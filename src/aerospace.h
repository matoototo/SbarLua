#include <sys/socket.h>
#include <sys/un.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <libproc.h>
#include <pwd.h>
#include <os/signpost.h>
#include <dispatch/dispatch.h>

struct aero_connection {
  int fd;
  CFSocketRef socket;
  CFRunLoopSourceRef source;
  char *input, *output;
  size_t input_size, output_size;
  bool ready, streaming;
};

struct aero_command {
  char *json;
  bool discord;
  struct aero_command *next;
};

static struct aero_connection aero_stream = { .fd = -1, .streaming = true };
static struct aero_connection aero_commands = { .fd = -1 };
static struct aero_command *aero_queue, *aero_tail;
static bool aero_command_running;
static int aero_callback_ref;
static CFRunLoopTimerRef aero_retry_timer;
static cJSON *aero_snapshot;
static char aero_workspace[256], aero_mru[3][256], aero_state_dir[1024];
static pid_t aero_chrome_pid;
static int aero_chrome_policy = -1;
static uint64_t aero_discord_windows;
static os_log_t aero_log;
static dispatch_queue_t aero_persistence_queue;

struct aero_mru_write {
  char path[1100], contents[772];
  os_log_t log;
};

static void aero_persist_mru(void *context) {
  struct aero_mru_write *write = context;
  os_signpost_id_t signpost = os_signpost_id_generate(write->log);
  os_signpost_interval_begin(write->log, signpost, "MRUPersist");
  FILE *file = fopen(write->path, "w");
  if (file) { fputs(write->contents, file); fclose(file); }
  os_signpost_interval_end(write->log, signpost, "MRUPersist");
  free(write);
}

static void aero_disconnect(struct aero_connection *connection);

static void aero_write(struct aero_connection *connection) {
  while (connection->output_size) {
    ssize_t count = send(connection->fd, connection->output, connection->output_size, 0);
    if (count < 0 && errno == EINTR) continue;
    if (count < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) break;
    if (count <= 0) { aero_disconnect(connection); return; }
    connection->output_size -= count;
    memmove(connection->output, connection->output + count, connection->output_size);
  }
  if (connection->output_size) CFSocketEnableCallBacks(connection->socket, kCFSocketWriteCallBack);
}

static void aero_send(struct aero_connection *connection, const void *bytes, size_t count) {
  if (connection->fd < 0) return;
  connection->output = realloc(connection->output, connection->output_size + count);
  memcpy(connection->output + connection->output_size, bytes, count);
  connection->output_size += count;
  aero_write(connection);
}

static void aero_send_json(struct aero_connection *connection, const char *json) {
  uint32_t count = (uint32_t)strlen(json);
  aero_send(connection, &count, sizeof(count));
  aero_send(connection, json, count);
}

static void aero_start_command(void) {
  if (!aero_commands.ready || aero_command_running || !aero_queue) return;
  aero_command_running = true;
  aero_send_json(&aero_commands, aero_queue->json);
}

static void aero_enqueue(cJSON *args, bool discord) {
  cJSON *request = cJSON_CreateObject();
  cJSON_AddItemToObject(request, "args", args);
  cJSON_AddStringToObject(request, "stdin", "");
  cJSON_AddNullToObject(request, "windowId");
  cJSON_AddNullToObject(request, "workspace");
  struct aero_command *command = calloc(1, sizeof(*command));
  command->json = cJSON_PrintUnformatted(request);
  command->discord = discord;
  cJSON_Delete(request);
  if (aero_tail) aero_tail->next = command;
  else aero_queue = command;
  aero_tail = command;
  aero_start_command();
}

static const char *aero_string(cJSON *object, const char *key) {
  return cJSON_GetObjectItemCaseSensitive(object, key)->valuestring;
}

static bool aero_hot(const char *workspace) {
  for (int i = 0; i < 3; i++) if (!strcmp(aero_mru[i], workspace)) return true;
  return false;
}

static void aero_remember_workspace(const char *workspace) {
  if (!strcmp(aero_mru[0], workspace)) return;
  int found = 2;
  for (int i = 1; i < 3; i++) if (!strcmp(aero_mru[i], workspace)) found = i;
  for (int i = found; i > 0; i--) memcpy(aero_mru[i], aero_mru[i - 1], sizeof(aero_mru[i]));
  snprintf(aero_mru[0], sizeof(aero_mru[0]), "%s", workspace);
  struct aero_mru_write *write = malloc(sizeof(*write));
  snprintf(write->path, sizeof(write->path), "%s/.mru", aero_state_dir);
  snprintf(write->contents, sizeof(write->contents), "%s %s %s\n", aero_mru[0], aero_mru[1], aero_mru[2]);
  write->log = aero_log;
  dispatch_async_f(aero_persistence_queue, write, aero_persist_mru);
}

static void aero_update_policy(cJSON *snapshot) {
  cJSON *windows = cJSON_GetObjectItemCaseSensitive(snapshot, "windows"), *window, *chrome = NULL;
  bool hot = false;
  cJSON_ArrayForEach(window, windows) {
    if (strcmp(aero_string(window, "app-bundle-id"), "com.google.Chrome")) continue;
    chrome = window;
    hot |= cJSON_IsTrue(cJSON_GetObjectItemCaseSensitive(window, "workspace-is-visible")) || aero_hot(aero_string(window, "workspace"));
  }
  if (!chrome) return;
  pid_t main_pid = cJSON_GetObjectItemCaseSensitive(chrome, "app-pid")->valueint;
  int policy = hot ? 0 : PRIO_DARWIN_BG;
  if (main_pid == aero_chrome_pid && policy == aero_chrome_policy) return;
  char prefix[PROC_PIDPATHINFO_MAXSIZE];
  snprintf(prefix, sizeof(prefix), "%s/Contents/", aero_string(chrome, "app-bundle-path"));
  size_t length = strlen(prefix);
  int capacity = proc_listallpids(NULL, 0) + 32;
  pid_t *pids = malloc(capacity * sizeof(*pids));
  int count = proc_listallpids(pids, capacity * sizeof(*pids));
  bool succeeded = true;
  for (int i = 0; i < count; i++) {
    char path[PROC_PIDPATHINFO_MAXSIZE];
    if (proc_pidpath(pids[i], path, sizeof(path)) <= 0 || strncmp(path, prefix, length)) continue;
    if (setpriority(PRIO_DARWIN_PROCESS, pids[i], policy) && errno != ESRCH) {
      fprintf(stderr, "AeroSpace Chrome priority: %s\n", strerror(errno));
      succeeded = false;
    }
  }
  free(pids);
  if (succeeded) {
    aero_chrome_pid = main_pid;
    aero_chrome_policy = policy;
  }
}

static void aero_query_discord(void) {
  for (struct aero_command *command = aero_queue; command; command = command->next) if (command->discord) return;
  const char *args[] = { "list-windows", "--monitor", "all", "--app-bundle-id", "com.hnc.Discord", "--format", "%{window-id} %{window-title} %{workspace} %{window-layout}", "--json" };
  aero_enqueue(cJSON_CreateStringArray(args, sizeof(args) / sizeof(*args)), true);
}

static void aero_follow_discord(cJSON *answer) {
  cJSON *windows = cJSON_Parse(aero_string(answer, "stdout")), *window;
  cJSON_ArrayForEach(window, windows) {
    if (strstr(aero_string(window, "window-title"), "Discord")) continue;
    if (!strcmp(aero_string(window, "workspace"), aero_workspace) && !strcmp(aero_string(window, "window-layout"), "floating")) continue;
    char command[512];
    int id = cJSON_GetObjectItemCaseSensitive(window, "window-id")->valueint;
    snprintf(command, sizeof(command), "layout --window-id %d floating; move-node-to-workspace --window-id %d %s", id, id, aero_workspace);
    const char *args[] = { "eval", command };
    aero_enqueue(cJSON_CreateStringArray(args, 2), false);
  }
  cJSON_Delete(windows);
}

static void aero_publish(cJSON *snapshot) {
  os_signpost_id_t signpost = os_signpost_id_generate(aero_log);
  os_signpost_interval_begin(aero_log, signpost, "StateToBar");
  const char *workspace = aero_string(snapshot, "workspace");
  bool changed = strcmp(aero_workspace, workspace);
  snprintf(aero_workspace, sizeof(aero_workspace), "%s", workspace);
  os_signpost_interval_begin(aero_log, signpost, "NativePolicy");
  os_signpost_interval_begin(aero_log, signpost, "MRUUpdate");
  aero_remember_workspace(workspace);
  os_signpost_interval_end(aero_log, signpost, "MRUUpdate");
  os_signpost_interval_begin(aero_log, signpost, "ChromePolicy");
  aero_update_policy(snapshot);
  os_signpost_interval_end(aero_log, signpost, "ChromePolicy");
  os_signpost_interval_end(aero_log, signpost, "NativePolicy");
  uint64_t discord = 0;
  cJSON *window;
  cJSON_ArrayForEach(window, cJSON_GetObjectItemCaseSensitive(snapshot, "windows")) {
    if (!strcmp(aero_string(window, "app-bundle-id"), "com.hnc.Discord")) {
      uint64_t id = cJSON_GetObjectItemCaseSensitive(window, "window-id")->valueint;
      discord += id * UINT64_C(11400714819323198485);
    }
  }
  if (discord && (changed || discord != aero_discord_windows)) aero_query_discord();
  aero_discord_windows = discord;
  cJSON_Delete(aero_snapshot);
  aero_snapshot = snapshot;
  os_signpost_interval_begin(aero_log, signpost, "LuaRender");
  lua_rawgeti(g_state, LUA_REGISTRYINDEX, aero_callback_ref);
  json_object_to_lua_table(g_state, snapshot);
  transaction_create(g_state);
  if (lua_pcall(g_state, 1, 0, 0)) {
    fprintf(stderr, "AeroSpace callback: %s\n", lua_tostring(g_state, -1));
    lua_pop(g_state, 1);
  }
  os_signpost_interval_end(aero_log, signpost, "LuaRender");
  os_signpost_interval_begin(aero_log, signpost, "BarCommit");
  transaction_commit_mode(g_state, false);
  os_signpost_interval_end(aero_log, signpost, "BarCommit");
  os_signpost_interval_end(aero_log, signpost, "StateToBar");
}

static void aero_connect(struct aero_connection *connection);

static void aero_retry(CFRunLoopTimerRef timer, void *info) {
  CFRelease(aero_retry_timer);
  aero_retry_timer = NULL;
  if (aero_stream.fd < 0) aero_connect(&aero_stream);
  if (aero_commands.fd < 0) aero_connect(&aero_commands);
}

static void aero_schedule_retry(void) {
  if (aero_retry_timer) return;
  aero_retry_timer = CFRunLoopTimerCreate(NULL, CFAbsoluteTimeGetCurrent() + 1, 0, 0, 0, aero_retry, NULL);
  CFRunLoopAddTimer(CFRunLoopGetMain(), aero_retry_timer, kCFRunLoopCommonModes);
}

static void aero_disconnect(struct aero_connection *connection) {
  if (connection->socket) {
    CFSocketInvalidate(connection->socket);
    CFRelease(connection->socket);
    CFRelease(connection->source);
  } else if (connection->fd >= 0) close(connection->fd);
  connection->fd = -1;
  connection->socket = NULL;
  connection->source = NULL;
  connection->ready = false;
  connection->input_size = connection->output_size = 0;
  if (!connection->streaming) aero_command_running = false;
  aero_schedule_retry();
}

static void aero_socket_callback(CFSocketRef socket, CFSocketCallBackType type, CFDataRef address, const void *data, void *info) {
  struct aero_connection *connection = info;
  if (type == kCFSocketWriteCallBack) { aero_write(connection); return; }
  char bytes[8192];
  ssize_t count;
  while ((count = recv(connection->fd, bytes, sizeof(bytes), 0)) > 0) {
    connection->input = realloc(connection->input, connection->input_size + count);
    memcpy(connection->input + connection->input_size, bytes, count);
    connection->input_size += count;
  }
  bool disconnected = !count || (errno != EAGAIN && errno != EWOULDBLOCK);
  if (!connection->ready && connection->input_size >= 4) {
    uint32_t version;
    memcpy(&version, connection->input, 4);
    if (version != 1) { fprintf(stderr, "AeroSpace socket protocol %u is unsupported\n", version); aero_disconnect(connection); return; }
    connection->input_size -= 4;
    memmove(connection->input, connection->input + 4, connection->input_size);
    connection->ready = true;
    if (connection->streaming) aero_send_json(connection, "{\"args\":[\"subscribe-state\"],\"stdin\":\"\",\"windowId\":null,\"workspace\":null}");
    else aero_start_command();
  }
  while (connection->ready && connection->input_size >= 4) {
    uint32_t length;
    memcpy(&length, connection->input, 4);
    if (connection->input_size < length + 4) break;
    cJSON *message = cJSON_ParseWithLength(connection->input + 4, length);
    connection->input_size -= length + 4;
    memmove(connection->input, connection->input + length + 4, connection->input_size);
    if (connection->streaming) {
      if (!cJSON_GetObjectItemCaseSensitive(message, "workspace")) {
        fprintf(stderr, "AeroSpace subscribe-state: %s\n", aero_string(message, "stderr"));
        cJSON_Delete(message);
        aero_disconnect(connection);
        return;
      }
      aero_publish(message);
    } else {
      struct aero_command *command = aero_queue;
      if (cJSON_GetObjectItemCaseSensitive(message, "exitCode")->valueint) fprintf(stderr, "AeroSpace command: %s\n", aero_string(message, "stderr"));
      else if (command->discord) aero_follow_discord(message);
      aero_queue = command->next;
      if (!aero_queue) aero_tail = NULL;
      free(command->json);
      free(command);
      cJSON_Delete(message);
      aero_command_running = false;
      aero_start_command();
    }
  }
  if (disconnected) aero_disconnect(connection);
}

static void aero_connect(struct aero_connection *connection) {
  struct sockaddr_un address = { .sun_family = AF_UNIX };
  snprintf(address.sun_path, sizeof(address.sun_path), "/tmp/bobko.aerospace-%s.sock", getpwuid(getuid())->pw_name);
  connection->fd = socket(AF_UNIX, SOCK_STREAM, 0);
  fcntl(connection->fd, F_SETFL, O_NONBLOCK);
  int no_sigpipe = 1;
  setsockopt(connection->fd, SOL_SOCKET, SO_NOSIGPIPE, &no_sigpipe, sizeof(no_sigpipe));
  if (connect(connection->fd, (struct sockaddr *)&address, sizeof(address)) && errno != EINPROGRESS) { aero_disconnect(connection); return; }
  CFSocketContext context = { 0, connection, NULL, NULL, NULL };
  connection->socket = CFSocketCreateWithNative(NULL, connection->fd, kCFSocketReadCallBack | kCFSocketWriteCallBack, aero_socket_callback, &context);
  CFSocketSetSocketFlags(connection->socket, kCFSocketCloseOnInvalidate | kCFSocketAutomaticallyReenableReadCallBack);
  connection->source = CFSocketCreateRunLoopSource(NULL, connection->socket, 0);
  CFRunLoopAddSource(CFRunLoopGetMain(), connection->source, kCFRunLoopCommonModes);
  uint32_t version = 1;
  aero_send(connection, &version, sizeof(version));
}

static int aerospace(lua_State *state) {
  luaL_checktype(state, 1, LUA_TFUNCTION);
  g_state = state;
  if (aero_callback_ref) luaL_unref(state, LUA_REGISTRYINDEX, aero_callback_ref);
  lua_pushvalue(state, 1);
  aero_callback_ref = luaL_ref(state, LUA_REGISTRYINDEX);
  if (!aero_log) aero_log = os_log_create("com.mato.aerospace-glue", OS_LOG_CATEGORY_POINTS_OF_INTEREST);
  if (!aero_persistence_queue) aero_persistence_queue = dispatch_queue_create("com.mato.aerospace-mru", dispatch_queue_attr_make_with_qos_class(DISPATCH_QUEUE_SERIAL, QOS_CLASS_UTILITY, 0));
  snprintf(aero_state_dir, sizeof(aero_state_dir), "%s/aero-demote", getenv("TMPDIR") ?: "/tmp");
  mkdir(aero_state_dir, 0700);
  char path[1100];
  snprintf(path, sizeof(path), "%s/.mru", aero_state_dir);
  FILE *file = fopen(path, "r");
  if (file) { fscanf(file, "%255s %255s %255s", aero_mru[0], aero_mru[1], aero_mru[2]); fclose(file); }
  if (aero_stream.fd < 0) aero_connect(&aero_stream);
  if (aero_commands.fd < 0) aero_connect(&aero_commands);
  return 0;
}

static int aerospace_command(lua_State *state) {
  luaL_checktype(state, 1, LUA_TTABLE);
  cJSON *args = cJSON_CreateArray();
  for (int i = 1; i <= lua_rawlen(state, 1); i++) {
    lua_rawgeti(state, 1, i);
    cJSON_AddItemToArray(args, cJSON_CreateString(luaL_checkstring(state, -1)));
    lua_pop(state, 1);
  }
  aero_enqueue(args, false);
  return 0;
}
