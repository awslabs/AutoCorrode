# ic2 — fast headless theory checking

Building a theory from the command line normally pays the full session/heap
load on every invocation. `isabelle ic2` keeps one warm session running and
checks files against it, so repeated checks are fast and report progress live.

A single command-line tool. Server lifecycle lives under `ic2 server`; the rest
act on a running server:

  * **`ic2 server start`** — start the background server for a session
    (`server stop` / `server status` to shut down / inspect; `server attach`
    to follow a backgrounded server's console log).
  * **`ic2 check FILE...`** — check `.thy` files against a running server, with
    a live progress bar per theory (`check status|attach|cancel` to inspect /
    stream / cancel the in-flight check; `--line N` for a partial check).
  * **`ic2 query SUBTOOL ...`** — read-only diagnostics over the warm session.
  * **`ic2 load-files FILE...`** — parse `.thy` files into the session graph
    *without* evaluating them, so structural queries work at near-zero cost.
  * **`ic2 repl-create FILE:LINE NAME`** — start an interactive I/R REPL at a
    source location.

Servers are addressed by name, so several can run side by side and the client
finds them with no host/port/token to configure. `isabelle ic2_test` is the
accompanying test runner.

## Quick start

```
# 1. Register the component (once):
isabelle components -u /path/to/AutoCorrode/ic2

# 2. Start a background server (returns when it is ready):
isabelle ic2 server start --daemon -l HOL
# or for a session tree like AutoCorrode:
isabelle ic2 server start --daemon -l AutoCorrode -d AutoCorrode
# (drop --daemon to run in the foreground until Ctrl-C.)

# 3. Check a file:
isabelle ic2 check /abs/path/to/Foo.thy
# → live progress bars; exit 0 on success, 1 on first error.

# 4. Inspect / stop:
isabelle ic2 server status
isabelle ic2 server stop
```

## `ic2 server start`

Starts the server for a session (e.g. `HOL`, or a session tree). It builds the
heap if needed, then serves checks until stopped. Foreground by default;
`--daemon` runs it in the background and returns once it is ready.

```
--daemon     run in the background and return once the server is ready
             (default: foreground until Ctrl-C)
--no-iq      do not bring up AutoCorrode's I/R interactive REPL
             (default: bring it up and spawn the repl.py bridge)
--mcp        also stand up the MCP server in front of the I/R bridge
             (default: off)
-L FILE      logging on FILE (in addition to stderr; the --daemon default is
             $ISABELLE_HOME_USER/ic2/<name>.log)
-d DIR       include session directory (repeatable)
-i NAME      include session for theory namespace (repeatable)
-l NAME      session name (default ISABELLE_LOGIC)
-n NAME      server name (default: "default") — lets several servers coexist
-o OPTION    override Isabelle option (NAME=VAL or NAME) (repeatable)
-N           no build: assume the heap is up-to-date (fails fast if missing)
-v           verbose: log connection lifecycle on stderr (repeat -vv for more)
```

The flags mirror `isabelle jedit`. `--daemon` exits 0 once the server is
serving, 1 if it dies during startup, or 0 with a "still starting" note if a
cold heap build outlasts the readiness wait — then follow the log or re-run
`ic2 server status`. With `--daemon` and no `-L`, output goes to
`$ISABELLE_HOME_USER/ic2/<name>.log`.

**I/R + MCP.** Unless `--no-iq` is given, the server brings up AutoCorrode's
interactive REPL against the same warm session it uses for checks, so an agent
or operator can drive Isar proof development without a separate Isabelle/jEdit +
I/Q instance. The I/R bring-up is delegated to the session-generic `IRLauncher`
(shared from `iq/src/IRClient.scala`) — the same code path Isabelle/jEdit's I/Q
plugin uses — which loads the I/R ML into the prover, opens a token-authenticated
ML_Repl listener inside it, spawns `ir/repl.py --daemon --expect-ml` as the
client-facing bridge, and connects.

In front of the bridge, the server can also stand up an **MCP server** (the generic
`McpServer` shared from `iq/src/McpServer.scala`) on loopback **port 8765** (the
same base I/Q uses; it scans upward to the first free port, so a second instance
takes 8766, …). This is **opt-in**: the MCP server comes up **only with `--mcp`**
and is **off by default**. The repl.py bridge, `repl.py cli`, and `ic2 repl-create`
all work without it — only the MCP layer (the `repl_*` MCP tools plus the
`mcp_port`/`mcp_token` endpoint) is gated. When enabled with `--mcp`, it registers
these tool families:

  * the I/R `repl_*` tools via the shared `IRTools` provider (interactive proof
    exploration — the same tools Isabelle/jEdit's I/Q plugin exposes);
  * the **session-generic diagnostic tools** via the shared `SessionClient` /
    `SessionTools` (`iq/src/`): `list_files`, `get_processing_status`,
    `get_document_info`, `get_diagnostics` (file or selection scope),
    `get_sorry_positions`, `get_entities`, `get_proof_blocks`, `get_command_info`,
    `get_state_at` (`get_context_info` is a deprecated alias). These are read-only
    analyses over the session's document
    snapshot and work identically here and in I/Q (see "Session diagnostic tools");
  * a **`check`** tool — type-check `.thy` files against the warm session (the
    MCP analogue of `isabelle ic2 check`). Submits the check and blocks on it;
    like the wire `check` it **stops on the first failed theory** and — when the
    client supplied a `progressToken` — emits `notifications/progress` (N/M
    theories processed, throttled to ~1s). Returns `{ok, theories, [reason]}`,
    aborting with reason `"timeout"` past `timeout_secs` (default 600). Session-
    mutating, so ic2-specific (not in the generic `SessionClient`);
  * **`check_async` / `check_status` / `check_cancel`** — the non-blocking form.
    `check_async` submits the check and returns immediately (it keeps running in
    the background); the no-argument `check_status` reports the current/last
    check's state (running/ok/failed) + per-theory status; the no-argument
    `check_cancel` aborts the in-flight one. **At most one check runs at a time**
    server-wide: `check`/`check_async` are refused while one is in flight (cancel
    it and resubmit the merged set). Same single check as the wire `check
    --detach` family;
  * a no-argument `status` tool (a liveness/diagnostic probe for the MCP server).

**Progress notifications.** The shared `McpServer` supports MCP progress: a tool
handler receives a sink (`McpProgress.Sink = JSON.Object.T => Unit`); whatever
dict it passes is forwarded verbatim as the params of a `notifications/progress`
message, with the client's `progressToken` injected. The sink is a no-op unless
the request carried `_meta.progressToken`, so non-progress tools and clients are
unaffected. Notifications are written on the same (synchronized) connection
writer as the final response, so they can't interleave with it. `check` is the
first consumer.

`ic2 server status` reports the available endpoints: the **repl.py** port/token
(raw I/R wire protocol) and, when the MCP server is enabled (only with `--mcp`),
the **MCP** port/token (point an MCP client there; authenticate with the token,
then call the tools above).

The MCP auth token is taken from `IQ_AUTH_TOKEN` (the same variable I/Q uses) if
set, otherwise generated and reported by `ic2 server status`. As with I/Q, the client
must call the `authenticate` tool with this token before any other tool
(`initialize` / `tools/list` / `ping` are always available).

The AutoCorrode tree is found at `$AUTOCORRODE_BASE` if set, otherwise the tree
this component lives inside (`ic2` sits at `<AutoCorrode>/ic2`, so the I/R
sources are at `<AutoCorrode>/ir`). Bring-up is best-effort and all-or-nothing:
if the `ir/` sources are missing, `python3`/`repl.py` is unavailable, or the
prover is unreachable, I/R+MCP are disabled but the checking server still runs
(a failure of just the MCP layer still leaves the repl.py bridge usable). repl.py
is spawned with `--no-heap-db`, so recorded-segment forking (`Ir.source`) is off
— that needs a heap built with `record_theories=true`, which is outside `ic2`'s
control. The repl.py child and the MCP server are terminated when the server
stops.

## `ic2 check`

```
ic2 check [-n NAME] [-P] [--detach] [--line N] [--long-running SECS] FILE...
  -n NAME             server to use (default: the sole running server)
  -P                  plain mode (disable the ANSI progress bars)
  --detach            submit the check and return immediately, without waiting
  --line N            partial check: only the prefix up to the command ending
                      on or before source line N (requires exactly one FILE)
  --long-running SECS list commands running longer than SECS under their bar
                      (default 5; 0 disables)
```

Checks the given `.thy` files (paths must be absolute and exist) against the
named server, showing one live progress bar per theory and stopping at the
first error, which is printed with its file and line. `-P` falls back to
plain-text lines; checking a non-TTY does the same automatically. Under each
bar, `--long-running SECS` lists commands still running past a threshold
(keyword / line / elapsed), so a stall is visible as a specific slow command
rather than just a paused bar.

`--line N` runs a **partial check** of a single FILE — only the prefix up to
the command ending on or before source line N is evaluated; commands after it
are left UNPROCESSED and the theory stays re-checkable. Handy for iterative
development: check up to the line you're editing without paying for the rest.

Exit codes — designed to drop into scripts and editor integrations:

  * **0** — all checks passed.
  * **1** — a check failed (an error was found, or the run was stopped).
  * **2** — bad usage (e.g. no FILE given).
  * **3** — the server could not be reached, or the connection dropped before
    the check finished.

On Ctrl-C the check is cancelled and the server stays up (only `ic2 server stop`
terminates it); the process exits with the usual interrupted code (130).

### Detached checks (non-blocking)

A check is a server-side unit of work; the foreground form above is just "submit
it, stream it, and cancel it if I disconnect." `--detach` submits and returns
immediately — the check keeps running on the server after the command exits (it
does **not** die when the submitting connection closes, unlike a foreground
check). Track it with:

```
ic2 check --detach -n NAME FILE...   # prints "submitted (...)"
ic2 check status -n NAME             # state (running/ok/failed), elapsed, per-theory status
ic2 check attach -n NAME             # stream the check's progress to completion (like foreground)
ic2 check cancel -n NAME             # abort the in-flight check (reason "cancelled")
```

**At most one check runs at a time, server-wide** — `use_theories` is not safe
to run concurrently on the one warm session, so a second `check` (foreground or
detached, wire or MCP) is **refused** while one is in flight. To check a
different or larger set, cancel the running check and resubmit the merged set of
theories. There are no job ids (there's only ever one check) and no subcommand
arguments beyond `-n`. `ic2 server status` shows the server `busy` while it runs; the
last check's status stays queryable via `check status` until the next submit.

## `ic2 query`

Read-only diagnostic queries over the warm session — the CLI form of the MCP
diagnostic tools. One-shot: each invocation opens a connection, asks, prints, and
exits. Most take a theory FILE (a loaded/checked session node; partial paths are
completed against loaded nodes). Output is human-readable; `--json` emits the raw
tool JSON (the same object the MCP tool returns), for piping to `jq`.

```
ic2 query SUBTOOL [FILE] [OPTIONS]
  -n NAME          server name (default: the sole running server)
  --json           raw tool JSON instead of formatted text
```

| SUBTOOL | FILE | options | reports |
|---|---|---|---|
| `list-files` | — | `--theory` / `--non-theory` | loaded nodes + per-node status |
| `processing-status` | ✓ | | PIDE processing counts for a theory |
| `document-info` | ✓ | | whole-theory command/error/warning totals |
| `diagnostics` | ✓ | `--severity error\|warning`, `--scope file\|selection`, `--offset N` / `--line N` / `--pattern P` | errors or warnings |
| `sorry` | ✓ | | sorry/oops positions + enclosing proof |
| `entities` | ✓ | `--max N` | declared entities (lemma/definition/fun/…) |
| `proof-blocks` | ✓ | `--min-chars N` | proof blocks with text + line ranges |
| `spans` | ✓ | | flat list of parsed command spans |
| `command-info` | ✓ | `--offset N` / `--line N` / `--pattern P` | command metadata/status/result at a selection |
| `state-at` | ✓ | `--offset N` / `--line N` / `--pattern P` | proof state (goal + context) at a selection |

The three selectors (`--offset`, `--line`, `--pattern`) point at a command;
`--line N` resolves to the command ending on or before that line (walking back
over blank lines, as jEdit does). `context-info` is kept as a deprecated alias
for `state-at`.

```
$ isabelle ic2 query entities Diagnostics.thy
6 entit(ies):
  line 13    definition   answer
  line 16    datatype     color
  line 18    fun          isRed
  line 23    lemma        structured
  line 29    lemma        applied
  line 35    lemma        incomplete

$ isabelle ic2 query diagnostics Trivial_Fail.thy
error (file): 1 found:
  /abs/path/Trivial_Fail.thy:6: Failed to finish proof
```

A FILE must be a loaded session node — check it first (`ic2 check` or
`ic2 load-files`) or it is reported as not loaded. `query` and the MCP
diagnostic tools route through the same `SessionTools.dispatch`, so the two
surfaces stay in lockstep. Exit codes: 0 on success, 2 on a usage error
(unknown subtool, missing FILE), 3 if the server is unreachable.

## `ic2 load-files`

```
ic2 load-files [-n NAME] [--print [--include-ignored]] FILE...
```

Parses `.thy` files into the running server's document graph **without
evaluating any commands**: the theory is split into its command spans (IDs,
offsets, line positions) but no ML runs and no proof state is produced. After
loading, the structural `query` subtools (`list-files`, `entities`, `sorry`,
`spans`, `proof-blocks`, `command-info`, `state-at` — the latter two with the
proof/status fields empty) work on the loaded nodes at near-zero cost, and a
later `ic2 check` on the same files pays only the evaluation cost, not the
parse cost. `--print` additionally dumps each loaded node's parsed spans (the
same output as `ic2 query spans FILE`); `--include-ignored` adds the
inter-command whitespace/comment spans too.

## `ic2 repl-create`

```
ic2 repl-create FILE:LINE NAME [-n SERVER]
```

**When to use this:** to start an *interactive* I/R proof REPL at a specific
`.thy` position — e.g. to explore or develop a proof step-by-step from the goal
state at that line. This is the only way to create a REPL anchored to a source
location: the bare `repl.py cli` **cannot** do it (mapping a source line to a
prover command id needs the live document, which only the ic2 daemon has — it
holds both the `Headless.Session` and the connected I/R client). For one-off
read-only queries you want `ic2 query` instead; for a quick stateless I/R call,
`repl.py cli raw '…'`.

`repl-create` resolves `LINE` (1-based) of theory `FILE` to the command spanning
it, creates the REPL named `NAME` (`Ir.init_from_document`), and prints **(a)**
the REPL's initial state and **(b)** the exact `repl.py cli` commands to drive
it — so no further lookup is needed:

```
$ isabelle ic2 repl-create AutoCorrode/Misc/Word.thy:142 w
REPL 'w' from document Misc.Word cmd 37
<proof state at that command...>

Drive this REPL with `repl.py cli` (one-shot client; `cli help` lists all verbs):
  step:       IR_AUTH_TOKEN=… python3 /abs/AutoCorrode/ir/repl.py cli --port 59498 step w 'apply simp'
  show state: IR_AUTH_TOKEN=… python3 /abs/AutoCorrode/ir/repl.py cli --port 59498 state w -1
  full text:  IR_AUTH_TOKEN=… python3 /abs/AutoCorrode/ir/repl.py cli --port 59498 text w
  any ML:     IR_AUTH_TOKEN=… python3 /abs/AutoCorrode/ir/repl.py cli --port 59498 raw  -- 'Ir.show "w"'
```

**How to drive the REPL afterwards:** run the printed `repl.py cli` lines (or any
verb from `repl.py cli help`) against the same server's bridge — each is a
one-shot call: `step` adds an Isar command, `state w -1` shows the latest proof
state, `text w` prints the accumulated script, `raw` sends arbitrary ML. The
`--port` and `IR_AUTH_TOKEN` shown are this server's; they also appear in
`ic2 server status` under `I/R cli:`.

`FILE` must be a loaded/checked node (run `ic2 check` first). Exit codes: 0 on
success, 2 on a usage error (no `FILE:LINE NAME`, non-integer LINE), 3 if the
server is unreachable, I/R isn't up, or the file isn't loaded.

## `ic2 server status`

```
ic2 server status [-n NAME] [--full]
```

With `-n NAME`, prints a summary line for that server — session, pid, uptime,
idle/busy, checks in flight, connection count — followed by the options it was
started with and the I/R endpoints, or `no I/R`; exits 3 if the server is
unreachable. Without `-n`, surveys every server that has a socket — summary +
I/R lines each, stale sockets flagged — and exits 0. During the initial heap
build the summary shows a lifecycle phase (building → loading → ready) instead
of idle/busy.

`--full` additionally lists every active document node (per-node processing %,
error/warning counts; heap-resident library nodes are omitted) followed by the
errors themselves. It targets the sole running server when `-n` is omitted, and
skips the node list with a note if the server isn't ready yet.

The I/R lines show the **repl.py** bridge (raw I/R wire protocol) and, when up,
the **MCP** server in front of it. The in-prover ML_Repl is deliberately *not*
advertised, so nothing can connect around it to the prover.

```
$ isabelle ic2 server status -n default
default: session=HOL pid=12345 up=42s idle conns=1
    started with: logic=HOL
    I/R repl.py: port=59498 token=GSJpumMw…  (raw I/R protocol)
    I/R MCP:     port=8765 token=a1b2c3d4…  (connect MCP repl_* here)
    I/R cli:     IR_AUTH_TOKEN=GSJpumMw… python3 /abs/AutoCorrode/ir/repl.py cli raw --port 59498 -- 'Ir.theories ()'

$ isabelle ic2 server status
default: session=HOL pid=12345 up=42s idle conns=1
    I/R repl.py: port=59498 token=GSJpumMw…  (raw I/R protocol)
    I/R MCP:     port=8765 token=a1b2c3d4…  (connect MCP repl_* here)
    I/R cli:     IR_AUTH_TOKEN=GSJpumMw… python3 /abs/AutoCorrode/ir/repl.py cli raw --port 59498 -- 'Ir.theories ()'
plain:   session=HOL pid=12346 up=5s idle conns=1
    no I/R
```

Three ways to drive I/R, all against the same warm session: point an MCP client
at the MCP port/token (authenticate, then call `repl_*` or the `status` probe); a
raw I/R client (IRClient) at the repl.py port/token; or — for a quick shell
one-liner — the **`I/R cli`** command, which runs `repl.py cli`, a one-shot client
that sends a single command and prints the reply. `repl.py cli help` lists its
typed verbs (`init`, `step`, `state`, …); `raw` sends ML verbatim. It reads the
token from `--token` or `$IR_AUTH_TOKEN`. Because each call pays no JVM/session
startup (it just hits the running server), it is far faster than a fresh
`isabelle` invocation.

## `ic2 server attach`

```
ic2 server attach [-n NAME] [-c N] [--from-start] [-L FILE]
  -n NAME       server to attach to (default: the sole running server)
  -c N          print the last N lines of the existing log for context before
                streaming (default 40; -c 0 shows only new output)
  --from-start  replay the whole current log first, then stream
  -L FILE       the log path, if the server was started with a matching -L
```

Follows a backgrounded server's console log — the same output you would have
seen had you run `server start` in the foreground, **including the heap-build
progress**. Handy right after `server start --daemon` to watch a cold heap build
to completion, or to tail a long-running check. Streaming continues until the
server shuts down (its socket disappears) or you press Ctrl-C — detaching leaves
the server running.

```
# start cold in the background, then watch it build:
isabelle ic2 server start --daemon -l HOL
isabelle ic2 server attach              # tails $ISABELLE_HOME_USER/ic2/default.log
```

It reads `$ISABELLE_HOME_USER/ic2/<name>.log`; if the server was started with
`-L FILE`, pass the same `-L FILE` here. Exits 3 if no such server (neither
socket nor log) exists.

## `ic2 server stop`

```
ic2 server stop [-n NAME]
```

Shuts the named server down. Any check in flight on another connection winds
down as the server exits.

## Tests

```
isabelle ic2_test unit               # unit tests (no session)
isabelle ic2_test e2e                # end-to-end tests (uses HOL)
isabelle ic2_test all                # default — all tests
isabelle ic2_test -v all             # show all events
isabelle ic2_test -t check_ok all    # only one test
```

E2E tests start their own `ic2 server start -l HOL`, run every scenario against it
(including `--daemon` launch and `ic2 server stop`), and shut it down. The first run
builds the HOL heap (slow); subsequent runs reuse it. Fixtures live in
`test/fixtures/`. See `run_unit` / `run_e2e` in `src/test_tool.scala` for the
catalogue.

---

## How it works

A server is one long-running `Headless.Session` (built like `isabelle jedit`'s
would be: `Build.build` with `build_heap = true`). `ic2 check` drives it via
`use_theories` and streams progress back; the warm session is what makes
repeated checks fast.

**Discovery and access control.** A server listens on a Unix-domain socket at
`$ISABELLE_HOME_USER/ic2/<name>.sock` (`--daemon` also writes `<name>.log`);
the client derives the same path from the name. The JVM creates the socket file
world-traversable, so access control is the *parent directory*: `ic2 server start`
creates `$ISABELLE_HOME_USER/ic2` mode `0700` (owner-only). There is no auth
token — the filesystem is the boundary, the same model as the ssh-agent / tmux
socket directories. A crashed server can leave a stale socket node behind; on
startup `ic2 server start` probes it, reclaims it if nothing is listening, and refuses
to start if a live server already holds the name.

**File resolution.** A file inside a session given via `-d` is checked under
that session's qualifier (e.g. `AutoCorrode.Misc.Foo`); any other file is
checked as `Draft.<basename>`.

**I/R bring-up.** At startup (unless `--no-iq`) the daemon hands its headless
`Headless.Session` to the session-generic `IRLauncher` (shared from
`iq/src/IRClient.scala`) — the very code Isabelle/jEdit's I/Q plugin drives with
its live PIDE session. IRLauncher probes `IR_Repl.status`; if the I/R ML isn't
loaded it loads it ad-hoc into an in-memory `ir` node (via `Session.update`) and
waits for it to consolidate; it then sends `protocol_command("IR_Repl.start")`,
captures the ML_Repl's port/token from the asynchronous `IR_Repl.port` reply,
spawns `ir/repl.py --daemon --expect-ml --poly-ml-port <port> --no-heap-db` (with
`IR_REPL_AUTH_TOKEN=<token>`), scrapes the bridge's own port/token from its
stdout, and connects a client. **Only when `--mcp` is given**, the daemon then
stands up a generic `McpServer` (shared from `iq/src/McpServer.scala`) on loopback
port 8765 (scanning upward to the first free port; token from `IQ_AUTH_TOKEN` or
freshly generated) and registers the I/R `repl_*` tools — via the shared `IRTools` provider
over an `Ic2IRConnection` that wraps the connected client + the session — plus a
no-arg `status` probe tool. Because bring-up only succeeds once repl.py is
reachable, the `status` op advertises *only* the repl.py bridge
(`repl_port`/`repl_token`) and, when the MCP server is enabled, the MCP endpoint
(`mcp_port`/`mcp_token`), never
the in-prover ML_Repl, so clients can't connect around it to the prover. The
`IRTools` source-location resolver runs headlessly: it completes a file argument
against the session's loaded theory nodes and reads its text from disk (no jEdit
buffers). The repl.py child and the MCP server are held by the daemon and torn
down (before `session.stop()`) on shutdown. The whole sequence is best-effort:
any failure disables I/R+MCP but leaves the checking server running.

**Session diagnostic tools.** Alongside `repl_*`, the MCP server exposes a family
of read-only diagnostic/introspection tools (`SessionClient` over `SessionTools`,
shared from `iq/src/`). They are *session-generic*: each reads only the document
snapshot (`Document.Snapshot` / `Document_Status` / command markup via `Rendering`
and `Protocol` — base PIDE, no jEdit), so the identical code serves ic2's headless
session and Isabelle/jEdit's live PIDE session. Two resolvers front them:
`resolveNode` (a partial path → a loaded node, by unique extension-insensitive
suffix match over `version.nodes`, with an absolute-path fallback) and
`resolveCommand` (path + offset|pattern → the command at that point). The file
tools (`list_files`, `get_processing_status`, `get_document_info`,
`get_diagnostics` file scope, `get_sorry_positions`, `get_entities`,
`get_proof_blocks`) take a `path`; the command tools (`get_command_info`,
`get_state_at`/`get_context_info`, `get_diagnostics` selection scope) take
`path` + `offset` or `pattern`.

These differ from I/Q **only** because of the editor's buffer/file-model layer,
which a headless session lacks:

  * *Candidate set.* I/Q completes paths against jEdit's open/tracked buffers
    (`Document_Model`); SessionTools completes against the session's loaded nodes
    (`version.nodes`). So a file must be loaded/checked (or an import) to resolve
    here — there is no "open but unprocessed" buffer, and conversely loaded-but-
    never-opened imports (e.g. `Main`) are visible that an editor view might omit.
  * *Text source.* I/Q reads the live, possibly-unsaved buffer; SessionTools
    reconstructs node text from the snapshot's command sources, so text offsets and
    the commands they index can never drift.

`get_command_info` reports a command's *output* (errors/warnings/writeln);
`get_state_at` (a.k.a. `context-info` / the `state-at` CLI subtool) reports the
*proof goal*. These are two different message streams and are read two different
ways. For the goal text to exist headlessly at all, the daemon turns on
**`show_states`** by default (override with `-o show_states=false`). Two prover
mechanisms can emit a proof state, but only `show_states` works here: the usual
`print_state` (gated by `editor_output_state`) runs as a *print function*, which
fires only for **visible** commands — and a `Headless.Session` hardcodes an empty
perspective, so nothing is ever visible and the goal text was always empty
despite `editor_output_state=true`. `show_states` instead emits the state
directly during the command transition, independent of the perspective, so it
fires for every evaluated command. (`editor_output_state=true` is still set too,
for parity with jEdit/VSCode.)

The goal text is then read from `snapshot.command_results(command)`, filtered to
the `STATE` messages (`Protocol.is_state`) — mirroring the reference
`Editor.output`. A proof state carries **no source position**, so the range-based
`Rendering.text_messages` walk (what the *output* tools, `get_command_info`
included, use) structurally cannot surface it — reading the goal that way left
`has_goal` false everywhere, which is the bug this fixes. `command_results` is
robust to snapshot/version identity (it falls back to the command's own state),
so it works even when the queried `Command` isn't from the current version. In a
fully consolidated session the proof state is attached to the command that
emitted it (e.g. a block's closing `qed`), not to every interior step.

Overlay-driven operations (I/Q's `get_definitions`, `explore` — which *run* the
`isar_explore` print function in the prover) are deliberately **not** part of this
generic layer; interactive execution lives on the I/R `repl_*` side.

**The check, cancellation, and first-error stop.** A check is a server-side unit
of work (`Check.Job`) created only by the single non-blocking `submit` — and
there is **at most one at a time**, server-wide: `use_theories` is not safe to
run concurrently on the one warm session (the calls share a single document
state + version history), so `submit` refuses while a check is in flight. The
caller cancels the running check and resubmits the merged set of theories.
Because checks never overlap there is no registry, no job ids, just the current
job in `Check.slot`. Everything else is a caller policy on top of `submit`:

  * A **foreground** check (`ic2 check`, MCP `check`) submits, streams its
    events, and waits — and, because it has a caller to answer to, cancels the
    check if that caller's own connection drops (the server detects EOF). The
    wait runs on a relay, so the connection thread stays free to notice the
    disconnect; Ctrl-C closes the connection, which is the same path.
  * A **detached** check (`ic2 check --detach`, MCP `check_async`) submits and
    returns immediately; nobody waits, so it survives the submitting connection
    and is cancelled only by an explicit `check_cancel` (`reason:"cancelled"`) or
    a timeout (MCP, `reason:"timeout"`).

A foreground caller's disconnect-cancel and a detached check's survival are thus
the *same* check seen under two caller policies. When any theory fails, the
progress driver emits one error event (file/line/message) and stops the run
(`progress.stop()`, which `use_theories` polls). A real error never surfaces as
a bare `interrupted`: if the run saw a failed node, the outcome is classified as
the error even when the cancel and the result race on the last tick.

`progress.stop()` alone only releases the Scala waiter — the ML kernel keeps
running an in-flight tactic to completion. So `Job.cancel` also fires
`session.cancel_exec` on every running exec in the job's theories (the only
primitive that actually interrupts a running tactic), with a short background
pulse to catch continuation execs a `by` forks after its tactic. A hard
`cancel_exec` poisons the cancelled command's memoized result, which would make
a later `use_theories` treat it as up-to-date and never re-run it (hanging the
re-check); `resetPoisonedTails` (`SessionTools.resetNodeTailFrom`) replays each
cancelled command's tail over itself so the parser re-splits it into fresh ids,
leaving the theory re-checkable. This is what makes both Ctrl-C on a slow proof
and `check --line N` (a partial check that cancels once the target command
finishes) leave a clean, re-checkable session.

Which commands are "running right now" — surfaced as the `long_running` array
and used to pick cancel targets — comes from `Timing_Tracker`, which counts the
raw `command_timing` stream per exec id rather than the built-in liveness
signals, which over-count forked proofs (every `apply`/`by` in a headless check
forks, so they read as running the moment their eval is dispatched).

**Wire protocol.** Newline-delimited JSON, one value per line (UTF-8). Clients
must ignore unknown keys and event types so the protocol can grow. The job ops
take no arguments beyond the implicit single check.

Client → server:

```
{"op":"check",        "files":["/abs/A.thy", ...]}          # foreground: stream + wait
{"op":"check",        "files":[...], "line":42}             # partial check up to line 42
{"op":"check",        "files":[...], "detach":true}         # detached: ack, keep running
{"op":"check_status"}                                       # one-shot state reply
{"op":"check_attach"}                                       # stream the in-flight check to completion
{"op":"check_cancel"}                                       # abort the in-flight check
{"op":"load-files",   "files":[...]}                        # parse into the graph, no eval
{"op":"query", "tool":"get_entities", "path":"A.thy", ...}  # one-shot diagnostic query
{"op":"repl",  "file":"A.thy", "line":42, "name":"r"}       # create an I/R REPL at a source line
{"op":"status"}
{"op":"shutdown"}
```

Server → client:

```
{"event":"ready",   "session":"AutoCorrode","pid":12345}
{"event":"status",  "session":"AutoCorrode","state":"ready","pid":12345,"uptime_s":42,
                    "busy":false,"checks_in_flight":0,"connections":1,
                    "options":{"logic":"AutoCorrode","dirs":["AutoCorrode"],
                               "include_sessions":[],"options":[],
                               "no_build":false,"load_iq":true},
                    "build":{...},           # only while state != "ready" (heap-build readout)
                    "ir":{"repl_port":59498,"repl_token":"…",
                          "mcp_port":8765,"mcp_token":"…",
                          "repl_cli":"…python3 …/repl.py cli raw --port 59498 -- '…'"}}
{"event":"started", "theories":["A","B",...]}
{"event":"progress","nodes":[ {"theory":"A","percentage":42,
                               "running":3,"unprocessed":7,
                               "finished":12,"warned":0,"failed":0,
                               "consolidated":false,
                               "long_running":[{"keyword":"by","line":30,"elapsed_s":7.2}]}, ... ]}
{"event":"error",   "theory":"A","file":"...","line":42,"message":"..."}
{"event":"finished","ok":true}
{"event":"finished","ok":false,"reason":"first-error stop|interrupted|cancelled|disconnect|timeout|errors|invalid request|exception:..."}
{"event":"submitted",   "state":"running","theories":[...],...}  # detached ack
{"event":"check_status","state":"running|ok|failed|idle","ok":...,"elapsed_ms":...,"nodes":[...]}
{"event":"check_cancel","cancelled":true}
{"event":"load-files",  "loaded":["A","B",...],"count":2}
{"event":"query",       "tool":"get_entities","result":{ ...tool JSON... }}
{"event":"repl",        "name":"r","result":"<REPL reply>"}
{"event":"server_error","message":"..."}
{"event":"shutting_down"}
```

`ready` is sent once on connect; `status` answers a `status` op — its `state`
is the lifecycle phase (`building`/`loading`/`starting_session`/`starting_ir`
while coming up, `ready` once serving, `failed` on bring-up error), with a
`build` sub-object carrying the heap-build readout until ready, and an `ir`
object present only when I/R was brought up (not `--no-iq` and the bridge came
up). `progress` events come at most every 200 ms; each node's optional
`long_running` array lists commands running past the client's threshold. A foreground
`check` (and `check_attach`) ends with exactly one `finished` event — including
invalid requests (`reason:"invalid request"`, preceded by a `server_error`), and
a refused concurrent check (`server_error` "already in flight"); a detached
`check` instead returns one `submitted` ack. `check_status` and `check_cancel`
are one-shot replies (no stream); `check_status` reports `state:"idle"` when no
check has run.

## Files

```
etc/build.props          — component manifest
etc/settings             — sets $ISABELLE_IC2_HOME
src/ic2.scala            — the `isabelle ic2` front door (subcommand dispatch)
src/daemon.scala         — `ic2 server start`: daemon, --daemon launch, status op
src/iq.scala             — I/R + MCP bring-up: IRLauncher, McpServer + IRTools +
                           SessionClient, Ic2IRConnection, the `status` + check
                           MCP tools, and the `Check` model (single-slot Job +
                           Job_Progress, Timing_Tracker, cancel_exec/reset +
                           partial `--line` worker) shared by the wire and MCP checks
src/client.scala         — `ic2 check` / `query` / `load-files` / `server
                           status` / `stop` / `repl-create` + Plain_UI + ANSI_UI
src/endpoint.scala       — socket-path discovery + the 0700 directory
src/json_io.scala        — newline-delimited JSON over a socket channel
src/test_tool.scala      — `isabelle ic2_test` runner
src/tools.scala          — Isabelle_Scala_Tools registration
test/fixtures/*.thy      — canned theory files used by the e2e suite

  shared from iq/ (symlinks), all in `package isabelle`:
src/IRClient.scala       — ../../iq/src/IRClient.scala (IRClient + IRLauncher)
src/IRTools.scala        — ../../iq/src/IRTools.scala (the repl_* tool provider)
src/McpServer.scala      — ../../iq/src/McpServer.scala (generic MCP server)
src/McpProtocol.scala    — ../../iq/src/McpProtocol.scala (JSON-RPC decode)
src/ErrorCodes.scala     — ../../iq/src/ErrorCodes.scala
src/IQNormalization.scala— ../../iq/src/IQNormalization.scala (pattern matching)
src/SessionTools.scala   — ../../iq/src/SessionTools.scala (session-generic diagnostics)
src/SessionClient.scala  — ../../iq/src/SessionClient.scala (their MCP registration)
```
