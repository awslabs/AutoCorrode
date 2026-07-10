# IC2 — headless, persistent Isabelle sessions

IC2 manages headless, persistent Isabelle sessions (`Headless.Session`) from the
command line — similar to `isabelle server` and `isabelle client`, but
integrated with [I/R](../ir) and [I/Q](../iq). A session stays resident and
serves work against it, avoiding repeated per-invocation session/heap loads.

`isabelle ic2` is a single command-line tool. Server lifecycle lives under
`ic2 server`; everything else acts on a running server, found by name (so several
run side by side, with no host/port/token to configure):

  * **`ic2 server`** — start/stop/inspect the resident session.
  * **`ic2 check FILE...`** — type-check `.thy` files, with live progress and a
    scriptable exit code.
  * **`ic2 query SUBTOOL FILE`** — read-only diagnostics over the session.
  * **`ic2 load-files FILE...`** — parse theories into the graph without
    evaluating, so structural queries work at near-zero cost.
  * **`ic2 repl-create FILE:LINE NAME`** — fork an interactive I/R REPL at a
    source location.

Unless `--no-iq`, the server also brings up I/R against the same session (`--mcp`
additionally serves the `repl_*` tools over MCP), so an agent can drive Isar
proofs without a separate Isabelle/jEdit + I/Q.

## Prerequisites

  * **Isabelle2025-2** — IC2 is built and tested against it (the headless
    goal-state readout relies on its `show_states` option). Set `ISABELLE_HOME`
    to the directory containing the `isabelle` binary.
  * For the I/R / MCP integration (on by default): **`python3`** and the I/R
    Python deps — `pip install -r ../ir/requirements.txt`. Without them, I/R
    bring-up is skipped and `server status` shows `no I/R`; plain checking still
    works. Start with `--no-iq` to skip I/R deliberately.

## Quick start

```bash
# Register the component (once). A fresh checkout also needs the JAR built:
#   `make` (in ic2/) or `isabelle scala_build`.
isabelle components -u /path/to/AutoCorrode/ic2

# Start a background server:
isabelle ic2 server start --daemon -l HOL
# ...or for a session tree like AutoCorrode:
isabelle ic2 server start --daemon -l AutoCorrode -d AutoCorrode

# Wait until the session is ready, then check a file:
isabelle ic2 server status                  # state: building → loading → ready
isabelle ic2 check /abs/path/to/Foo.thy     # exit 0 = ok, 1 = first error

# Stop:
isabelle ic2 server stop
```

The flags mirror `isabelle jedit` (`-l` logic, `-d` session dir, `-i` include
session, `-o` option, `-n` server name). `server start` runs in the foreground
until Ctrl-C; `--daemon` backgrounds it and logs to
`$ISABELLE_HOME_USER/ic2/<name>.log` (override with `-L FILE`).

**Readiness.** `--daemon` returns 0 once the server is *serving* — but a cold
heap build can outlast its ~30 s wait, in which case it still returns 0 with a
"still starting" note and the build continues in the background. A `check`
submitted before the session is ready fails fast, so gate on
`ic2 server status` reporting `state: ready` first (or `ic2 server attach` to
watch a cold build to completion).

## `ic2 check`

Type-checks `.thy` files (absolute paths) against the running server, showing one
live progress bar per theory and stopping at the first error.

```bash
isabelle ic2 check Foo.thy Bar.thy      # check both, stop at first error
isabelle ic2 check Foo.thy --line 87    # partial: only up to line 87
isabelle ic2 check Foo.thy -P           # plain output (no ANSI bars)
```

`--line N` evaluates only the prefix up to line `N`, leaving the rest
unprocessed and re-checkable — handy for iterating on the line you're editing.
On Ctrl-C the check is cancelled and interrupted promptly; the server stays up.

Exit codes drop into scripts and editor integrations:

| code | meaning |
|---|---|
| 0 | all checks passed |
| 1 | a check failed (a proof error was found, or the run was stopped) — **also** a bad FILE argument (not `.thy`, or does not exist) |
| 2 | bad usage (no FILE, or `--line` with ≠1 file) |
| 3 | server unreachable, not ready, or connection dropped mid-check |

Note the code-1 overlap: a missing or non-`.thy` path exits 1, the same as a
real proof error. If a script must distinguish them, validate the path before
calling `check`.

**Detached checks.** `--detach` submits and returns immediately; the check keeps
running server-side after the command exits. Track it without `-n` ambiguity:

```bash
isabelle ic2 check --detach Foo.thy     # "submitted (...)"
isabelle ic2 check status               # state + per-theory status
isabelle ic2 check attach               # stream to completion
isabelle ic2 check cancel               # abort the in-flight check
```

**At most one check runs at a time, server-wide** (`use_theories` is not safe to
run concurrently on one session). A second check is refused while one is in
flight — cancel it and resubmit the merged set.

## `ic2 query`

Read-only diagnostics over the session — the CLI form of the MCP diagnostic
tools. One-shot: each invocation opens a connection, asks, prints, exits. Output
is human-readable; `--json` emits the raw tool JSON for piping to `jq`.

```
$ isabelle ic2 query entities Diagnostics.thy
6 entit(ies):
  line 13    definition   answer
  line 16    datatype     color
  line 23    lemma        structured

$ isabelle ic2 query diagnostics Trivial_Fail.thy
error (file): 1 found:
  /abs/path/Trivial_Fail.thy:6: Failed to finish proof

$ isabelle ic2 query state-at Foo.thy --pattern 'by simp'   # goal at that command
$ isabelle ic2 query diagnostics Foo.thy --json | jq .      # raw payload
```

| SUBTOOL | FILE | reports |
|---|---|---|
| `list-files` | — | loaded nodes + per-node status |
| `processing-status` | ✓ | PIDE processing counts |
| `document-info` | ✓ | whole-theory command/error/warning totals |
| `diagnostics` | ✓ | errors or warnings (`--severity`, `--scope`) |
| `sorry` | ✓ | sorry/oops positions + enclosing proof |
| `entities` | ✓ | declared entities (lemma/definition/fun/…) |
| `proof-blocks` | ✓ | proof blocks with text + line ranges |
| `spans` | ✓ | flat list of parsed command spans |
| `command-info` | ✓ | command metadata/status/result at a selection |
| `state-at` | ✓ | proof state (goal + context) at a selection |

The selection tools take one of `--offset N` / `--line N` / `--pattern P` to
point at a command; `--line N` resolves to the command ending on or before that
line (as jEdit does). The FILE must be a loaded session node — check it
(`ic2 check`) or parse it (`ic2 load-files`) first.

## `ic2 load-files`

Parses `.thy` files into the document graph **without evaluating any commands** —
no ML runs, no proof state. The structural `query` subtools then work on the
loaded nodes at near-zero cost, and a later `ic2 check` pays only the evaluation
cost, not the parse cost.

```bash
isabelle ic2 load-files Foo.thy Bar.thy
isabelle ic2 load-files Foo.thy --print   # also dump each node's parsed spans
```

## `ic2 repl-create`

Starts an *interactive* [I/R](../ir) proof REPL anchored at a source location —
e.g. to develop a proof step-by-step from the goal state at that line. (The bare
`repl.py cli` can't do this: mapping a source line to a prover command id needs
the live document, which only the ic2 server holds.)

```
$ isabelle ic2 repl-create AutoCorrode/Misc/Word.thy:142 w
REPL 'w' from document Misc.Word cmd 37
<proof state at that command...>

Drive this REPL with `repl.py cli`:
  step:       IR_AUTH_TOKEN=… python3 …/ir/repl.py cli --port 59498 step w 'apply simp'
  show state: IR_AUTH_TOKEN=… python3 …/ir/repl.py cli --port 59498 state w -1
  full text:  IR_AUTH_TOKEN=… python3 …/ir/repl.py cli --port 59498 text w
```

`repl-create` resolves `LINE` to the command spanning it, creates the REPL, and
prints its initial state plus the exact `repl.py cli` commands to drive it. Each
is a one-shot call against the same server's I/R bridge — `step` adds an Isar
command, `state w -1` shows the latest goal, `text w` prints the script, `raw`
sends arbitrary ML. `FILE` must be a checked node.

## `ic2 server`

```bash
isabelle ic2 server start [--daemon] [--no-iq] [--mcp] -l NAME [-d DIR] [-n NAME]
isabelle ic2 server status [-n NAME] [--full]
isabelle ic2 server attach [-n NAME]
isabelle ic2 server stop   [-n NAME]
```

`start` builds the heap if needed, then serves checks and queries until stopped.
Key flags beyond the `isabelle jedit` set: `--daemon` (background it — see
[Readiness](#quick-start) for the cold-build caveat), `-n NAME` (server name, so
several coexist), `-N` (no build — fail fast if the heap is missing), `--no-iq` /
`--mcp` (see below).

`status` prints a summary line — session, pid, uptime, idle/busy, checks in
flight — plus the I/R endpoints. Without `-n` it surveys every running server;
during the initial heap build it shows a live phase (building → loading →
ready). `--full` adds per-node processing/errors.

```
$ isabelle ic2 server status
default: session=HOL pid=12345 up=42s idle conns=1
    I/R repl.py: port=59498 token=GSJpumMw…  (raw I/R protocol)
    I/R MCP:     port=8765  token=a1b2c3d4…  (connect MCP repl_* here)
    I/R cli:     IR_AUTH_TOKEN=GSJpumMw… python3 …/ir/repl.py cli --port 59498 raw -- 'Ir.theories ()'
plain:   session=HOL pid=12346 up=5s idle conns=1
    no I/R
```

`attach` follows a backgrounded server's console log (including heap-build
progress) until it shuts down or you Ctrl-C. `stop` shuts the named server down.

## I/R and MCP integration

Unless `--no-iq`, the server brings up [I/R](../ir) against the same session it
uses for checks, so an agent can drive Isar proof development without a separate
Isabelle/jEdit + [I/Q](../iq). Bring-up is delegated to the shared `IRLauncher`
(the same code path I/Q uses): it loads the I/R ML into the prover, opens a
token-authenticated `ML_Repl` listener, spawns `ir/repl.py` as the client-facing
bridge, and connects. `ic2 server status` prints the bridge's port/token and a
ready-to-paste `repl.py cli` invocation.

With `--mcp` (opt-in, off by default), the server also stands up a generic
`McpServer` and registers three tool families:

  * the I/R **`repl_*`** tools — interactive proof exploration, the same tools
    I/Q exposes;
  * **session diagnostic tools** — `list_files`, `get_diagnostics`,
    `get_sorry_positions`, `get_entities`, `get_proof_blocks`,
    `get_command_info`, `get_state_at`, `load_files`, `status`, etc. These read
    only the document snapshot (base PIDE, no jEdit), so the identical code
    serves ic2's headless session and I/Q's live PIDE session — the `query` CLI
    routes through the same dispatch;
  * **`check` / `check_async` / `check_status` / `check_cancel`** — the MCP
    analogue of `isabelle ic2 check` (with MCP progress notifications).

### Connecting an MCP client

The MCP server is the **same one I/Q uses**: a raw **TCP** listener speaking
newline-delimited JSON-RPC on loopback **port 8765** (scanning upward to the
first free port if taken) — *not* an HTTP endpoint. Most MCP clients speak stdio
or HTTP, so connect through the stdio↔TCP bridge [`iq_bridge.py`](../iq/iq_bridge.py)
(shipped with I/Q); point it at ic2's port with `IQ_MCP_BRIDGE_PORT`. A typical
client config:

```json
{
  "mcpServers": {
    "ic2": {
      "command": "python3",
      "args": ["/path/to/AutoCorrode/iq/iq_bridge.py"],
      "env": { "IQ_MCP_BRIDGE_PORT": "8765", "IQ_AUTH_TOKEN": "…" }
    }
  }
}
```

Every tool except `initialize` / `tools/list` / `ping` requires auth: the client
must first call the **`authenticate`** tool with the MCP token. That token comes
from `IQ_AUTH_TOKEN` (the same variable I/Q uses) if set, else it is generated
and reported by `ic2 server status` (`I/R MCP: … token=…`). Set `IQ_AUTH_TOKEN`
in both the server's environment and the client config to fix it ahead of time.
The in-prover `ML_Repl` is never advertised, so nothing can connect around the
bridge to the prover.

### Best-effort bring-up

If the `ir/` sources are missing, `python3`/`repl.py` or its deps (see
[Prerequisites](#prerequisites)) are unavailable, or the MCP layer fails, I/R is
skipped and checking still works — `server status` shows `no I/R`, and the reason
goes to the daemon log (`ic2 server attach` to see it). repl.py runs with
`--no-heap-db`, so recorded-segment forking is off (that needs a heap built with
`record_theories=true`). The AutoCorrode tree is found via `$AUTOCORRODE_BASE`,
else the tree this component lives inside.

## Access control

A server listens on a Unix-domain socket at `$ISABELLE_HOME_USER/ic2/<name>.sock`;
the client derives the same path from the name. There is **no auth token on the
control socket** — access control is the *parent directory*, which `ic2 server
start` keeps mode `0700` (owner-only). A crashed server can leave a stale socket;
on startup the server probes it, reclaims it if nothing is listening, and refuses
to start if a live server already holds the name.

**Threat model.** IC2 aims to keep out remote hosts (the control socket is
AF_UNIX, so it is not network-reachable) and other local OS users (the `0700`
directory). It does **not** defend against other processes running as the same OS
user — and it does not try to. Note in particular:

  * The control socket is unauthenticated, and a `check`ed theory may contain
    `ML‹…›` blocks, so any process that can reach the socket can run arbitrary ML
    as the daemon user and read the layered tokens via the `status` op. The
    `0700` directory is the only boundary; there is no defence-in-depth behind it.
  * There is **no read/write-root sandbox**: the daemon will parse, check, and
    read any file its user can (unlike I/Q, which restricts to allowed roots).
  * The `0700` mode is set right after the directory is created, not atomically
    at creation, and is **not applied on Windows** (POSIX permissions are
    unavailable there). On a shared Windows host the directory is not a boundary.

The I/R and MCP endpoints layered on top *are* token-authenticated (see above),
but those tokens are handed out over the unauthenticated control socket, so they
add no protection against a same-user process — only against network/other-user
access, which the socket already blocks.

## Tests

```bash
isabelle ic2_test all                # default — all tests
isabelle ic2_test unit               # unit tests (no session)
isabelle ic2_test e2e                # end-to-end tests (uses HOL)
isabelle ic2_test -v -t check_ok all # verbose, single test
```

E2E tests start their own `ic2 server`, run every scenario against it (including
`--daemon` launch and `ic2 server stop`), and shut it down. The first run builds
the HOL heap (slow); subsequent runs reuse it. Fixtures live in `test/fixtures/`.

## Files

```
etc/build.props     — component manifest
etc/settings        — sets $ISABELLE_IC2_HOME
src/ic2.scala       — the `isabelle ic2` front door (subcommand dispatch)
src/daemon.scala    — `ic2 server start`: daemon, --daemon launch, status op
src/iq.scala        — I/R + MCP bring-up (IRLauncher, McpServer + tools) and the
                      single-slot Check model (Job, cancel/reset, --line worker)
src/client.scala    — check / query / load-files / server / repl-create + UIs
src/endpoint.scala  — socket-path discovery + the 0700 directory
src/json_io.scala   — newline-delimited JSON over a socket channel
src/test_tool.scala — `isabelle ic2_test` runner
src/tools.scala     — Isabelle_Scala_Tools registration

  shared from iq/ (symlinks), all in `package isabelle`:
src/IRClient.scala      — IRClient + IRLauncher
src/IRTools.scala       — the repl_* tool provider
src/McpServer.scala     — generic MCP server
src/McpProtocol.scala   — JSON-RPC decode
src/SessionTools.scala  — session-generic diagnostics
src/SessionClient.scala — their MCP registration
src/ErrorCodes.scala, src/IQNormalization.scala
```

For the wire protocol (newline-delimited JSON) and the internals of checking,
cancellation, and the headless goal-state plumbing, see the comments in
`src/daemon.scala` and `src/iq.scala`.
```
