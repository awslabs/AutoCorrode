# Isabelle/Check (I/C)

I/C provides **file-oriented proof checking** on top of [I/R](../ir/README.md) (Isabelle/REPL). Point it at a `.thy` file — it discovers sessions from I/R's configured directory, resolves cross-session dependencies, checks each file with precise per-command error reporting, and supports incremental rebuild so that changing one file only reprocesses what's necessary.

I/C is stateless: it connects directly to a running I/R REPL, recovering all needed state from I/R queries and disk on each invocation. The I/R REPL persists across invocations, so proof state (steps, theories) survives. Dependencies are classified and executed in parallel for throughput.

## Quick Start

```bash
# 1. Start I/R REPL (requires Isabelle). Pin the auth token so both
#    server and client can find it without manual copy-paste. Pass
#    --dir for every directory containing a ROOT/ROOTS file you want
#    I/C to discover sessions from.
export IR_AUTH_TOKEN=$(python3 -c 'import secrets; print(secrets.token_urlsafe(24))')
python3 ../ir/repl.py --session HOL --server-only --dir test

# 2. Check a file that succeeds (connects directly to I/R on port 9147)
python3 ic_client.py check test/check_all/Check_All.thy
#   OK   Check_All

# 3. Check a file that fails — I/C reports the exact line and error
python3 ic_client.py check test/check_error/Check_Error.thy
#   ERR  Check_Error:6: Failed to apply initial proof method:
#   goal (1 subgoal):
#    1. 0 = 1
#   At command "by"

# 4. Check with parallelism (6 concurrent connections)
python3 ic_client.py check test/check_all/Check_All.thy -j 6
```

### Auth token

I/R always requires a token on every TCP connection. The two supported
flows are:

- Set `IR_AUTH_TOKEN` **before** starting `repl.py` (as above). Every
  subsequent `ic_client.py` invocation from the same shell reads the
  token from the environment automatically.
- Or: read the `IR_Repl.token: <value>` line printed by `repl.py` on
  startup, then pass it explicitly with `python3 ic_client.py
  --repl-token <value> check ...`.

## Commands

| Command | Description |
|---------|-------------|
| `check <path>` | Discover sessions via ROOT/ROOTS, check file + deps, incremental rebuild on change |
| `status` | Show I/C state (REPLs, markers, staleness) — read-only |
| `clean` | Remove all ic.* REPLs |
| `heapdiff <path>` | Show heap-vs-disk segment comparison for diagnosing unexpected segment inits |

### check options

| Flag | Description |
|------|-------------|
| `-j N` / `--jobs N` | Number of parallel jobs (default: 1) |
| `--timeout N` | Per-step timeout in seconds (default: 0 = use I/R default) |
| `-q` | Suppress progress output (quiet) |
| `-v` | Show extra detail |
| `--always-stepwise` | Never use Ir.load_theory for file deps (auto-enabled when `$ISABELLE_REMOTE` is set) |
| `--dry-run` | Print classification/plan table without executing |
| `--resolve-deps-via-reload` | Diamond deps: reload REPL'd theories from source |
| `--resolve-deps-via-repl` | Diamond deps: step importing theories via REPL |
| `--resolve-deps-via-lines-heuristic` | Diamond deps: choose based on line count (default) |

## Session-based `check`

`check` is the single entry point that handles everything. It uses Isabelle's ROOT/ROOTS file conventions for session and dependency discovery. Session directories are fetched automatically from I/R's `--dir` configuration (via the `/info` command), so the client doesn't need to specify them.

**Import resolution** follows Isabelle conventions:
- `imports A` — theory A in the same session
- `imports S.A` — theory A in session S (discovered via I/R's session directory)
- `imports HOL-Library.Multiset` — external session theory (loaded via `Ir.load_theory`)

**Incremental rebuild**: unchanged dependencies are never re-stepped; within a changed file, unchanged command prefixes are preserved — only the changed tail is re-stepped. Change detection uses content hashes (own file + dependency files) stored in markers, plus segment comparison against the heap for heap theories.

To check all files, iterate `.thy` files and call `check` on each — the REPL tracks proof state, so deps already checked by earlier calls are reused automatically.

## Error Reporting

Errors are reported with the exact file and line number of the failing command, plus the full Isabelle error message. When a file fails, its dependents are marked stale rather than checked.

## Files

| File | Description |
|------|-------------|
| `ic_core.py` | Types, ROOT/ROOTS parsing, session discovery, dep resolution, command splitting |
| `ic_check.py` | Check engine: CLASSIFY/ASSIGN/EXECUTE pipeline, parallel execution, REPL interaction |
| `ic_status.py` | Read-only status display (REPLs, markers, staleness) |
| `ic_repl.py` | TCP client to I/R REPL + connection pool |
| `ic_client.py` | CLI client |
| `ic_snippets.ML` | Isabelle/ML helpers loaded into I/R at runtime |
| `test_ic_core.py` | Unit tests (no Isabelle needed) |
| `test_ic_integration.py` | Integration tests (needs running I/R REPL) |
| `test/` | Test fixture .thy files |
| `run_tests.sh` | Test runner (auto-starts I/R REPL for integration tests) |

See [IMPLEMENTATION.md](IMPLEMENTATION.md) for internals (command splitting, dependency resolution, parallel architecture).

## Testing

```bash
# Unit + integration tests (default, auto-starts I/R REPL)
./run_tests.sh

# Unit tests only (no Isabelle needed)
./run_tests.sh --unit-only

# Integration tests only
./run_tests.sh --integration-only

# Run a single test
./run_tests.sh --integration-only -k test_name

# Run all tests with parallel execution
IC_POOL_SIZE=3 ./run_tests.sh --integration-only
```
