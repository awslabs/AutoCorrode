# I/C Implementation Details

## Architecture

```
I/C Client (CLI: ic_client.py)
  |  calls check()/clean() from ic_check.py
  v
I/C Check Engine (ic_check.py)
  |-- bootstrap()         -- Ir.theories() + Ir.repls() state recovery
  |-- ic_core.py          -- types, session discovery, dep resolution
  |
  |-- CLASSIFY            -- ProcessPoolExecutor (per-task ClassifyInput)
  |-- ASSIGN              -- staleness propagation, plan assignment
  |-- EXECUTE             -- ThreadPoolExecutor + ReplPool (dataflow futures)
  |
  |  TCP (line-based, <<DONE>> sentinel) via ic_repl.py
  v
I/R REPL Server (repl.py, independently running)
```

I/C is stateless: each invocation recovers all state from I/R queries + disk. The I/R REPL persists across invocations, retaining proof state (steps, theories).

## State Recovery

On each invocation, `ic_check.check()` recovers state from I/R:

| What | How |
|------|-----|
| Loaded theories | `Ir.theories()` |
| Active REPLs + step counts | `Ir.repls()` |
| Markers | `ic_symtab_get_all()` |
| Sessions | `fetch_dirs(repl)` + `discover_sessions(dirs)` |
| File metadata | Re-parse .thy files from disk |

## Per-Theory REPLs

Each file gets its own REPL, named `ic.{session}.{name}` (e.g., `ic.MySession.Utils`). After successful stepping, REPLs are **pinned** (snapshot of theory state). Downstream REPLs reference deps via `pin@name` syntax in their `Ir.init` spec, e.g. `Ir.init "ic.S.Target" ["pin@ic.S.Dep1", "pin@ic.S.Dep2"]`.

Dependencies are resolved before stepping the target:

- **From heap**: theory already in the Isabelle heap — passed as a parent to `Ir.init`
- **From file**: loaded via `Ir.load_theory` from source
- **From REPL**: dependency was checked in a previous call and its REPL is still active — referenced via `pin@repl_name` in `Ir.init`, reusing its pinned state

## REPL Lifecycle (Pin/Rebase)

### Pins

After a REPL completes stepping, `Ir.pin "repl_name"` snapshots its theory state. Other REPLs reference this snapshot via `pin@repl_name` in their `Ir.init` parent list. Pins are stable across re-checks until the owning REPL is removed or rebased.

### InitStrategy

| Strategy | When used | Action |
|---|---|---|
| `INIT` | REPL absent, or has `From_Segment` origin | Remove old REPL (if any), `Ir.init` fresh |
| `REBASE` | REPL persists (non-segment origin), parent was rebuilt | `Ir.rebase` updates base to new parent pin, then truncate + re-execute all steps |

`REBASE` avoids removal, which would invalidate downstream pin references and require careful ordering. Instead, the existing REPL is updated in-place.

### `has_persistent_repl`

Determines whether a dep's REPL survives execution (used for REBASE eligibility):
- `ReplChanged` — yes (incremental restep keeps REPL)
- `ReplCachedError` — yes (error recovery keeps REPL)
- `NoRepl` with existing non-segment REPL whose origin imports match the file's current imports — yes (stale propagation converted it, but REPL is rebase-compatible)
- `NoRepl` whose imports have changed since the REPL was built — no (the REPL must be removed and re-`Ir.init`'d with the new parent list)
- All others — no

## Pre-Execution Removal

Plans declare a `removes_repl` property:
- `CheckPlan(INIT)` — True
- `SegmentInitPlan` — True
- `LoadFilePlan` — True
- All others — False

### `remove_stale_repls`

1. Collect REPL names from plans where `removes_repl` is True.
2. Expand with **pin dependents**: external REPLs whose origin string references a to-be-removed REPL (via `pin@X` → depends on X).
3. Compute `removal_order` via topo sort of pin-dep graph.
4. Remove in order (dependents first).

### `removal_order`

Builds a directed graph from origin strings: if REPL B has origin containing `pin@A`, then B depends on A. Topological sort of this graph, reversed, gives safe removal order (dependents before their dependencies).

### Busy REPL blocking

If a REPL in `Claimed` state holds a pin dependency on a to-be-removed REPL, removal is blocked. See [Busy REPLs](#busy-repls).

## Busy REPLs

Parsed from `Ir.repls()` output as `BusyReplInfo` (name + origin string). A REPL is busy when it is in `Claimed` state (being stepped by another thread/client).

| Context | Behavior |
|---|---|
| `check()` | Aborts if a needed dep REPL is busy |
| `clean()` | Aborts if any REPL is busy |
| `status` | Displays busy REPLs inline with "BUSY" marker |
| Removal | Blocks removal if busy REPL holds pin dep on target |

## Marker Storage

State markers are stored in an ML-side `Synchronized.var` holding a `string Symtab.table` (`ic_mgmt_tab` in `ic_snippets.ML`). This provides thread-safe key-value storage without the overhead of a dedicated REPL. Markers are written via `ic_symtab_set` and read in bulk via `ic_symtab_get_all` (tab-separated `key\tvalue` output). Three marker types:

- **SteppedMarker**: `ic:hash=H:cmds=N:deps=[dep1=h1,...]:seg=SPEC` — records file hash, command count, dependency hashes, and optional segment spec
- **LoadedMarker**: `ic:loaded:hash=H` — records hash for `Ir.load_theory`'d files
- **HeapVerifiedMarker**: `ic:heap:hash=H` — caches heap-vs-disk comparison result

Dependency hashes (`deps=`) track content hashes of file dependencies. On recheck, if any dep's hash changed, the REPL is stale even if the file itself is unchanged.

## CLASSIFY / ASSIGN / EXECUTE Pipeline

### CLASSIFY (`classify_files`)

Runs in a `ProcessPoolExecutor`. Each theory gets a `ClassifyInput` (entry, marker, REPL info, dep hashes, symbols) — small, picklable. Workers get their own I/R connections via `initializer`. Results collected via `as_completed`.

Classifications (each has `is_rebuilding` property for staleness propagation):

| Classification | Meaning | Rebuilding? |
|---|---|---|
| `InHeap` | Theory in heap, unchanged | No |
| `HeapStale` | Heap theory, source changed on disk | Yes |
| `HeapStaleDep` | Heap theory whose dep was rebuilt | Yes |
| `ReplClean` | Has REPL, file + deps unchanged, previous check OK | No |
| `ReplCachedError` | Has REPL, file unchanged, previous check had error | No |
| `ReplChanged` | Has REPL, file changed (includes diff for incremental) | Yes |
| `FileLoaded` | Loaded via `Ir.load_theory`, unchanged | No |
| `FileNotLoaded` | Not yet loaded, needs `Ir.load_theory` | Yes |
| `NoRepl` | No REPL, needs loading/stepping | Yes |

### ASSIGN (`assign_methods`)

Global analysis producing a `DepPlan` per dependency:

1. **`propagate_staleness`** — walks deps in build order. If a dep `is_rebuilding`, downstream deps are converted: `ReplClean`/`ReplCachedError` → `NoRepl` (or `HeapStaleDep` for heap), `FileLoaded` → `FileNotLoaded`. `InHeap` deps become `HeapStaleDep` if any file dep is not `InHeap`. Returns `rebase_rebuilding` set (deps whose parent was rebuilt but which have a persistent REPL) and tracks `has_persistent_repl` per dep.

2. **`build_plans`** — maps classification to plan. Uses `rebase_rebuilding` set to assign `CheckPlan(REBASE)` vs `CheckPlan(INIT)`:

| Plan | From | Action |
|---|---|---|
| `SkipPlan` | InHeap, ReplClean, FileLoaded | Reuse existing state (0 steps) |
| `RecoverErrorPlan` | ReplCachedError | Re-execute from failing command |
| `LoadFilePlan` | NoRepl, FileNotLoaded | Call `Ir.load_theory` |
| `CheckPlan(INIT)` | HeapStaleDep, NoRepl (no persistent REPL) | Remove + `Ir.init` fresh |
| `CheckPlan(REBASE)` | NoRepl (persistent non-segment REPL, in `rebase_rebuilding`) | `Ir.rebase` + truncate + restep |
| `IncrementalPlan` | ReplChanged | Truncate + restep changed tail |
| `SegmentInitPlan` | HeapStale | Init from heap segment + step tail |
| `TargetUnchangedPlan` | InHeap/FileLoaded (target) | Report OK with 0 steps |

Each plan type has `import_name()` returning the theory reference for downstream parents (REPL name or heap name).

3. **`resolve_diamonds`** — detects diamond conflicts, groups them, applies strategy
4. **`compute_theory_refs`** — calls `plan.import_name()` for each dep

### EXECUTE (`execute_plans`)

Parallel dataflow via `ThreadPoolExecutor` + `ReplPool`. Each dep gets a future. Jobs wait for their dep futures before acquiring a pool connection and executing. Independent deps at the same topological level run concurrently.

Key design: **wait for deps BEFORE acquiring connection** — prevents deadlock where all workers hold connections while blocked on dep futures.

Failure propagation: if a dep future resolves as failed, downstream jobs return stale immediately without doing I/R work.

Progress display: multi-line block for concurrent stepping (theory name + progress bar per active job). Target keeps its own progress bar (single-threaded by design — all deps completed before target runs).

## Diamond Dependency Resolution

A diamond conflict occurs when `Ir.load_theory` would rebuild a theory that has an active REPL. Before grouping, `expand_with_descendants` expands the conflict set with descendant REPLs (REPLs whose pin-dep chain traces back to a conflicting REPL).

Three strategies:

- **Reload** (`--resolve-deps-via-reload`): load conflicting REPL'd theories from source
- **REPL** (`--resolve-deps-via-repl`): step the dependency via its own REPL
- **Heuristic** (`--resolve-deps-via-lines-heuristic`, default): compare line counts

## Command Splitting

I/C uses `ic_parse_spans` (defined in `ic_snippets.ML`, invoked inside a REPL via `ML_val`) to split theory bodies into individual Isar commands using Isabelle's own `Outer_Syntax.parse_text`. Command modifier spans (`qualified`, `private`) are merged with the following command.

## Incremental Rebuild

### Within-file incremental

When a file's body changes but its imports are unchanged:
1. Diff old commands (from `Ir.text()` + `ic_parse_spans`) against new (from disk)
2. `Ir.truncate` the REPL to just after the last unchanged command
3. Re-step only the changed tail

For segment-init REPLs (tail-only steps), the diff is aligned against the tail, not the full body. If the segment boundary shifted, the REPL is re-init'd from the new segment point.

### Cross-file rebuild

Staleness propagation in ASSIGN converts downstream deps. Dep hash tracking in `SteppedMarker` detects when a dep's content changed even if the dependent's file is unchanged.

### Error recovery

`ReplCachedError` classification → `RecoverErrorPlan`. The plan carries the commands and body_steps from CLASSIFY. The executor re-steps from the failing command onward. If the error is transient (e.g., ML counter), it may succeed on retry.

## Dependency Resolution

For each import in a theory header:
1. In `files`? — file dependency (`FileImport`)
2. In `loaded_theories`? — heap import (`HeapImport`)
3. Otherwise — external import (`ExternalImport`, needs `Ir.load_theory`)

File deps take priority over heap — if a theory has both a source file and is in the heap, it's treated as a file dep.

Build order: topological sort (Kahn's algorithm). Cycles detected and reported.

## Theory Header Parsing

Regex patterns ported from `isabelle-assistant/src/TheoryMetadata.scala`:

```python
THEORY_PAT  = re.compile(r'(?m)^\s*theory\s+(\S+)')
IMPORTS_PAT = re.compile(r'(?s)\bimports\b\s+(.*?)(?:\bkeywords\b|\babbrevs\b|\bbegin\b|\Z)')
TOKEN_PAT   = re.compile(r'"[^"]+"|[^\s"]+')
```

`IMPORTS_PAT` stops at `keywords`, `abbrevs`, or `begin`. Theories with `keywords` in the header are detected (`has_keywords`) and cannot be checked via REPL.

## ML String Escaping

When sending file body text to `ic_parse_spans` or `Ir.step`, the text is escaped for ML string literals: `\` to `\\`, `"` to `\"`, newlines to `\n`. The I/R server's auto-correction converts `\\<symbol>` back to `\<symbol>` for Isabelle symbol encoding.
