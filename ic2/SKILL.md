---
name: ic2
description: "Activate when the user asks to work on an Isabelle session or theory (`.thy`) — make changes, develop a proof, fix a proof, resolve a sorry, refactor tactics, chase down an error. Prefer over `isabelle build`. If the user has not already picked a tool, clarify whether IC2 (headless, CLI-driven) or I/Q (interactive, jEdit GUI) is the right fit for the task; in headless/agent contexts default to IC2."
---

# Working on Isabelle theories

## Which tool

- **IC2** — headless, CLI-driven: iterating on a theory from a shell or an agent,
  batch-checking, diagnostics, no display available. Entry point
  `isabelle ic2 --help`. Default in headless/agent contexts, and what the rest of
  this skill covers.
- **I/Q** — the user is interactively driving Isabelle/jEdit. Use the I/Q MCP
  server; if no connection is established, say so.
- **Batch build** — one-shot `isabelle build`. ONLY if the user explicitly asks.

If it is unclear, ask. Mentions of jEdit or I/Q mean I/Q; "IC2" or "headless"
means IC2.

## The two loops

Checking a theory and developing a proof are different jobs with different tools.

| | tool | cost per iteration | answers with |
|---|---|---|---|
| Does this theory go through? | `isabelle ic2 check` | a client JVM start (~2 s), another for each `check status` poll, and re-execution of every command from the edit to the end of the theory | a verdict |
| Does this *proof step* go through? | an I/R REPL (`ic2 repl-create`) | one round-trip to the resident prover, from the REPL's cached state | the new goal state |

So: **`check` locates the problem and confirms the fix. A REPL does the work in
between.** Whenever `check status` can locate a failure, it prints the
`repl-create` command for that line.

### The loop, concretely

```bash
# 0) once: a resident server (skip if `ic2 server status` already shows one ready)
isabelle ic2 server start --daemon -l AutoCorrode -d /abs/AutoCorrode
isabelle ic2 server status                        # wait for state=ready

# 1) check once — find out where the theory actually stands
isabelle ic2 check /abs/path/Foo.thy
isabelle ic2 check status                         # -> error: /abs/path/Foo.thy:87
                                                  #    + the repl-create command

# 2) fork a REPL at the failing proof and iterate THERE. REPL names must be
#    fresh, so name it after the line (`check status` suggests exactly this).
isabelle ic2 repl-create /abs/path/Foo.thy:87 r87
#    prints the goal state and the token/port to drive this REPL. Set them up
#    once (see below); every step here reuses $IR.
$IR step r87 'apply (induction xs)'               # try a step
$IR state r87 -1                                  # look at the goal
$IR sledgehammer r87 5                            # ask for a proof
$IR fork r87 r87_sub -1                           # sub-REPL from the latest state
$IR text r87                                      # the accumulated script

# 3) write the proof into Foo.thy, confirm — once — and drop the REPL
isabelle ic2 check /abs/path/Foo.thy
isabelle ic2 check status
$IR remove r87                                    # frees the name for lap 2
```

Set `$IR` up once per server from what `repl-create` (or `ic2 server status`)
prints — the token and port are stable for the server's lifetime. The token must
go in the environment, NOT in the variable: a leading `VAR=value` is only
recognised when the shell parses the line, so `IR="IR_AUTH_TOKEN=… python3 …"`
would try to execute a command named `IR_AUTH_TOKEN=…`.

```bash
export IR_AUTH_TOKEN=<token>
IR="python3 /abs/AutoCorrode/ir/repl.py cli --port <port>"
```

Reusing a name fails (`REPL "r87" already exists`): `$IR remove r87` first, or
pick another. `fork`'s last argument is a **state index** (`0` = base, `-1` = latest), not a
subgoal number. `$IR text r` returns the concatenated Isar text of the REPL's
steps — it does not include the `lemma` line unless the REPL was forked from
before it, so check what you have before pasting into the theory.

Use `check --line N` to narrow a check after a *structural* edit (a changed
definition, a new lemma, a moved block), not to iterate on a tactic.

For the proof-development method itself — building a frame of `sorry`s top-down,
one sub-REPL per `sorry`, merging back — follow the **isar-proof** skill, via the
tool-name translation below.

## Driving a REPL: MCP tool ↔ `repl.py cli`

Same I/R engine, two front ends. `isar-proof`'s workflow applies once you
translate the tool names (it writes them `mcp__iq__repl_*`). The rule:
**`repl_X(repl, ...)` → `X R ...`** — drop the `repl_` prefix, arguments in the
same order. `R` is a REPL name, `IDX` a state index (`0` = base, `-1` = latest).
The exceptions:

| I/Q MCP tool | `repl.py cli` form |
|---|---|
| `repl_connect()` | nothing to do — ic2 brings I/R up at `server start`; confirm with `$IR repls` |
| `repl_init_from_source(repl, file, pattern)` | `isabelle ic2 repl-create FILE:LINE R` — only ic2 can resolve a source line |
| `repl_list()` | `repls` |
| `repl_find_theorems(repl, query, max_results)` | `find-theorems R N 'QUERY'` — note N *before* QUERY |
| `repl_raw(ml_code)` | `raw -- 'ML'` |

`$IR help` prints the full verb table. Semantics carry over exactly, including the
important one: **a failed `step` leaves the REPL state unchanged — do not `back`
after a failure**, just re-`step` with different text.

With `--mcp` the `repl_*` tools are *also* served over MCP (both front ends
coexist), and the left-hand column then applies directly — prefer that. Connecting
needs the stdio↔TCP bridge and an `authenticate` call; see "Connecting an MCP
client" in ic2/README.md.

## Common gotchas

- `isabelle` is the Isabelle installation, e.g. `/Applications/Isabelle2025-2.app/bin/isabelle`. If `ic2` is unavailable, register the component with `make -C ic2` in the AutoCorrode repository.
- Server lifecycle, `check`, `query`, `repl-create` all have their own `isabelle ic2 <subcommand> --help`.
- ic2 `check attach` is a live-TTY human UI — rejects agent contexts; use `check status` for polling.
- Prefer absolute `.thy` paths: the CLI resolves relative ones against YOUR cwd, not the server's, and the MCP `check` tool rejects them outright.
- If `server status` reports `no I/R`, the whole REPL path is unavailable — `pip install -r ir/requirements.txt` and restart the server without `--no-iq`.
- Server discovery is by name; when multiple are running, pass `-n NAME`.
- `repl-create` needs its FILE to be a checked node — run `check` on it once first.
- At most one check runs server-wide; a second is refused while one is in flight.
