"""I/C Check: stateless proof checking engine on top of I/R REPL.

All state is recovered from I/R queries (Ir.repls(), Ir.theories(), Ir.text())
and disk (ROOT files, .thy files) on each invocation.
"""

import os
import re
import sys
import threading
from collections import defaultdict, deque
import multiprocessing
from concurrent.futures import (ThreadPoolExecutor, ProcessPoolExecutor,
                                Future, as_completed)
from dataclasses import dataclass, field

import copy


class CancellableExecutor(ThreadPoolExecutor):
    """ThreadPoolExecutor that doesn't block on exit.

    The default __exit__ calls shutdown(wait=True), blocking until all
    workers finish — even on KeyboardInterrupt. This override uses
    wait=False so the process can exit immediately on Ctrl+C.
    """
    def __exit__(self, *args):
        self.shutdown(wait=False, cancel_futures=True)
        return False


class CancellableProcessExecutor(ProcessPoolExecutor):
    """ProcessPoolExecutor that doesn't block on exit."""
    def __exit__(self, *args):
        self.shutdown(wait=False, cancel_futures=True)
        return False

from ic_repl import ReplClient, ReplPool, MlOk, MlError, MlResult, strip_ml_noise


from ic_core import (
    DiamondStrategy, InitStrategy, FileStatus,
    ResolvedImport, FileImport, HeapImport, ExternalImport,
    InHeap, HeapFreshness, HeapStaleDep, ReplClean, ReplCachedError,
    ReplChanged, NoRepl, FileLoaded, FileNotLoaded, HeapStale,
    FromFile, FromHeap,
    SegmentDiff, FileClassification,
    DepPlan, SkipPlan, LoadFilePlan, RecoverErrorPlan,
    CheckPlan, TargetUnchangedPlan, IncrementalPlan, SegmentInitPlan,
    FileResult, DepInfo, CheckResponse,
    PlanOk, PlanDepFailed, PlanAbort, PlanResult,
    TheoryHeader, BodyCommand, ChangeInfo, LineInfo,
    FileEntry, SessionInfo,
    parse_theory_file, file_content_hash, ml_escape,
    QualifiedTheory, qualify_import, DepGraph,
    split_body_by_offsets, resolve_dependencies, resolve_import, strip_comments,
    discover_sessions, topological_sort,
)


# --- Step descriptions (shared by verbose logs and dry-run) ---

@dataclass
class StepLoaded:
    """Plan loads theory from file via Ir.load_theory."""
    pass


@dataclass
class StepSkip:
    """Plan reuses existing state."""
    reason: str


@dataclass
class StepCommands:
    """Plan steps commands over a line range."""
    action: str
    first_line: int
    last_line: int
    cmd_count: int | None = None
    suffix: str = ""


StepDescription = StepLoaded | StepSkip | StepCommands


def describe_plan(plan: 'DepPlan', ctx: 'CheckContext',
                  ri: 'ResolvedImport') -> StepDescription:
    """Describe what a plan would do, without executing it."""
    if isinstance(plan, SkipPlan):
        marker = ctx.read_marker(plan.qt)
        if isinstance(marker, HeapVerifiedMarker):
            return StepSkip("from_heap (cached)")
        elif isinstance(marker, LoadedMarker):
            return StepSkip("loaded (up to date)")
        elif isinstance(marker, SteppedMarker):
            return StepSkip("cache matches file")
        elif plan.heap_freshness == HeapFreshness.NO_SEGMENTS:
            return StepSkip("from_heap (no segments)")
        else:
            return StepSkip("from_heap")
    elif isinstance(plan, TargetUnchangedPlan):
        return StepSkip("unchanged (in heap)")
    elif isinstance(plan, LoadFilePlan):
        return StepLoaded()
    elif isinstance(plan, CheckPlan):
        entry = ctx.files.get(plan.qt) if isinstance(ri, FileImport) else None
        if entry:
            return StepCommands("stepwise check",
                                entry.header.body_start_line,
                                entry.total_lines)
        return StepCommands("stepwise check", 0, 0)
    elif isinstance(plan, IncrementalPlan):
        li = plan.change_info.line_info
        n = len(plan.change_info.new_commands) - plan.change_info.first_diff
        return StepCommands("continuing", li.first_changed_line,
                            li.total_lines, n, "(file changed)")
    elif isinstance(plan, RecoverErrorPlan):
        li = plan.line_info
        n = len(plan.commands) - plan.body_steps
        return StepCommands("continuing", li.first_changed_line,
                            li.total_lines, n)
    elif isinstance(plan, SegmentInitPlan):
        li = plan.diff.line_info
        if plan.diff.tail:
            return StepCommands("segment init from heap",
                                li.first_changed_line, li.total_lines,
                                len(plan.diff.tail))
        else:
            return StepSkip(f"segment init from heap at "
                            f"L{li.first_changed_line} - heap matches file")
    raise TypeError(f"Unknown plan type: {type(plan)}")


def format_step_description(desc: StepDescription) -> str:
    """Format for verbose log output."""
    if isinstance(desc, StepLoaded):
        return "loading from file..."
    elif isinstance(desc, StepSkip):
        return desc.reason
    elif isinstance(desc, StepCommands):
        if desc.cmd_count is not None:
            s = (f"{desc.action} - stepping {desc.cmd_count} commands "
                 f"to L{desc.last_line}")
        else:
            s = f"{desc.action} - stepping to L{desc.last_line}"
        if desc.suffix:
            s += f" {desc.suffix}"
        return s
    raise TypeError(f"Unknown step description type: {type(desc)}")


def format_step_short(desc: StepDescription) -> str:
    """Format for dry-run table column."""
    if isinstance(desc, StepLoaded):
        return "load from file"
    elif isinstance(desc, StepSkip):
        return "-"
    elif isinstance(desc, StepCommands):
        if desc.cmd_count is None:
            return f"L{desc.first_line}–L{desc.last_line} (full)"
        return f"L{desc.first_line}–L{desc.last_line} ({desc.cmd_count} cmds)"
    raise TypeError(f"Unknown step description type: {type(desc)}")


# --- State recovery: Ir.repls() parsing ---

@dataclass
class ReplInfo:
    """Parsed info about an active I/R REPL."""
    name: str
    step_count: int
    stale_count: int
    origin: str          # e.g. "theory Main+ic.S.Dep"
    is_current: bool


@dataclass
class BusyReplInfo:
    """A REPL in Claimed (busy) state."""
    name: str
    origin: str
    step_count: int
    stale_count: int
    operation: str   # "step" | "edit" | "replay" | "rebase" | "merge"
    elapsed: str     # raw "X.Xs" string from server


# Matches: "  > name (3 steps, 2 stale, from theory X+Y, pinned [stale])"
#      or: "    name (5 steps, from theory Main)"
# The "from" capture stops before ", pinned" so origin is the bare spec list.
_REPL_PAT = re.compile(
    r'^\s*(>?)\s*(\S+)\s+\((\d+)\s+steps?'
    r'(?:,\s+(\d+)\s+stale)?'
    r',\s+from\s+(.*?)'
    r'(?:,\s+pinned(?:\s+\[stale\])?)?'
    r'\)\s*$'
)

# Matches: "    name (3 steps, 2 stale, from Main, busy [replay] 2.1s)"
_BUSY_PAT = re.compile(
    r'^\s*(\S+)\s+\((\d+)\s+steps?'
    r'(?:,\s+(\d+)\s+stale)?'
    r',\s+from\s+(.*?)'
    r',\s+busy\s+\[(\w+)\]\s+([\d.]+s)'
    r'\)\s*$'
)


def parse_repls_output(text: str) -> tuple[dict[str, ReplInfo], dict[str, BusyReplInfo]]:
    """Parse Ir.repls() output into active and busy ic.* REPLs.

    Returns (active_repls, busy_repls).
    """
    result: dict[str, ReplInfo] = {}
    busy: dict[str, BusyReplInfo] = {}
    for line in text.splitlines():
        # Try busy first: live regex would otherwise greedily capture the
        # busy suffix into origin.
        m = _BUSY_PAT.match(line)
        if m:
            name = m.group(1)
            if name.startswith("ic."):
                busy[name] = BusyReplInfo(
                    name=name,
                    step_count=int(m.group(2)),
                    stale_count=int(m.group(3)) if m.group(3) else 0,
                    origin=m.group(4),
                    operation=m.group(5),
                    elapsed=m.group(6),
                )
            continue
        m = _REPL_PAT.match(line)
        if m:
            name = m.group(2)
            if not name.startswith("ic."):
                continue
            result[name] = ReplInfo(
                name=name,
                step_count=int(m.group(3)),
                stale_count=int(m.group(4)) if m.group(4) else 0,
                origin=m.group(5),
                is_current=m.group(1) == ">",
            )
    return result, busy



def ml_expect(result: MlResult) -> str:
    """Unwrap MlResult, raising RuntimeError on MlError."""
    if isinstance(result, MlError):
        raise RuntimeError(f"ML call failed: {result.error}")
    return result.output


def bootstrap(repl: ReplClient) -> tuple[set[str], dict[str, ReplInfo], dict[str, BusyReplInfo]]:
    """Query Ir.theories() and Ir.repls().

    Returns (loaded_theories, active_repls, busy_repls).
    """
    theories_raw = strip_ml_noise(ml_expect(repl.send('Ir.theories ()')))
    loaded_theories = {line.strip() for line in theories_raw.splitlines()
                     if line.strip()}
    repls_raw = strip_ml_noise(ml_expect(repl.send('Ir.repls ()')))
    active_repls, busy_repls = parse_repls_output(repls_raw)
    return loaded_theories, active_repls, busy_repls


def load_isabelle_symbols(repl: ReplClient) -> dict[str, str]:
    """Load Isabelle symbol table (\\<name> -> Unicode) via the ML process.

    Reads $ISABELLE_HOME/etc/symbols as raw bytes through ML and hex-
    encodes the result, bypassing I/R's symbol auto-correction which
    would otherwise convert \\<name> sequences to Unicode in the output.
    Works regardless of whether Isabelle runs locally or on a remote
    host (e.g. via I/P proxy).
    """
    result = repl.send(
        'let val path = getenv "ISABELLE_HOME" ^ "/etc/symbols"\n'
        '    val is = BinIO.openIn path\n'
        '    val bytes = BinIO.inputAll is\n'
        '    val _ = BinIO.closeIn is\n'
        '    fun hex b = StringCvt.padLeft #"0" 2 '
        '(Int.fmt StringCvt.HEX (Word8.toInt b))\n'
        'in writeln (String.concat '
        '(Word8Vector.foldr (fn (b, acc) => hex b :: acc) [] bytes)) end',
        timeout=30)
    if isinstance(result, MlError):
        return {}
    payload = strip_ml_noise(result.output).strip()
    if not payload:
        return {}
    try:
        raw = bytes.fromhex(payload)
    except ValueError:
        return {}
    text = raw.decode('iso-8859-1')
    mapping: dict[str, str] = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) >= 3 and parts[1] == "code:":
            try:
                mapping[parts[0]] = chr(int(parts[2], 16))
            except ValueError:
                continue
    return mapping


_SYMBOL_PAT = re.compile(r'\\<[a-zA-Z_]+>')


def symbols_to_unicode(text: str, symbols: dict[str, str]) -> str:
    """Convert \\<name> sequences to Unicode using the symbol table."""
    if not symbols or "\\" not in text:
        return text
    return _SYMBOL_PAT.sub(lambda m: symbols.get(m.group(), m.group()), text)


# --- Execution locks ---

@dataclass
class ExecutionLocks:
    """Locks for parallel execution of dep plans."""
    load_theory: threading.Lock = field(default_factory=threading.Lock)


# --- Transient check context ---

@dataclass
class CheckContext:
    """Holds transient state for one check() invocation."""
    repl: ReplClient
    loaded_theories: set[str] = field(default_factory=set)
    active_repls: dict[str, ReplInfo] = field(default_factory=dict)
    busy_repls: dict[str, BusyReplInfo] = field(default_factory=dict)
    sessions: dict[str, SessionInfo] = field(default_factory=dict)
    files: dict[QualifiedTheory, FileEntry] = field(default_factory=dict)
    path_index: dict[str, QualifiedTheory] = field(default_factory=dict)
    build_order: list[ResolvedImport] = field(default_factory=list)
    dep_graph: DepGraph = field(default_factory=dict)
    theory_ref: dict[ResolvedImport, str] = field(default_factory=dict)
    markers: dict[str, 'HashMarker'] = field(default_factory=dict)
    parse_errors: list[dict] = field(default_factory=list)
    diamond_strategy: DiamondStrategy = DiamondStrategy.HEURISTIC
    verbose: int = 0
    isabelle_symbols: dict[str, str] = field(default_factory=dict)
    locks: ExecutionLocks = field(default_factory=ExecutionLocks)
    pool_size: int = 1
    timeout: int = 0         # per-REPL step timeout (0 = use I/R default)
    always_stepwise: bool = False  # never use Ir.load_theory for file deps
    is_target: bool = False  # set per-job for logging control
    display: 'ProgressDisplay | None' = None
    job_id: str = ""       # short theory name for progress display
    job_begun: bool = False # True after first log_step registered with display

    def parents_for(self, ri) -> list[str]:
        """Collect theory refs for ri's direct imports, preserving order."""
        return [self.theory_ref[dep_ri]
                for dep_ri in self.dep_graph.get(ri, [])
                if dep_ri in self.theory_ref]

    def read_marker(self, qt: QualifiedTheory) -> 'HashMarker | None':
        """Read the marker for a theory."""
        return self.markers.get(qt.name)

    def read_stepped_marker(self, qt: QualifiedTheory) -> 'SteppedMarker | None':
        """Read the stepped marker if a stepped REPL exists, or None."""
        marker = self.read_marker(qt)
        return marker if isinstance(marker, SteppedMarker) else None

    def remove_repl(self, qt: QualifiedTheory) -> None:
        """Remove a REPL if it exists."""
        if qt.repl_name in self.active_repls:
            ml_expect(self.repl.send(f'Ir.remove "{ml_escape(qt.repl_name)}"'))
            del self.active_repls[qt.repl_name]


_PIN_REF_RE = re.compile(r'pin@([\w.]+)')


def pin_deps_from_origin(origin: str) -> list[str]:
    """Extract pin@NAME references from a REPL origin string."""
    return _PIN_REF_RE.findall(origin)


def removal_order(origins: dict[str, str], names: set[str]) -> list[str]:
    """Compute removal order for a set of REPL names: dependents first.

    Builds a dep graph from origin strings (pin@X → depends on X).
    Returns names ordered so each REPL comes before its pin-parents.
    origins: name → origin string for all known REPLs (active + busy).
    """
    graph: dict[str, set[str]] = {}
    for name in names:
        origin = origins.get(name, "")
        parents = set(pin_deps_from_origin(origin)) & names
        graph[name] = parents
    return list(reversed(topological_sort(graph)))


def remove_repls(repl: ReplClient, names: list[str]) -> None:
    """Remove REPLs in the given order (dependents before parents)."""
    for name in names:
        ml_expect(repl.send(f'Ir.remove "{ml_escape(name)}"'))


def expand_with_pin_dependents(origins: dict[str, str],
                               names: set[str]) -> set[str]:
    """Expand removal set with all REPLs transitively depending on names.

    Builds a reverse pin-dep graph (parent → children that reference it),
    then BFS from names to find all transitive dependents. O(V+E).
    """
    children: dict[str, set[str]] = defaultdict(set)
    for rn, origin in origins.items():
        for parent in pin_deps_from_origin(origin):
            children[parent].add(rn)

    expanded = set(names)
    queue = deque(names)
    while queue:
        node = queue.popleft()
        for child in children.get(node, ()):
            if child not in expanded:
                expanded.add(child)
                queue.append(child)
    return expanded


def make_job_ctx(ctx: CheckContext, conn: ReplClient) -> CheckContext:
    """Shallow-copy ctx with a per-job REPL connection.

    Mutable dicts (active_repls, markers, loaded_theories) are
    shared references — mutations propagate to the original ctx.
    """
    job_ctx = copy.copy(ctx)
    job_ctx.repl = conn
    return job_ctx


# --- Progress display ---

class ProgressDisplay:
    """Multi-line progress display for concurrent jobs.

    Dynamically sized: the block grows when jobs start stepping and
    shrinks when they finish. Each active job gets a line showing
    a progress bar with the theory name. Status messages print above
    the block. All terminal output is serialized via a lock.
    """

    def __init__(self):
        self._lock = threading.Lock()
        self._active = False
        self._jobs: list[tuple[str, str]] = []  # (job_id, text)

    def start(self) -> None:
        """Activate the display. No lines reserved upfront."""
        with self._lock:
            if sys.stderr.isatty():
                self._active = True

    def begin_job(self, job_id: str) -> None:
        """Register a new active job (grows the block by one line)."""
        with self._lock:
            if not self._active:
                return
            self._jobs.append((job_id, ""))
            print("", file=sys.stderr)

    def update_job(self, job_id: str, text: str) -> None:
        """Update the progress text for an active job."""
        with self._lock:
            if not self._active:
                return
            for i, (jid, _) in enumerate(self._jobs):
                if jid == job_id:
                    self._jobs[i] = (job_id, text)
                    up = len(self._jobs) - i
                    print(f"\033[{up}A\033[2K  {text}\033[{up}B\r",
                          end="", file=sys.stderr, flush=True)
                    return

    def end_job(self, job_id: str) -> None:
        """Remove a completed job (shrinks the block by one line)."""
        with self._lock:
            if not self._active:
                return
            n = len(self._jobs)
            self._jobs = [(jid, t) for jid, t in self._jobs
                          if jid != job_id]
            if n > 0:
                print(f"\033[{n}A\033[J", end="", file=sys.stderr)
                for _, text in self._jobs:
                    print(f"  {text}", file=sys.stderr)

    def message(self, text: str) -> None:
        """Print a status message above the progress block."""
        with self._lock:
            if not self._active:
                print(text, file=sys.stderr)
                return
            n = len(self._jobs)
            if n > 0:
                print(f"\033[{n}A\033[J{text}", file=sys.stderr)
                for _, line in self._jobs:
                    print(f"  {line}", file=sys.stderr)
            else:
                print(text, file=sys.stderr)

    def stop(self) -> None:
        """Finalize the progress block."""
        with self._lock:
            if self._active:
                self._active = False
                n = len(self._jobs)
                if n > 0:
                    print(f"\033[{n}A\033[J",
                          end="", file=sys.stderr, flush=True)
                self._jobs.clear()


# --- Verbose logging ---

_USE_COLOR = sys.stderr.isatty()
_DIM = "\033[2m" if _USE_COLOR else ""
_GREEN = "\033[32m" if _USE_COLOR else ""
_RST = "\033[0m" if _USE_COLOR else ""


def log(ctx: CheckContext, msg: str) -> None:
    """Level 1 verbose message to stderr."""
    if ctx.verbose >= 1:
        if ctx.display:
            ctx.display.message(msg)
        else:
            print(msg, file=sys.stderr)


def log2(ctx: CheckContext, msg: str) -> None:
    """Level 2 verbose message to stderr."""
    if ctx.verbose >= 2:
        if ctx.display:
            ctx.display.message(msg)
        else:
            print(msg, file=sys.stderr)


def format_bar(i: int, total: int, name: str, cmd_text: str) -> str:
    """Format a progress bar string, optionally with theory name."""
    width = 20
    filled = width * (i + 1) // total if total > 0 else width
    bar = "=" * filled + " " * (width - filled)
    cmd = cmd_text.strip().replace("\n", " ")[:50]
    name_part = f"{name}  " if name else ""
    return f"{_DIM}[{bar}] {i+1}/{total}  {name_part}{cmd}{_RST}"


def log_step(ctx: CheckContext, i: int, total: int, cmd_text: str) -> None:
    """Overwrite a progress bar on stderr (tty only)."""
    if ctx.verbose < 1 or not sys.stderr.isatty():
        return
    if ctx.display and not ctx.is_target:
        if not ctx.job_begun:
            ctx.display.begin_job(ctx.job_id)
            ctx.job_begun = True
        ctx.display.update_job(
            ctx.job_id, format_bar(i, total, ctx.job_id, cmd_text))
        return
    # Single-connection mode or target: direct terminal write
    print(f"\r\033[2K  {format_bar(i, total, '', cmd_text)}",
          end="", file=sys.stderr, flush=True)


def log_step_done(ctx: CheckContext) -> None:
    """Clear the progress bar line."""
    if ctx.verbose >= 1 and sys.stderr.isatty():
        if ctx.display and not ctx.is_target:
            if ctx.job_begun:
                ctx.display.end_job(ctx.job_id)
                ctx.job_begun = False
            return
        print("\r\033[2K", end="", file=sys.stderr, flush=True)


def log_progress(ctx: CheckContext, i: int, total: int, msg: str) -> None:
    """Overwrite a progress message on stderr (tty only)."""
    if ctx.verbose < 1 or not sys.stderr.isatty():
        return
    print(f"\r\033[2K  {_DIM}{i+1}/{total}  {msg}{_RST}",
          end="", file=sys.stderr, flush=True)


def log_progress_done(ctx: CheckContext) -> None:
    """Clear the progress line."""
    if ctx.verbose >= 1 and sys.stderr.isatty():
        print("\r\033[2K", end="", file=sys.stderr, flush=True)


# --- REPL interaction ---

def pin_repl(ctx: CheckContext, repl_name: str) -> None:
    """Pin a REPL so it can be referenced as a parent via pin@name."""
    ml_expect(ctx.repl.send(f'Ir.pin "{ml_escape(repl_name)}"'))


def ensure_timeout(ctx: CheckContext, repl_name: str) -> None:
    """Set per-REPL timeout if configured."""
    if ctx.timeout > 0:
        ctx.repl.send(
            f'Ir.timeout "{ml_escape(repl_name)}" {ctx.timeout}')


def step(ctx: CheckContext, repl_name: str, text: str) -> tuple[bool, str]:
    """Step a single Isar command. Returns (success, output)."""
    repl_id = ml_escape(repl_name)
    escaped = ml_escape(text)
    result = ctx.repl.send(f'Ir.step "{repl_id}" "{escaped}"')
    if isinstance(result, MlOk):
        ctx.active_repls[repl_name].step_count += 1
        return True, result.output
    return False, strip_ml_noise(result.error)


def truncate_to(ctx: CheckContext, repl_name: str, step_idx: int) -> None:
    """Truncate REPL. step_idx < 0 clears all steps."""
    repl_id = ml_escape(repl_name)
    info = ctx.active_repls[repl_name]
    if step_idx < 0:
        n = info.step_count
        if n > 0:
            ml_expect(ctx.repl.send(f'Ir.truncate "{repl_id}" ~{n}'))
            info.step_count = 0
    else:
        ml_expect(ctx.repl.send(f'Ir.truncate "{repl_id}" {step_idx}'))
        info.step_count = step_idx + 1


def ensure_snippets_loaded(repl: ReplClient) -> None:
    """Load I/C ML snippets into I/R if not already loaded."""
    result = repl.send('ic_snippets_loaded')
    if isinstance(result, MlOk):
        return
    snippets_path = os.path.join(os.path.dirname(__file__), "ic_snippets.ML")
    with open(snippets_path) as f:
        ml_code = f.read()
    # The TCP handler evaluates one ;-terminated statement at a time,
    # sending <<DONE>> after each. Split into individual statements
    # and send each via send() (which appends the ;).
    for stmt in ml_code.split(";"):
        if stmt.strip():
            ml_expect(repl.send(stmt))
    ml_expect(repl.send('val ic_snippets_loaded = ()'))


def parse_spans(repl: ReplClient, repl_name: str, body: str) -> list[int]:
    """Get 1-based command offsets by stepping ML_val in the REPL.

    Steps ML_val calling ic_parse_spans with @{theory} into the REPL,
    reads offsets from output, then truncates. Uses ML_val (not ML)
    because ML_val works in any context including proof mode.

    The body text is passed as a cartouche string literal inside the
    ML_val, avoiding a global ML variable (which would race under
    concurrent connections). Isabelle's cartouche nesting handles
    \\<open>/\\<close> inside the body correctly.
    """
    repl_id = ml_escape(repl_name)
    # Body is passed as an ML string literal inside ML_val, which is
    # itself inside an Ir.step ML string. Two escaping layers:
    #   1. Inner: body → ML string for ic_parse_spans ("..." in ML_val)
    #   2. Outer: whole Isar command → ML string for Ir.step's 2nd arg
    # The inner escape uses \092 (ML decimal escape for backslash)
    # instead of \\ to avoid \\< patterns that I/R's auto-correct
    # would mangle across the two layers.
    inner = (body
             .replace('\\', '\\092')
             .replace('"', '\\"')
             .replace('\n', '\\n')
             .replace('\t', '\\t')
             .replace('\r', ''))
    cmd = f'ML_val \\<open>ic_parse_spans @{{theory}} "{inner}"\\<close>'
    result = repl.send(f'Ir.step "{repl_id}" "{ml_escape(cmd)}"')
    if isinstance(result, MlError):
        # Outer_Syntax.parse_text turns unparseable text into <malformed>
        # transitions rather than raising, so this should not happen in
        # practice. Guard against it anyway: no step was added on failure,
        # so we must NOT truncate (that would remove a real step).
        raise RuntimeError(f"parse_spans failed: {result.error}")
    # Step succeeded — remove the temporary ML_val step.
    repl.send(f'Ir.truncate "{repl_id}" ~1')
    offsets = []
    for line in result.output.splitlines():
        line = line.strip()
        if line.isdigit():
            offsets.append(int(line))
    return offsets


def ensure_repl(ctx: CheckContext, parent_theories: list[str],
                 repl_name: str,
                 segment_spec: str | None = None) -> str | None:
    """Ensure a named REPL exists with the given parent theories.

    If the REPL already exists, return immediately.
    If it doesn't exist, create it. Returns error message or None.
    parent_theories order is preserved (matches theory header import order).

    If segment_spec is given (e.g. "session.Theory:42"), init from that
    recorded segment instead of from theories.
    """
    theories = parent_theories or ["Main"]

    if repl_name in ctx.active_repls:
        return None

    # Create REPL
    if segment_spec:
        result = ctx.repl.send(
            f'Ir.init "{ml_escape(repl_name)}" '
            f'["{ml_escape(segment_spec)}"]')
        origin = f"segment {segment_spec}"
    else:
        theory_list = ", ".join(f'"{t}"' for t in theories)
        result = ctx.repl.send(
            f'Ir.init "{ml_escape(repl_name)}" [{theory_list}]')
        origin = "theory " + "+".join(theories)
    if isinstance(result, MlError):
        what = segment_spec or list(theories)
        return f"Ir.init failed with {what}: {result.error}"
    if "Created REPL" not in result.output:
        what = segment_spec or list(theories)
        return f"Ir.init failed with {what}: {result.output}"
    ctx.active_repls[repl_name] = ReplInfo(
        name=repl_name, step_count=0, stale_count=0,
        origin=origin, is_current=True)
    return None


# --- Session scanning ---

def ensure_sessions_scanned(ctx: CheckContext, dirs: list[str],
                             target_path: str) -> dict | None:
    """Discover sessions from dirs and load the target's session + deps."""
    try:
        ctx.sessions = discover_sessions(dirs)
    except (ValueError, IOError) as e:
        return {"status": "error", "error": str(e)}

    # Find which session contains the target file
    target_path = os.path.realpath(target_path)
    target_session = None
    for sname, sinfo in ctx.sessions.items():
        if target_path in sinfo.theories.values():
            target_session = sname
            break
        # Also check unlisted files in session/extra directories
        for scan_dir in [sinfo.directory] + sinfo.directories:
            if target_path.startswith(os.path.realpath(scan_dir) + os.sep):
                target_session = sname
                break
        if target_session:
            break

    if not target_session:
        return {"status": "error",
                "error": f"File not in any session: {target_path}"}

    # Compute transitive session dependencies
    needed = transitive_session_deps(ctx, target_session)
    # Always include the target's session (even if all its theories are in
    # the heap) so the target file is loaded into ctx.files.
    if target_session not in needed:
        needed.append(target_session)

    # Load .thy files for needed sessions
    err = load_session_files(ctx, needed)
    log(ctx, f"  {_DIM}{len(ctx.sessions)} sessions, "
              f"{len(ctx.files)} theories{_RST}")
    return err


def transitive_session_deps(ctx: CheckContext,
                             session_name: str) -> list[str]:
    """Return session names transitively needed, in dependency order.

    Skips sessions whose theories are already in the heap.
    """
    result: list[str] = []
    visited: set[str] = set()

    def visit(name: str) -> None:
        if name in visited or name not in ctx.sessions:
            return
        visited.add(name)
        session = ctx.sessions[name]
        for dep in session.session_deps:
            visit(dep)
        result.append(name)

    visit(session_name)
    return result


def load_session_files(ctx: CheckContext,
                        session_names: list[str]) -> dict | None:
    """Load .thy files for the given sessions into ctx. Returns error or None."""
    files: dict[QualifiedTheory, FileEntry] = {}

    for sname in session_names:
        session = ctx.sessions[sname]

        # Collect all .thy files: ROOT-listed theories + unlisted files
        # in the session directory. ROOT-listed entries take priority.
        thy_paths: dict[str, str] = dict(session.theories)
        scan_dirs = [session.directory] + session.directories
        for scan_dir in scan_dirs:
            if not os.path.isdir(scan_dir):
                continue
            for fname in os.listdir(scan_dir):
                if fname.endswith('.thy'):
                    thy_name = fname.removesuffix('.thy')
                    if thy_name not in thy_paths:
                        thy_paths[thy_name] = os.path.join(
                            scan_dir, fname)

        for thy_name, thy_path in thy_paths.items():
            if not os.path.isfile(thy_path):
                continue
            qt = QualifiedTheory(f"{sname}.{thy_name}")
            if qt in files:
                return {"status": "error",
                        "error": f"Duplicate theory '{qt}' in sessions "
                                 f"'{files[qt].session_name}' and '{sname}'"}
            try:
                with open(thy_path, 'r') as f:
                    text = f.read()
                header = parse_theory_file(text)
                files[qt] = FileEntry(
                    path=thy_path,
                    header=header,
                    session_name=sname,
                    content_hash=file_content_hash(text),
                    total_lines=len(text.splitlines()),
                )
                if not header.body_ended:
                    ctx.parse_errors.append({
                        "path": thy_path,
                        "error": "theory has no terminating 'end' line",
                    })
            except (ValueError, IOError) as e:
                ctx.parse_errors.append({"path": thy_path, "error": str(e)})

    ctx.files = files
    ctx.path_index = {entry.path: qt for qt, entry in files.items()}

    try:
        ctx.build_order, ctx.dep_graph = resolve_dependencies(
            ctx.files, ctx.loaded_theories)
    except ValueError as e:
        return {"status": "error", "error": str(e)}

    return None


# --- Dependency helpers ---

def transitive_deps_in_build_order(ctx: CheckContext,
                                    target: QualifiedTheory
                                    ) -> list[ResolvedImport]:
    """Return transitive deps of target (including target), in build order."""
    needed: set[ResolvedImport] = set()

    def collect(ri: ResolvedImport) -> None:
        if ri in needed:
            return
        needed.add(ri)
        if isinstance(ri, FileImport):
            entry = ctx.files.get(ri.qualified)
            if entry:
                for imp in entry.header.imports:
                    dep_ri = resolve_import(
                        imp, ri.qualified.session_name,
                        ctx.files, ctx.loaded_theories)
                    collect(dep_ri)

    target_ri = FileImport(target)
    collect(target_ri)
    return [ri for ri in ctx.build_order if ri in needed]


def theory_name_from_repl(repl_name: str) -> QualifiedTheory:
    """Extract qualified theory name from REPL name: ic.S.A -> QualifiedTheory('S.A')."""
    return QualifiedTheory(repl_name.removeprefix("ic."))


# --- State recovery from I/R ---

# Hash marker types stored in the ML-side symtab (ic_mgmt_tab).
#
# Three marker formats:
#   Stepped: ic:hash=HASH:cmds=N[:seg=SPEC]  — REPL that stepped file commands
#   Loaded:  ic:loaded:hash=HASH              — tracks a loaded theory's hash
#   HeapVerified: ic:heap:hash=HASH           — caches heap-vs-disk comparison

@dataclass
class SteppedMarker:
    """Marker for a REPL that stepped the file's commands."""
    content_hash: str
    cmd_count: int
    segment_spec: str | None = None
    dep_hashes: dict[str, str] = field(default_factory=dict)


@dataclass
class LoadedMarker:
    """Marker for a loaded theory's hash and dependency hashes."""
    content_hash: str
    dep_hashes: dict[str, str] = field(default_factory=dict)


@dataclass
class HeapVerifiedMarker:
    """Marker for a REPL that verified a heap theory matches disk."""
    content_hash: str


HashMarker = SteppedMarker | LoadedMarker | HeapVerifiedMarker

_STEPPED_PAT = re.compile(
    r'ic:hash=([a-f0-9]+):cmds=(\d+):deps=\[([^\]]*)\](?::seg=([^›\s]+))?')
_LOADED_PAT = re.compile(
    r'ic:loaded:hash=([a-f0-9]+):deps=\[([^\]]*)\]')
_HEAP_VERIFIED_PAT = re.compile(
    r'ic:heap:hash=([a-f0-9]+)')


def serialize_marker(marker: HashMarker) -> str:
    """Convert a marker to its wire string (no text wrapper)."""
    if isinstance(marker, SteppedMarker):
        deps = ','.join(f'{k}={v}' for k, v in sorted(marker.dep_hashes.items()))
        base = f'ic:hash={marker.content_hash}:cmds={marker.cmd_count}:deps=[{deps}]'
        if marker.segment_spec:
            base += f':seg={marker.segment_spec}'
        return base
    elif isinstance(marker, LoadedMarker):
        deps = ','.join(f'{k}={v}' for k, v in sorted(marker.dep_hashes.items()))
        return f'ic:loaded:hash={marker.content_hash}:deps=[{deps}]'
    elif isinstance(marker, HeapVerifiedMarker):
        return f'ic:heap:hash={marker.content_hash}'
    raise TypeError(f"Unknown marker type: {type(marker)}")


def marker_hash(marker: HashMarker) -> str:
    """Hash a marker for dep staleness tracking."""
    return file_content_hash(serialize_marker(marker))


def parse_marker(text: str) -> HashMarker | None:
    """Parse a marker wire string. Returns HashMarker or None."""
    m = _HEAP_VERIFIED_PAT.search(text)
    if m:
        return HeapVerifiedMarker(m.group(1))
    m = _LOADED_PAT.search(text)
    if m:
        dep_hashes = {}
        deps_str = m.group(2)
        if deps_str:
            for pair in deps_str.split(','):
                if '=' in pair:
                    name, h = pair.rsplit('=', 1)
                    dep_hashes[name] = h
        return LoadedMarker(m.group(1), dep_hashes)
    m = _STEPPED_PAT.search(text)
    if m:
        dep_hashes = {}
        deps_str = m.group(3)
        if deps_str:
            for pair in deps_str.split(','):
                if '=' in pair:
                    name, h = pair.rsplit('=', 1)
                    dep_hashes[name] = h
        return SteppedMarker(m.group(1), int(m.group(2)), m.group(4),
                             dep_hashes)
    return None


def compute_dep_hashes(ctx: 'CheckContext',
                        ri: ResolvedImport) -> dict[str, str]:
    """Compute hashes of dep markers for staleness detection."""
    result: dict[str, str] = {}
    for dep_ri in ctx.dep_graph.get(ri, []):
        if not isinstance(dep_ri, FileImport):
            continue
        dep_name = dep_ri.qualified.name
        dep_marker = ctx.markers.get(dep_name)
        if dep_marker is not None:
            result[dep_name] = marker_hash(dep_marker)
        # else: heap theory without available segments — FileImport
        # but no marker. Excluded from tracking; if a marker appears
        # later, the dep_hash will mismatch → stale (conservative).
    return result


# --- Marker storage ---


def write_marker(ctx: CheckContext, key: str,
                  marker: HashMarker) -> None:
    """Write a keyed marker to the ML-side symtab."""
    ml_expect(ctx.repl.send(
        f'ic_symtab_set "{ml_escape(key)}" '
        f'"{ml_escape(serialize_marker(marker))}"'))
    ctx.markers[key] = marker


def write_markers_batch(ctx: CheckContext,
                         entries: list[tuple[str, HashMarker]]) -> None:
    """Batch-write multiple markers to the symtab."""
    for key, marker in entries:
        write_marker(ctx, key, marker)


def parse_symtab_output(raw: str) -> dict[str, HashMarker]:
    """Parse tab-separated key\\tvalue output from ic_symtab_get_all."""
    result: dict[str, HashMarker] = {}
    for line in raw.splitlines():
        parts = line.split('\t', 1)
        if len(parts) == 2:
            marker = parse_marker(parts[1])
            if marker is not None:
                result[parts[0]] = marker
    return result


def read_all_markers(repl: ReplClient) -> dict[str, HashMarker]:
    """Read all markers from the ML-side symtab."""
    raw = strip_ml_noise(ml_expect(repl.send('ic_symtab_get_all ()')))
    return parse_symtab_output(raw)


def read_marker_from_symtab(repl: ReplClient, key: str) -> HashMarker | None:
    """Read a single marker from the ML-side symtab."""
    result = repl.send(f'ic_symtab_get "{ml_escape(key)}"')
    if isinstance(result, MlOk) and result.output.strip():
        return parse_marker(strip_ml_noise(result.output).strip())
    return None


@dataclass
class MarkerVerification:
    """Result of verifying parent markers against the live symtab."""
    ok: bool
    changed_dep: str | None = None
    expected: str | None = None
    actual: str | None = None

    @staticmethod
    def passed() -> 'MarkerVerification':
        return MarkerVerification(ok=True)

    @staticmethod
    def failed(dep_name: str, expected: str | None,
               actual: str | None) -> 'MarkerVerification':
        return MarkerVerification(ok=False, changed_dep=dep_name,
                                  expected=expected, actual=actual)


def verify_parent_markers(ctx: 'CheckContext',
                           ri: ResolvedImport) -> MarkerVerification:
    """Re-read parent dep markers from symtab and verify unchanged.

    Detects concurrent modifications: if another client rebuilt a dep
    between our classification and our Ir.init, the marker will differ.
    """
    for dep_ri in ctx.dep_graph.get(ri, []):
        if not isinstance(dep_ri, FileImport):
            continue
        dep_name = dep_ri.qualified.name
        expected = ctx.markers.get(dep_name)
        if expected is None:
            continue
        actual = read_marker_from_symtab(ctx.repl, dep_name)
        expected_str = serialize_marker(expected)
        actual_str = serialize_marker(actual) if actual else None
        if actual_str != expected_str:
            return MarkerVerification.failed(dep_name, expected_str, actual_str)
    return MarkerVerification.passed()


# --- REPL body text ---

def read_repl_body_text(repl: ReplClient, repl_name: str) -> str:
    """Read all step text from a REPL (body commands only, no marker)."""
    repl_id = ml_escape(repl_name)
    return strip_ml_noise(ml_expect(repl.send(f'Ir.text "{repl_id}"')))


def recover_old_commands(repl: ReplClient,
                          repl_name: str) -> list[BodyCommand]:
    """Recover body text from REPL and parse into commands."""
    old_text = read_repl_body_text(repl, repl_name)
    if not old_text.strip():
        return []
    offsets = parse_spans(repl, repl_name, old_text)
    return split_body_by_offsets(old_text, offsets, body_start_line=1)


# --- Diamond detection ---

def detect_diamond(ctx: CheckContext, qt: QualifiedTheory) -> set[str]:
    """Detect if loading `qt` via Ir.load_theory would conflict with
    any active REPL. Returns set of conflicting REPL names."""
    entry = ctx.files.get(qt)
    if not entry:
        return set()

    conflicts: set[str] = set()
    visited: set[QualifiedTheory] = set()

    def check_imports(q: QualifiedTheory) -> None:
        if q in visited:
            return
        visited.add(q)
        e = ctx.files.get(q)
        if not e:
            return
        if ctx.read_stepped_marker(q):
            conflicts.add(q.repl_name)
        for imp in e.header.imports:
            imp_qt = qualify_import(imp, q.session_name)
            if imp_qt in ctx.files:
                check_imports(imp_qt)

    for imp in entry.header.imports:
        imp_qt = qualify_import(imp, qt.session_name)
        if imp_qt in ctx.files:
            check_imports(imp_qt)

    return conflicts


# --- Diamond resolution helpers ---


def group_conflicting_repls(all_conflict_repls: set[str],
                             dep_conflicts: dict[str, set[str]],
                             repl_repl_deps: dict[str, set[str]]
                             ) -> list[set[str]]:
    """Group conflicting REPLs into connected components.

    Two REPLs are in the same group if:
    (a) one depends on the other (direct dependency edge), or
    (b) a pending dep imports both (shared reverse-dep bridge).
    """
    adj: dict[str, set[str]] = defaultdict(set)
    for rn, deps in repl_repl_deps.items():
        for d in deps:
            adj[rn].add(d)
            adj[d].add(rn)
    for conflicts in dep_conflicts.values():
        repls = list(conflicts)
        for i in range(len(repls)):
            for j in range(i + 1, len(repls)):
                adj[repls[i]].add(repls[j])
                adj[repls[j]].add(repls[i])

    visited: set[str] = set()
    groups: list[set[str]] = []
    for rn in all_conflict_repls:
        if rn in visited:
            continue
        group: set[str] = set()
        queue = deque([rn])
        while queue:
            curr = queue.popleft()
            if curr in visited:
                continue
            visited.add(curr)
            group.add(curr)
            queue.extend(adj.get(curr, set()) - visited)
        groups.append(group)
    return groups


def expand_with_descendants(all_conflict_repls: set[str],
                            plans: dict[ResolvedImport, DepPlan],
                            deps_in_order: list[ResolvedImport],
                            dep_graph: DepGraph) -> set[str]:
    """Expand conflict set with descendant REPLs.

    A descendant is a non-pending dep with a stepped REPL (SkipPlan with
    has_stepped_repl=True) that transitively imports a conflict REPL.
    These must participate in diamond resolution because RELOAD would
    invalidate their identity ancestry.

    Walks deps_in_order (topological) propagating a 'tainted' set forward.
    Returns the expanded conflict set.
    """
    conflict_qts: set[QualifiedTheory] = {
        theory_name_from_repl(rn) for rn in all_conflict_repls}
    tainted: set[ResolvedImport] = set()
    expanded = set(all_conflict_repls)

    for ri in deps_in_order[:-1]:
        if not isinstance(ri, FileImport):
            continue
        if ri.qualified in conflict_qts:
            tainted.add(ri)
            continue
        direct_deps = dep_graph.get(ri, [])
        if not any(d in tainted for d in direct_deps):
            continue
        tainted.add(ri)
        plan = plans.get(ri)
        if isinstance(plan, SkipPlan) and plan.has_stepped_repl:
            expanded.add(ri.qualified.repl_name)

    return expanded


def choose_group_strategy(group: set[str],
                           repl_to_pending: dict[str, set[str]],
                           ctx: CheckContext
                           ) -> tuple[DiamondStrategy, set[str]]:
    """Choose RELOAD or REPL for a group of conflicting REPLs.

    Returns (strategy, affected_pending_deps).

    TODO: If any of the affected theories that would be stepped via REPL
    have has_keywords in their header, REPL strategy is not viable and
    RELOAD must be forced.
    """
    reload_cost = sum(
        ctx.files[theory_name_from_repl(rn)].header.body.count('\n')
        for rn in group
        if theory_name_from_repl(rn) in ctx.files
    )
    affected_pending: set[ResolvedImport] = set()
    for rn in group:
        affected_pending |= repl_to_pending.get(rn, set())
    repl_cost = sum(
        ctx.files[ri.qualified].header.body.count('\n')
        for ri in affected_pending
        if isinstance(ri, FileImport) and ri.qualified in ctx.files
    )
    if reload_cost <= repl_cost:
        return DiamondStrategy.RELOAD, affected_pending
    else:
        return DiamondStrategy.REPL, affected_pending



# --- Dep resolution planning ---

@dataclass
class ClassifyInput:
    """Per-task data for classify_file_import. Picklable."""
    qt: QualifiedTheory
    entry: FileEntry
    marker: 'HashMarker | None'
    repl_info: ReplInfo | None
    dep_hashes: dict[str, str]     # dep_name → content_hash
    in_loaded_theories: bool
    origin_imports: list[str] | None = None  # qualified imports from REPL origin
    isabelle_symbols: dict[str, str] = field(default_factory=dict)  # set by worker


def classify_loaded_repl(marker: LoadedMarker, disk_hash: str,
                          qt: QualifiedTheory,
                          dep_hashes: dict[str, str]
                          ) -> FileClassification:
    """Classify a file with a loaded marker (own hash + dep hashes)."""
    if marker.content_hash == disk_hash:
        for dep_name, dep_hash in marker.dep_hashes.items():
            if dep_hashes.get(dep_name) != dep_hash:
                return FileNotLoaded(qt)
        return FileLoaded(qt)
    return FileNotLoaded(qt)



def parse_origin_specs(origin: str) -> list[str] | None:
    """Split origin into Ir.init specs. None for segment origins."""
    clean = origin.removesuffix(", pinned [stale]").removesuffix(", pinned")
    clean = clean.removeprefix("theory ")
    # Segment origins have format "Theory:idx" (colon without pin@ prefix)
    if ":" in clean and not clean.startswith("pin@"):
        return None
    return [s.strip() for s in clean.split("+")]


def spec_to_import(spec: str) -> str:
    """Strip Ir.init spec format to a bare import name.

    "pin@ic.S.A" → "S.A"
    "Main" → "Main"
    """
    if spec.startswith("pin@ic."):
        return spec.removeprefix("pin@ic.")
    return spec


def current_import_spec(qt: QualifiedTheory,
                        markers: dict[str, 'HashMarker'],
                        active_repls: dict[str, 'ReplInfo']) -> str:
    """What Ir.init spec would currently be used for this dep as a parent.

    Same decision as SkipPlan.import_name(): pin@repl_name if the dep
    has a stepped REPL, qualified theory name otherwise.
    """
    if (isinstance(markers.get(qt.name), SteppedMarker)
            and qt.repl_name in active_repls):
        return f"pin@{qt.repl_name}"
    return qt.name


def build_origin_imports(repl_info: ReplInfo | None,
                         session: str) -> list[str] | None:
    """Qualify the REPL's origin specs for import comparison.

    Returns None if no REPL or segment origin (no comparison possible).
    """
    if repl_info is None:
        return None
    specs = parse_origin_specs(repl_info.origin)
    if specs is None:
        return None
    return [qualify_import(spec_to_import(s), session).name for s in specs]


def classify_stepped_repl(repl: ReplClient, marker: SteppedMarker,
                           disk_hash: str, inp: ClassifyInput
                           ) -> FileClassification:
    """Classify a file with a stepped REPL.

    - Hash match → ReplClean or ReplCachedError
    - Hash mismatch → ReplChanged (computes diff for incremental rebuild)
    """
    qt, entry = inp.qt, inp.entry
    if marker.content_hash == disk_hash:
        # Check dep hashes — if any dep changed, REPL is stale
        for dep_name, dep_hash in marker.dep_hashes.items():
            if inp.dep_hashes.get(dep_name) != dep_hash:
                return NoRepl(qt)
        # File and deps unchanged — check if previous check completed
        body_steps = body_step_count(inp.repl_info)
        if body_steps >= marker.cmd_count:
            return ReplClean(qt)
        # Cached error: parse commands for recovery
        all_cmds = parse_body_commands(repl, qt.repl_name, entry.header)
        if marker.segment_spec and marker.cmd_count > 0:
            cmds = all_cmds[-marker.cmd_count:]
        else:
            cmds = all_cmds
        if len(cmds) == 0:
            first_changed_line = entry.header.body_start_line
        elif body_steps < len(cmds):
            first_changed_line = cmds[body_steps].file_line
        else:
            first_changed_line = cmds[-1].file_line
        line_info = LineInfo(first_changed_line, entry.total_lines)
        return ReplCachedError(qt, commands=cmds, body_steps=body_steps,
                               line_info=line_info)
    else:
        # File changed — check if imports changed (needs full rebuild).
        if inp.origin_imports is not None:
            current = [qualify_import(imp, entry.session_name).name
                       for imp in entry.header.imports]
            if inp.origin_imports != current:
                return NoRepl(qt)

        # Imports unchanged — compute diff for incremental rebuild.
        if marker.segment_spec:
            return classify_segment_repl_changed(
                repl, marker, inp, disk_hash)

        # Non-segment REPL: diff full old body vs full new body
        old_commands = recover_old_commands(repl, qt.repl_name)
        new_commands = parse_body_commands(repl, qt.repl_name, entry.header)
        return make_repl_changed(
            inp, old_commands, new_commands,
            disk_hash, entry.header, None)


def diff_commands(old: list[BodyCommand], new: list[BodyCommand],
                   symbols: dict[str, str]) -> int:
    """Find the index of the first differing command."""
    first_diff = len(new)
    old_texts = [c.text.strip() for c in old]
    new_texts = [symbols_to_unicode(c.text.strip(), symbols) for c in new]
    for i in range(min(len(old_texts), len(new_texts))):
        if old_texts[i] != new_texts[i]:
            first_diff = i
            break
    if len(old_texts) != len(new_texts):
        first_diff = min(first_diff, min(len(old_texts), len(new_texts)))
    return first_diff


def make_repl_changed(inp: ClassifyInput,
                        old_commands: list[BodyCommand],
                        new_commands: list[BodyCommand],
                        disk_hash: str, new_header: TheoryHeader,
                        segment_spec: str | None) -> ReplChanged:
    """Build a ReplChanged from aligned old/new command lists."""
    first_diff = diff_commands(old_commands, new_commands,
                                inp.isabelle_symbols)
    restep = len(new_commands) - first_diff
    if len(new_commands) == 0:
        first_changed_line = new_header.body_start_line
    elif first_diff < len(new_commands):
        first_changed_line = new_commands[first_diff].file_line
    else:
        first_changed_line = new_commands[-1].file_line
    line_info = LineInfo(first_changed_line, inp.entry.total_lines)
    change = ChangeInfo(old_commands, new_commands, first_diff, line_info)
    body_steps = body_step_count(inp.repl_info)
    sr = (0, body_steps - 1) if body_steps > 0 else (0, 0)
    return ReplChanged(
        inp.qt, change, restep,
        step_range=sr, new_header=new_header,
        content_hash=disk_hash, segment_spec=segment_spec)


def classify_segment_repl_changed(
        repl: ReplClient, marker: SteppedMarker,
        inp: ClassifyInput, disk_hash: str,
) -> FileClassification:
    """Classify a changed file whose REPL was created via segment init.

    Re-run segment comparison on the new file to find the boundary:
    - Same segment point → diff old tail vs new tail (aligned)
    - Different segment point → HeapStale (re-init from new point)
    """
    qt = inp.qt
    diff = compare_heap_segments(repl, inp)
    assert diff is not None, (
        f"compare_heap_segments returned None for {qt.name} which "
        f"previously had segment_spec={marker.segment_spec}")

    if diff.segment_spec == marker.segment_spec:
        # Same segment init point — diff the tails
        old_tail = recover_old_commands(repl, qt.repl_name)
        return make_repl_changed(
            inp, old_tail, diff.tail,
            disk_hash, inp.entry.header, marker.segment_spec)

    # Segment point shifted — re-init from the new point
    return HeapStale(qt, diff)


def classify_repl_file(repl: ReplClient, inp: ClassifyInput
                        ) -> FileClassification:
    """Classify a file that has an active I/C REPL.

    Dispatches to classify_loaded_repl or classify_stepped_repl
    based on the marker type. Error reading REPL → NoRepl.
    """
    qt, marker = inp.qt, inp.marker
    try:
        if marker is None:
            return NoRepl(qt)
        disk_hash = inp.entry.content_hash

        if isinstance(marker, LoadedMarker):
            return classify_loaded_repl(
                marker, disk_hash, qt, inp.dep_hashes)
        elif isinstance(marker, SteppedMarker):
            return classify_stepped_repl(
                repl, marker, disk_hash, inp)
        else:
            raise TypeError(f"Unknown marker type: {type(marker)}")
    except (ValueError, IOError):
        return NoRepl(qt)


def classify_file_import(repl: ReplClient, inp: ClassifyInput
                          ) -> tuple[FileClassification, HashMarker | None]:
    """Classify a managed file import based on its local state.

    Returns (classification, optional_marker). The marker, if present,
    should be written to the symtab by the caller.
    """
    qt, entry, marker = inp.qt, inp.entry, inp.marker

    # Non-heap theory with existing REPL
    if marker is not None and not inp.in_loaded_theories:
        if isinstance(marker, SteppedMarker) and inp.repl_info is None:
            # Should be unreachable: remove_stale_repls clears the
            # paired marker whenever it removes the REPL. Warn loudly
            # so any future leak is reported, then clear the orphan
            # symtab entry and treat as if absent.
            print(
                f"I/C: orphan SteppedMarker for {qt.name} (no live "
                f"REPL {qt.repl_name}). This is a bug — please "
                f"report. Clearing the stale marker.",
                file=sys.stderr, flush=True)
            ml_expect(repl.send(
                f'ic_symtab_delete "{ml_escape(qt.name)}"'))
            return NoRepl(qt), None
        return classify_repl_file(repl, inp), None

    # Non-heap, no REPL
    if not inp.in_loaded_theories:
        return NoRepl(qt), None

    # Heap theory — check freshness
    disk_hash = entry.content_hash

    # Fast path: check cached HeapVerifiedMarker hash
    if marker is not None:
        if isinstance(marker, HeapVerifiedMarker):
            if marker.content_hash == disk_hash:
                return InHeap(qt, HeapFreshness.VERIFIED), None
            # Hash mismatch — fall through to segment comparison
        else:
            # Stepped/Loaded REPL — use existing classify logic
            result = classify_repl_file(repl, inp)
            if isinstance(result, (ReplClean, ReplCachedError)):
                result.in_heap = True
            elif isinstance(result, NoRepl):
                # Dep hash mismatch for a heap theory — can't use
                # Ir.load_theory, need CheckPlan via HeapStaleDep
                result = HeapStaleDep(qt)
            return result, None

    # Slow path: full segment comparison
    diff = compare_heap_segments(repl, inp)
    if diff is not None and diff.tail:
        return HeapStale(qt, diff), None
    if diff is not None:
        # Segments match — cache hash for next time
        return InHeap(qt, HeapFreshness.VERIFIED), HeapVerifiedMarker(disk_hash)
    return InHeap(qt, HeapFreshness.NO_SEGMENTS), None


# --- Parallel classify worker (ProcessPoolExecutor) ---

_classify_conn: ReplClient | None = None
_classify_symbols: dict[str, str] = {}


def init_classify_worker(host: str, port: int, token: str | None,
                           isabelle_symbols: dict[str, str]) -> None:
    """Initialize a classify worker process with its own I/R connection."""
    global _classify_conn, _classify_symbols
    _classify_conn = ReplClient(host, port, token)
    _classify_conn.connect()
    _classify_symbols = isabelle_symbols


def classify_one(inp: ClassifyInput
                   ) -> tuple[FileClassification, HashMarker | None]:
    """Classify a single dep in a worker process."""
    inp.isabelle_symbols = _classify_symbols
    return classify_file_import(_classify_conn, inp)


def build_classify_input(ctx: CheckContext,
                           ri: FileImport) -> ClassifyInput:
    """Build a ClassifyInput from the CheckContext for a FileImport."""
    qt = ri.qualified
    entry = ctx.files[qt]
    marker = ctx.markers.get(qt.name)
    repl_info = ctx.active_repls.get(qt.repl_name)
    dep_hashes: dict[str, str] = {}
    if isinstance(marker, (SteppedMarker, LoadedMarker)):
        for dep_name in marker.dep_hashes:
            dep_marker = ctx.markers.get(dep_name)
            if dep_marker is not None:
                dep_hashes[dep_name] = marker_hash(dep_marker)
    return ClassifyInput(
        qt=qt, entry=entry, marker=marker, repl_info=repl_info,
        dep_hashes=dep_hashes,
        in_loaded_theories=(qt.name in ctx.loaded_theories),
        origin_imports=build_origin_imports(repl_info, entry.session_name))


def classify_files(ctx: CheckContext,
                    deps_in_order: list[ResolvedImport],
                    ) -> dict[ResolvedImport, FileClassification]:
    """Classify each dep using a process pool for true CPU parallelism."""
    total = len(deps_in_order)
    with CancellableProcessExecutor(
            max_workers=ctx.pool_size,
            mp_context=multiprocessing.get_context('fork'),
            initializer=init_classify_worker,
            initargs=(ctx.repl.host, ctx.repl.port, ctx.repl.token,
                      ctx.isabelle_symbols)
    ) as executor:
        future_to_ri: dict[Future, ResolvedImport] = {}
        classifications: dict[ResolvedImport, FileClassification] = {}
        for ri in deps_in_order:
            if isinstance(ri, HeapImport):
                classifications[ri] = InHeap(
                    QualifiedTheory(ri.name), HeapFreshness.VERIFIED)
            elif isinstance(ri, ExternalImport):
                classifications[ri] = NoRepl(QualifiedTheory(ri.name))
            else:
                inp = build_classify_input(ctx, ri)
                future_to_ri[executor.submit(classify_one, inp)] = ri
        n_instant = len(classifications)
        pending_markers: list[tuple[str, HashMarker]] = []
        for i, future in enumerate(as_completed(future_to_ri)):
            ri = future_to_ri[future]
            log_progress(ctx, n_instant + i, total,
                         f"classifying {ri_log_name(ri)}")
            classification, marker = future.result()
            classifications[ri] = classification
            if marker:
                assert isinstance(ri, FileImport)
                pending_markers.append((ri.qualified.name, marker))
        log_progress_done(ctx)
        write_markers_batch(ctx, pending_markers)
        return classifications


def rebase_detects_all_changes(
        ri: FileImport,
        imp_ris: list[ResolvedImport],
        active_repls: dict[str, 'ReplInfo'],
        markers: dict[str, 'HashMarker']) -> bool:
    """Whether Ir.rebase can detect all parent changes for this REPL.

    Ir.rebase detects changes via pin@ version tracking. For deps
    referenced by bare name (no stepped REPL), rebase can't see
    reloads. Returns False if any such dep's marker changed since the
    REPL was built.
    """
    m = markers.get(ri.qualified.name)
    if not isinstance(m, SteppedMarker):
        return False
    for dep_ri in imp_ris:
        if not isinstance(dep_ri, FileImport):
            continue
        dep_qt = dep_ri.qualified
        if dep_qt.repl_name in active_repls:
            continue
        dep_marker = markers.get(dep_qt.name)
        current_hash = marker_hash(dep_marker) if dep_marker else None
        recorded_hash = m.dep_hashes.get(dep_qt.name)
        if current_hash != recorded_hash:
            return False
    return True


def has_persistent_repl(ri: ResolvedImport,
                        c: FileClassification,
                        active_repls: dict[str, 'ReplInfo'],
                        markers: dict[str, 'HashMarker'],
                        files: dict[QualifiedTheory, FileEntry]) -> bool:
    """Whether the dep's REPL survives execution (not destroyed)."""
    if not isinstance(ri, FileImport):
        return False
    if isinstance(c, (ReplChanged, ReplCachedError)):
        return True
    if isinstance(c, (NoRepl, HeapStaleDep)):
        rn = ri.qualified.repl_name
        if rn not in active_repls:
            return False
        m = markers.get(ri.qualified.name)
        if not (isinstance(m, SteppedMarker) and m.segment_spec is None):
            return False
        entry = files.get(ri.qualified)
        if not entry:
            return False
        specs = parse_origin_specs(active_repls[rn].origin)
        if specs is None:
            return False
        expected_specs = [current_import_spec(
            qualify_import(imp, entry.session_name),
            markers, active_repls) for imp in entry.header.imports]
        return specs == expected_specs
    return False


def propagate_staleness(classes: dict[ResolvedImport, FileClassification],
                         deps_in_order: list[ResolvedImport],
                         files: dict[QualifiedTheory, FileEntry],
                         markers: dict[str, 'HashMarker'],
                         active_repls: dict[str, 'ReplInfo'],
                         ) -> set[ResolvedImport]:
    """Propagate staleness through deps in build order.

    Mutates `classes` when any import is being rebuilt:
    - ReplClean → NoRepl (or HeapStaleDep for heap theories)
    - FileLoaded → FileNotLoaded
    - InHeap → HeapStaleDep if any file dep is not InHeap (a heap
      theory can only trust its heap version if all deps are also
      using their heap versions)
    Only FileImports participate.

    Returns `rebase_rebuilding`: the set of deps whose REPLs persist
    after rebuild (rebase-compatible). Used by build_plans to decide
    InitStrategy.REBASE vs INIT.
    """
    rebuilding: set[ResolvedImport] = set()
    rebase_rebuilding: set[ResolvedImport] = set()

    def is_rebase_compatible(ri: ResolvedImport,
                             imp_ris: list[ResolvedImport]) -> bool:
        if ri in rebase_rebuilding:
            return True
        if not has_persistent_repl(ri, classes[ri], active_repls, markers, files):
            return False
        if not all(d in rebase_rebuilding for d in imp_ris if d in rebuilding):
            return False
        return rebase_detects_all_changes(ri, imp_ris, active_repls, markers)

    for ri in deps_in_order:
        if not isinstance(ri, FileImport):
            continue
        c = classes[ri]
        entry = files[ri.qualified]
        imp_ris = [FileImport(qualify_import(imp, ri.qualified.session_name))
                   for imp in entry.header.imports]
        if c.is_rebuilding:
            rebuilding.add(ri)
            if is_rebase_compatible(ri, imp_ris):
                rebase_rebuilding.add(ri)
        if isinstance(c, InHeap):
            if any(not isinstance(classes.get(d), InHeap)
                   for d in imp_ris if d in classes):
                classes[ri] = HeapStaleDep(c.qt)
                rebuilding.add(ri)
        elif isinstance(c, HeapStale):
            if any(not isinstance(classes.get(d), InHeap)
                   for d in imp_ris if d in classes):
                classes[ri] = HeapStaleDep(c.qt)
        elif isinstance(c, FileLoaded):
            if any(d in rebuilding for d in imp_ris):
                classes[ri] = FileNotLoaded(c.qt)
                rebuilding.add(ri)
        elif isinstance(c, (ReplClean, ReplCachedError)):
            if any(d in rebuilding for d in imp_ris):
                if c.in_heap:
                    classes[ri] = HeapStaleDep(c.qt)
                else:
                    classes[ri] = NoRepl(c.qt)
                rebuilding.add(ri)
                if is_rebase_compatible(ri, imp_ris):
                    rebase_rebuilding.add(ri)
        elif isinstance(c, ReplChanged):
            if any(d in rebuilding for d in imp_ris):
                classes[ri] = NoRepl(c.qt)

    return rebase_rebuilding


def build_plans(classes: dict[ResolvedImport, FileClassification],
                 deps_in_order: list[ResolvedImport],
                 always_stepwise: bool = False,
                 ) -> dict[ResolvedImport, DepPlan]:
    """Assign a DepPlan to each dep based on its classification.

    The target (last in deps_in_order) always gets a REPL-stepping
    plan — never LoadFilePlan or SkipPlan. CheckPlan init_strategy is
    left as None — filled in by assign_init_strategies after diamond
    resolution.
    """
    plans: dict[ResolvedImport, DepPlan] = {}

    # Dependencies: classification-based mapping
    for ri in deps_in_order[:-1]:
        c = classes[ri]

        if isinstance(c, InHeap):
            plans[ri] = SkipPlan(c.qt, has_stepped_repl=False,
                                 heap_freshness=c.freshness)
        elif isinstance(c, ReplClean):
            plans[ri] = SkipPlan(c.qt, has_stepped_repl=True)
        elif isinstance(c, ReplCachedError):
            plans[ri] = RecoverErrorPlan(c.qt, c.commands, c.body_steps, c.line_info)
        elif isinstance(c, FileLoaded):
            plans[ri] = SkipPlan(c.qt, has_stepped_repl=False)
        elif isinstance(c, ReplChanged):
            plans[ri] = IncrementalPlan(c.qt, c.change_info,
                                          c.step_range, c.segment_spec)
        elif isinstance(c, NoRepl):
            if always_stepwise and isinstance(ri, FileImport):
                plans[ri] = CheckPlan(c.qt)
            else:
                plans[ri] = LoadFilePlan(c.qt)
        elif isinstance(c, HeapStale):
            plans[ri] = SegmentInitPlan(c.qt, c.diff)
        elif isinstance(c, HeapStaleDep):
            plans[ri] = CheckPlan(c.qt)
        elif isinstance(c, FileNotLoaded):
            if always_stepwise and isinstance(ri, FileImport):
                plans[ri] = CheckPlan(c.qt)
            else:
                plans[ri] = LoadFilePlan(c.qt)
        else:
            raise TypeError(f"Unhandled classification: {type(c)}")

    # Target: always checked via REPL
    if deps_in_order:
        target = deps_in_order[-1]
        c = classes[target]

        if isinstance(c, InHeap):
            plans[target] = TargetUnchangedPlan(
                c.qt, source=FromHeap(c.freshness))
        elif isinstance(c, FileLoaded):
            plans[target] = TargetUnchangedPlan(c.qt, source=FromFile())
        elif isinstance(c, ReplClean):
            plans[target] = SkipPlan(c.qt, has_stepped_repl=True)
        elif isinstance(c, ReplCachedError):
            plans[target] = RecoverErrorPlan(c.qt, c.commands, c.body_steps, c.line_info)
        elif isinstance(c, ReplChanged):
            plans[target] = IncrementalPlan(c.qt, c.change_info,
                                             c.step_range, c.segment_spec)
        elif isinstance(c, HeapStale):
            plans[target] = SegmentInitPlan(c.qt, c.diff)
        else:
            plans[target] = CheckPlan(c.qt)

    return plans


def resolve_diamonds(plans: dict[ResolvedImport, DepPlan],
                      classes: dict[ResolvedImport, FileClassification],
                      deps_in_order: list[ResolvedImport],
                      ctx: CheckContext) -> None:
    """Detect diamond conflicts and override plans where needed.

    Mutates `plans`: overrides entries for deps involved in diamond
    conflicts. Only FileImport deps with LoadFilePlan participate —
    diamonds are a conflict between Ir.load_theory and stepped REPLs.
    """
    pending = [ri for ri in deps_in_order[:-1]
               if isinstance(ri, FileImport)
               and isinstance(plans.get(ri), LoadFilePlan)]
    dep_conflicts: dict[ResolvedImport, set[str]] = {}
    repl_to_pending: dict[str, set[ResolvedImport]] = defaultdict(set)
    for ri in pending:
        conflicts = detect_diamond(ctx, ri.qualified)
        if conflicts:
            dep_conflicts[ri] = conflicts
            for rn in conflicts:
                repl_to_pending[rn].add(ri)

    if not dep_conflicts:
        return

    all_conflict_repls: set[str] = set()
    for conflicts in dep_conflicts.values():
        all_conflict_repls |= conflicts

    all_conflict_repls = expand_with_descendants(
        all_conflict_repls, plans, deps_in_order, ctx.dep_graph)

    all_pending = set()
    for ris in repl_to_pending.values():
        all_pending |= ris
    assert all_pending <= set(pending), \
        "repl_to_pending values must be a subset of pending"

    # Build reverse lookup: QualifiedTheory → ResolvedImport key
    qt_to_ri: dict[QualifiedTheory, ResolvedImport] = {}
    for ri in deps_in_order:
        if isinstance(ri, FileImport):
            qt_to_ri[ri.qualified] = ri

    def apply_reload(affected: set[ResolvedImport],
                     group: set[str]) -> None:
        assert affected <= all_pending
        for ri in affected:
            plans[ri] = LoadFilePlan(classes[ri].qt)
        for rn in group:
            rn_qt = theory_name_from_repl(rn)
            rn_ri = qt_to_ri.get(rn_qt)
            if rn_ri and rn_ri in plans:
                plans[rn_ri] = LoadFilePlan(classes[rn_ri].qt)

    def apply_repl(affected: set[ResolvedImport]) -> None:
        assert affected <= all_pending
        for ri in affected:
            c = classes[ri]
            plans[ri] = CheckPlan(c.qt)

    if ctx.diamond_strategy == DiamondStrategy.HEURISTIC:
        repl_repl_deps: dict[str, set[str]] = {}
        for rn in all_conflict_repls:
            inner = detect_diamond(ctx, theory_name_from_repl(rn))
            repl_repl_deps[rn] = inner & all_conflict_repls
        groups = group_conflicting_repls(
            all_conflict_repls, dep_conflicts, repl_repl_deps)
        for group in groups:
            strategy, affected = choose_group_strategy(
                group, dict(repl_to_pending), ctx)
            if strategy == DiamondStrategy.RELOAD:
                apply_reload(affected, group)
            else:
                apply_repl(affected)
    elif ctx.diamond_strategy == DiamondStrategy.RELOAD:
        apply_reload(set(dep_conflicts.keys()), all_conflict_repls)
    else:
        apply_repl(set(dep_conflicts.keys()))


def compute_theory_refs(plans: dict[ResolvedImport, DepPlan],
                         deps_in_order: list[ResolvedImport]
                         ) -> dict[ResolvedImport, str]:
    """For each dep, determine which theory name to use as a parent ref."""
    return {ri: plans[ri].import_name() for ri in deps_in_order}




def assign_init_strategies(plans: dict[ResolvedImport, DepPlan],
                           rebase_rebuilding: set[ResolvedImport],
                           dep_graph: DepGraph,
                           deps_in_order: list[ResolvedImport]) -> None:
    """Fill in CheckPlan init strategies based on the final plan set.

    Walks in build order so parents are resolved before children.
    REBASE if the dep is in rebase_rebuilding and no parent's plan
    removes its REPL. INIT otherwise.
    """
    for ri in deps_in_order:
        plan = plans.get(ri)
        if not isinstance(plan, CheckPlan):
            continue
        if ri not in rebase_rebuilding:
            plan.init_strategy = InitStrategy.INIT
            continue
        parents_ok = all(
            not plans[dep_ri].removes_repl
            for dep_ri in dep_graph.get(ri, [])
            if dep_ri in plans)
        plan.init_strategy = (InitStrategy.REBASE if parents_ok
                              else InitStrategy.INIT)


# --- Segment-based init (record_theories) ---

@dataclass
class SegmentInfo:
    """A segment from Ir.source_map output."""
    seg_idx: int
    keyword: str
    line: int
    offset: int
    file: str


_SEG_MAP_PAT = re.compile(
    r'\s*(\d+)\s+(\S+)\s+(\d+)\s+(\d+)\s+(\S.*)')


def query_source_map(repl: ReplClient,
                      qualified: str) -> list[SegmentInfo] | None:
    """Query Ir.source_map for a theory's recorded segments.

    Returns ordered list of SegmentInfo, or None if segments unavailable
    (theory not in heap, or heap built without record_theories=true).
    """
    result = repl.send(
        f'Ir.source_map "{ml_escape(qualified)}" 0 ~1', timeout=30)
    if isinstance(result, MlError):
        return None
    raw = result.output
    if "No recorded segments" in raw:
        return None
    segments: list[SegmentInfo] = []
    for line in raw.splitlines():
        m = _SEG_MAP_PAT.match(line)
        if m:
            segments.append(SegmentInfo(
                seg_idx=int(m.group(1)),
                keyword=m.group(2),
                line=int(m.group(3)),
                offset=int(m.group(4)),
                file=m.group(5).strip(),
            ))
    if not segments:
        raise ValueError(
            f"source_map for {qualified}: response had no parseable "
            f"segment lines")
    if segments[0].keyword != "theory":
        raise ValueError(
            f"source_map for {qualified}: expected 'theory' header "
            f"segment, got '{segments[0].keyword}'")
    return segments


_HEADER_KEYWORDS = {"theory", "imports", "begin"}


def body_segment_range(segments: list[SegmentInfo]
                        ) -> tuple[int, int] | None:
    """Find first and last body segment indices (between header and end).

    Body segments are those after the header (theory/imports/begin) and
    before the final `end`. Returns (first, last) as indices into the
    segments list, or None if no body segments found.
    """
    end_pos = None
    for i in range(len(segments) - 1, -1, -1):
        if segments[i].keyword == "end":
            end_pos = i
            break
    if end_pos is None:
        return None
    first_body = None
    for i, seg in enumerate(segments):
        if seg.keyword not in _HEADER_KEYWORDS:
            first_body = i
            break
    if first_body is None or first_body >= end_pos:
        return None
    return (first_body, end_pos - 1)


def load_theory(ctx: CheckContext, qualified: str) -> tuple[bool, bool]:
    """Load a theory via Ir.load_theory. Returns (success, rebuilt).

    Serialized via ctx.locks.load_theory: Ir.load_theory mutates
    Isabelle's global theory database, and the subsequent Ir.theories()
    verification must see the result.

    Return value combinations:
      (True, True)   — theory was rebuilt from source and is now loaded.
                        First load, or source file changed since last load.
      (True, False)  — theory was already loaded and source is unchanged.
                        Isabelle reused the cached version.
      (False, True)  — rebuild was attempted but failed (e.g. proof error).
                        Isabelle removes the old version before rebuilding,
                        so a failed rebuild leaves the theory unloaded.
      (False, False) — theory could not be found or loaded at all.
                        Never previously loaded, and the load attempt failed.
    """
    with ctx.locks.load_theory:
        result = ctx.repl.send(
            f'Ir.load_theory "{ml_escape(qualified)}"', timeout=600)
        rebuilt = "Loading theory" in result.output
        # Note: MlOk/MlError does NOT reliably indicate whether our theory loaded.
        # Ir.load_theory (via Thy_Info.use_theories) may reportly fail because of
        # existing build failures in unrelated theories. If so, the
        # ML call raises even though our requested theory loaded fine. We therefore
        # check Ir.theories() for ground truth instead of relying on MlResult.
        # See test_load_theory_leak for a reproducing test.
        out = ml_expect(ctx.repl.send('Ir.theories ()'))
        in_theories = qualified in out or f'  {qualified}' in out
        if in_theories:
            ctx.loaded_theories.add(qualified)
            return True, rebuilt
        return False, rebuilt


# --- Checking ---

def body_step_count(info: ReplInfo | None) -> int:
    """Number of body steps in the REPL."""
    return info.step_count if info else 0


COMMAND_MODIFIERS = {"qualified", "private"}


def parse_body_commands(repl: ReplClient, repl_name: str,
                         header: TheoryHeader) -> list[BodyCommand]:
    """Parse theory body into commands via Ir.parse_spans + split_body_by_offsets."""
    if not header.body.strip():
        return []
    offsets = parse_spans(repl, repl_name, header.body)
    commands = split_body_by_offsets(header.body, offsets, header.body_start_line)
    # Merge command modifiers (qualified, private) with the following command.
    # Ir.parse_spans returns them as separate spans, but Isabelle's theory
    # evaluation treats modifier + command as one segment.
    merged = []
    i = 0
    while i < len(commands):
        if (commands[i].text.strip() in COMMAND_MODIFIERS
                and i + 1 < len(commands)):
            next_cmd = commands[i + 1]
            merged.append(BodyCommand(
                text=commands[i].text + "\n" + next_cmd.text,
                file_line=commands[i].file_line))
            i += 2
        else:
            merged.append(commands[i])
            i += 1
    return merged


def is_comment_only(text: str) -> bool:
    r"""True if the command text contains only comments/markers.

    Strips (* ... *) and \<comment>\<open>...\<close> blocks, returns True
    if nothing remains.
    """
    return not strip_comments(text).strip()


_WS_PAT = re.compile(r'\s+')

_SOURCE_LINE_PAT = re.compile(r'^\s*\d+\s{2}(.*)')


def parse_source_output(raw: str) -> list[str]:
    """Parse Ir.source output into list of command texts (stripped)."""
    result = []
    for line in raw.splitlines():
        m = _SOURCE_LINE_PAT.match(line)
        if m:
            result.append(m.group(1).strip())
    return result



def compare_heap_segments(repl: ReplClient, inp: ClassifyInput
                           ) -> SegmentDiff | None:
    """Compare a heap theory's source against disk using recorded segments.

    Returns SegmentDiff with the init point and tail, or None if
    comparison is not possible (no segments, no body range, etc).
    """
    qt, entry = inp.qt, inp.entry
    segments = query_source_map(repl, qt.name)
    if segments is None:
        return None

    body_range = body_segment_range(segments)
    if not body_range:
        seg_idx = segments[-1].seg_idx
        line_info = LineInfo(segments[-1].line, entry.total_lines)
        return SegmentDiff(f"{qt.name}:{seg_idx}", [], 0,
                           entry.content_hash, line_info)
    body_start, body_end = body_range
    body_seg_count = body_end - body_start + 1

    # Parse commands for comparison. Create a temporary REPL if needed
    # (parse_spans requires a REPL with the right theory context).
    created_temp_repl = False
    if inp.repl_info is None:
        result = repl.send(
            f'Ir.init "{ml_escape(qt.repl_name)}" ["{qt.name}"]')
        if isinstance(result, MlError) or "Created REPL" not in result.output:
            return None
        created_temp_repl = True
    commands = parse_body_commands(repl, qt.repl_name, entry.header)
    if created_temp_repl:
        ml_expect(repl.send(f'Ir.remove "{ml_escape(qt.repl_name)}"'))

    # Filter comment-only commands
    real_commands = [(i, cmd) for i, cmd in enumerate(commands)
                     if not is_comment_only(cmd.text)]

    # Get heap version text via Ir.source
    first_seg = segments[body_start].seg_idx
    last_seg = segments[body_end].seg_idx
    raw = ml_expect(repl.send(
        f'Ir.source "{ml_escape(qt.name)}" {first_seg} {last_seg}',
        timeout=30))
    heap_texts = parse_source_output(raw)
    assert len(heap_texts) == body_seg_count, (
        f"Ir.source for {qt.name} returned {len(heap_texts)} entries "
        f"but body_segment_range expects {body_seg_count}")

    # Compare disk commands against heap segments
    def norm(text: str) -> str:
        return _WS_PAT.sub(' ', symbols_to_unicode(
            text.strip(), inp.isabelle_symbols))

    compare_count = min(body_seg_count, len(real_commands))
    first_diff_idx = None
    for j in range(compare_count):
        cmd_idx, cmd = real_commands[j]
        if norm(cmd.text) != norm(heap_texts[j]):
            first_diff_idx = j
            break

    if first_diff_idx is not None:
        if first_diff_idx == 0:
            if body_start == 0:
                return None
            seg = segments[body_start - 1]
            tail = list(commands)
        else:
            seg = segments[body_start + first_diff_idx - 1]
            first_changed_cmd = real_commands[first_diff_idx][0]
            tail = commands[first_changed_cmd:]
    elif len(real_commands) > body_seg_count:
        seg = segments[body_end]
        first_new_cmd = real_commands[body_seg_count][0]
        tail = commands[first_new_cmd:]
    elif len(real_commands) < body_seg_count:
        seg = segments[body_start + len(real_commands) - 1]
        tail = []
    else:
        seg = segments[body_end]
        tail = []

    first_changed_line = tail[0].file_line if tail else seg.line
    line_info = LineInfo(first_changed_line, entry.total_lines)
    seg_spec = f"{qt.name}:{seg.seg_idx}"
    return SegmentDiff(seg_spec, tail, len(commands),
                       entry.content_hash, line_info)


@dataclass
class SegmentComparison:
    """One heap segment paired with its disk counterpart."""
    seg_idx: int
    heap_text: str
    file_lines: list[str]
    file_line_start: int
    normalized_heap: str
    normalized_disk: str

    @property
    def matches(self) -> bool:
        return self.normalized_heap == self.normalized_disk

    @property
    def first_diff_char(self) -> int | None:
        if self.matches:
            return None
        for k in range(min(len(self.normalized_heap), len(self.normalized_disk))):
            if self.normalized_heap[k] != self.normalized_disk[k]:
                return k
        return min(len(self.normalized_heap), len(self.normalized_disk))


def bootstrap_context(repl: ReplClient, path: str) -> 'CheckContext | dict':
    """Bootstrap a CheckContext for a given path.

    Returns a ready CheckContext or an error dict.
    """
    path = os.path.realpath(path)
    if not os.path.isfile(path):
        return {"status": "error", "error": f"File not found: {path}"}

    ensure_snippets_loaded(repl)
    ml_expect(repl.send('Ir.config (fn {color, show_ignored, full_spans, '
              'show_theory_in_source, auto_replay} => {color=color, '
              'show_ignored=show_ignored, full_spans=true, '
              'show_theory_in_source=show_theory_in_source, '
              'auto_replay=auto_replay})'))

    loaded_theories, active_repls, busy_repls = bootstrap(repl)
    ctx = CheckContext(
        repl=repl,
        loaded_theories=loaded_theories,
        active_repls=active_repls,
        busy_repls=busy_repls,
        markers=read_all_markers(repl),
        isabelle_symbols=load_isabelle_symbols(repl),
    )
    dirs = fetch_dirs(repl)
    scan_err = ensure_sessions_scanned(ctx, dirs, path)
    if scan_err:
        return scan_err
    return ctx


def fetch_heap_segment_texts(repl: ReplClient, qt: QualifiedTheory
                             ) -> tuple[list[str], list[SegmentInfo],
                                        tuple[int, int]] | None:
    """Query source_map and Ir.source for a heap theory's body segments.

    Returns (heap_texts, segments, body_range) or None if unavailable.
    """
    segments = query_source_map(repl, qt.name)
    if segments is None:
        return None
    body_range = body_segment_range(segments)
    if not body_range:
        return None
    body_start, body_end = body_range
    first_seg = segments[body_start].seg_idx
    last_seg = segments[body_end].seg_idx
    raw = ml_expect(repl.send(
        f'Ir.source "{ml_escape(qt.name)}" {first_seg} {last_seg}',
        timeout=30))
    heap_texts = parse_source_output(raw)
    body_seg_count = body_end - body_start + 1
    assert len(heap_texts) == body_seg_count, (
        f"Ir.source for {qt.name} returned {len(heap_texts)} entries "
        f"but body_segment_range expects {body_seg_count}")
    return heap_texts, segments, body_range


def fetch_disk_commands(repl: ReplClient, qt: QualifiedTheory,
                        header: TheoryHeader,
                        active_repls: dict[str, ReplInfo]
                        ) -> list[tuple[int, BodyCommand]]:
    """Parse body commands from disk, filtering comment-only entries.

    Creates and removes a temp REPL if needed for parse_spans.
    """
    repl_name = qt.repl_name
    created_temp = False
    if repl_name not in active_repls:
        result = repl.send(f'Ir.init "{ml_escape(repl_name)}" ["{qt.name}"]')
        if isinstance(result, MlError) or "Created REPL" not in result.output:
            return []
        created_temp = True
    commands = parse_body_commands(repl, repl_name, header)
    if created_temp:
        ml_expect(repl.send(f'Ir.remove "{ml_escape(repl_name)}"'))
    return [(i, cmd) for i, cmd in enumerate(commands)
            if not is_comment_only(cmd.text)]


def build_comparisons(heap_texts: list[str],
                      real_commands: list[tuple[int, BodyCommand]],
                      file_lines: list[str],
                      symbols: dict[str, str]) -> list[SegmentComparison]:
    """Pair each heap segment with its disk command and normalize both."""
    def norm(t: str) -> str:
        return _WS_PAT.sub(' ', symbols_to_unicode(t.strip(), symbols))

    comparisons = []
    for j in range(min(len(heap_texts), len(real_commands))):
        cmd_idx, cmd = real_commands[j]
        start_line = cmd.file_line
        if j + 1 < len(real_commands):
            end_line = real_commands[j + 1][1].file_line - 1
        else:
            end_line = len(file_lines)
        raw_lines = file_lines[start_line - 1:end_line]
        comparisons.append(SegmentComparison(
            seg_idx=j,
            heap_text=heap_texts[j],
            file_lines=raw_lines,
            file_line_start=start_line,
            normalized_heap=norm(heap_texts[j]),
            normalized_disk=norm(cmd.text),
        ))
    return comparisons


def print_dry_run(deps_in_order: list[ResolvedImport],
                  initial_classes: dict[ResolvedImport, FileClassification],
                  propagated_classes: dict[ResolvedImport, FileClassification],
                  initial_plans: dict[ResolvedImport, DepPlan],
                  final_plans: dict[ResolvedImport, DepPlan],
                  ctx: 'CheckContext') -> None:
    """Print a compact table of classifications and plans."""
    has_diamond_changes = any(
        type(initial_plans.get(ri)) != type(final_plans.get(ri))
        or (isinstance(initial_plans.get(ri), CheckPlan)
            and isinstance(final_plans.get(ri), CheckPlan)
            and initial_plans[ri].init_strategy != final_plans[ri].init_strategy)
        for ri in deps_in_order if ri in initial_plans)

    rows = []
    for ri in deps_in_order:
        name = ri.sort_key
        ri_type = type(ri).__name__

        ic = initial_classes.get(ri)
        pc = propagated_classes.get(ri)
        class_col = ic.display_name() if ic else "?"
        stale_col = pc.display_name() if pc and type(pc) != type(ic) else "-"

        ip = initial_plans.get(ri)
        fp = final_plans.get(ri)
        plan_col = ip.display_name() if ip else "?"
        diamond_col = fp.display_name() if (has_diamond_changes and fp) else None
        step_col = (format_step_short(describe_plan(fp, ctx, ri))
                    if fp else "-")

        rows.append((name, ri_type, class_col, stale_col, plan_col, diamond_col, step_col))

    headers = ["theory", "resolved as", "classification", "with staleness", "plan"]
    if has_diamond_changes:
        headers.append("after diamond")
    headers.append("to-step")

    cols = list(zip(*rows)) if rows else [[] for _ in headers]
    widths = [max(len(h), max((len(str(v or "")) for v in col), default=0))
              for h, col in zip(headers, cols + [[] for _ in range(len(headers) - len(cols))])]

    header_line = "  ".join(h.ljust(w) for h, w in zip(headers, widths))
    print(header_line)
    print("  ".join("-" * w for w in widths))
    for row in rows:
        parts = list(row[:5])
        if has_diamond_changes:
            parts.append(row[5] or "-")
        parts.append(row[6])
        print("  ".join(str(p).ljust(w) for p, w in zip(parts, widths)))


def print_heapdiff_report(name: str, comparisons: list[SegmentComparison],
                          extra_on_disk: int, verbose: int) -> None:
    """Format and print the heapdiff report."""
    first_diff_idx = next(
        (i for i, c in enumerate(comparisons) if not c.matches), None)

    if first_diff_idx is None and extra_on_disk <= 0:
        print(f"{name}: heap matches file ({len(comparisons)} segments)")
        return

    first_line = comparisons[0].file_line_start if comparisons else 0
    print(f"{name}: {len(comparisons)} body segments, "
          f"starting at line {first_line}")
    print()

    if first_diff_idx is not None:
        show_from = 0 if verbose >= 1 else max(0, first_diff_idx - 3)
        show_to = first_diff_idx
    else:
        show_from = 0
        show_to = len(comparisons) - 1

    if show_from > 0:
        print(f"  ({show_from} matching segments skipped)")
        print()

    for idx in range(show_from, show_to + 1):
        cmp = comparisons[idx]
        end_line = cmp.file_line_start + len(cmp.file_lines) - 1
        line_range = (f"line {cmp.file_line_start}"
                      if cmp.file_line_start == end_line
                      else f"lines {cmp.file_line_start}-{end_line}")
        if cmp.matches:
            print(f"  segment {cmp.seg_idx} ({line_range}): MATCH")
            if verbose >= 1:
                print(f"    heap: {cmp.heap_text}")
                for rl in cmp.file_lines:
                    print(f"    file: {rl}")
                print()
        else:
            print(f"  segment {cmp.seg_idx} ({line_range}): "
                  f"DIFF at char {cmp.first_diff_char}")
            print(f"    heap: {cmp.heap_text}")
            for rl in cmp.file_lines:
                print(f"    file: {rl}")
            print(f"    normalized heap: {cmp.normalized_heap}")
            print(f"    normalized disk: {cmp.normalized_disk}")
            print()

    remaining = len(comparisons) - show_to - 1
    if remaining > 0 and first_diff_idx is not None:
        print(f"  ({remaining} segments after first diff skipped)")
        print()

    if first_diff_idx is not None:
        cmp = comparisons[first_diff_idx]
        tail_count = len(comparisons) - first_diff_idx + extra_on_disk
        print(f"First diff at segment {first_diff_idx} (file line "
              f"{cmp.file_line_start}). "
              f"{tail_count} commands would be re-stepped.")
    elif extra_on_disk > 0:
        last_cmp = comparisons[-1]
        last_end = last_cmp.file_line_start + len(last_cmp.file_lines)
        print(f"{extra_on_disk} extra commands on disk beyond heap segments "
              f"(from line {last_end}). "
              f"{extra_on_disk} commands would be re-stepped.")


def print_heapdiff(repl: ReplClient, path: str, verbose: int = 0) -> None:
    """Print a diagnostic comparison of heap segments vs disk file."""
    path = os.path.realpath(path)
    ctx = bootstrap_context(repl, path)
    if isinstance(ctx, dict):
        print(f"Error: {ctx.get('error', 'unknown')}", file=sys.stderr)
        return

    qt = ctx.path_index.get(path)
    if not qt:
        print(f"Error: File not in any session: {path}", file=sys.stderr)
        return
    entry = ctx.files[qt]

    if qt.name not in ctx.loaded_theories:
        print(f"Error: {qt.name} is not in the heap", file=sys.stderr)
        return

    heap_result = fetch_heap_segment_texts(ctx.repl, qt)
    if heap_result is None:
        print(f"{qt.name}: no recorded segments "
              f"(heap built without record_theories=true?)")
        return
    heap_texts, segments, body_range = heap_result

    real_commands = fetch_disk_commands(ctx.repl, qt, entry.header,
                                       ctx.active_repls)
    with open(entry.path) as f:
        file_lines = f.read().splitlines()

    comparisons = build_comparisons(heap_texts, real_commands, file_lines,
                                    ctx.isabelle_symbols)
    body_seg_count = body_range[1] - body_range[0] + 1
    extra_on_disk = len(real_commands) - body_seg_count
    print_heapdiff_report(qt.name, comparisons, extra_on_disk, verbose)


def step_after_segment_init(ctx: CheckContext, qt: QualifiedTheory,
                              entry: FileEntry,
                              content_hash: str,
                              tail: list[BodyCommand],
                              seg_spec: str,
                              total_commands: int) -> FileResult | None:
    """Step tail commands after segment-based REPL init.

    Returns FileResult.
    """
    info = ctx.active_repls[qt.repl_name]
    if not tail:
        entry.status = FileStatus.OK
        return FileResult(name=qt.theory_name, status="ok", steps_taken=0)

    ensure_timeout(ctx, qt.repl_name)
    steps_taken = 0
    total = len(tail)
    for cmd in tail:
        log_step(ctx, steps_taken, total, cmd.text)
        ok, output = step(ctx, qt.repl_name, cmd.text)
        steps_taken += 1
        if not ok:
            log_step_done(ctx)
            entry.status = FileStatus.ERROR

            entry.error_line = cmd.file_line
            return FileResult(name=qt.theory_name, status="error",
                              steps_taken=steps_taken,
                              error=output, line=cmd.file_line)

    log_step_done(ctx)
    entry.status = FileStatus.OK

    entry.error_line = None
    return FileResult(name=qt.theory_name, status="ok", steps_taken=steps_taken)


def check_file(ctx: CheckContext, qt: QualifiedTheory,
               commands: list[BodyCommand]) -> FileResult:
    """Check a single file by stepping all its body commands."""
    entry = ctx.files[qt]
    assert entry.status == FileStatus.PENDING, \
        f"check_file called on {qt} with status '{entry.status}'"

    info = ctx.active_repls[qt.repl_name]
    ensure_timeout(ctx, qt.repl_name)
    steps_taken = 0
    total = len(commands)
    for cmd in commands:
        log_step(ctx, steps_taken, total, cmd.text)
        ok, output = step(ctx, qt.repl_name, cmd.text)
        steps_taken += 1
        if not ok:
            log_step_done(ctx)
            entry.status = FileStatus.ERROR

            entry.error_line = cmd.file_line
            return FileResult(name=qt.theory_name, status="error",
                              steps_taken=steps_taken,
                              error=output, line=cmd.file_line)

    log_step_done(ctx)
    entry.status = FileStatus.OK

    entry.error_line = None
    return FileResult(name=qt.theory_name, status="ok", steps_taken=steps_taken)


def step_tail(ctx: CheckContext, qt: QualifiedTheory,
              tail: list[BodyCommand], offset: int,
              total: int) -> FileResult:
    """Step a tail of commands with progress logging.

    offset: number of already-stepped commands (for progress display).
    total: total number of commands in the file.
    Returns FileResult with status ok or error.
    """
    entry = ctx.files[qt]
    info = ctx.active_repls[qt.repl_name]
    ensure_timeout(ctx, qt.repl_name)
    steps_taken = 0
    for cmd in tail:
        log_step(ctx, offset + steps_taken, total, cmd.text)
        ok, output = step(ctx, qt.repl_name, cmd.text)
        steps_taken += 1
        if not ok:
            log_step_done(ctx)
            entry.status = FileStatus.ERROR

            entry.error_line = cmd.file_line
            return FileResult(name=qt.theory_name, status="error",
                              steps_taken=steps_taken,
                              error=output, line=cmd.file_line)

    log_step_done(ctx)
    entry.status = FileStatus.OK

    entry.error_line = None
    return FileResult(name=qt.theory_name, status="ok", steps_taken=steps_taken)


def incremental_check_file(ctx: CheckContext, qt: QualifiedTheory,
                            change: ChangeInfo,
                            step_range: tuple[int, int]) -> FileResult:
    """Incrementally rebuild a file using pre-computed diff.

    Truncates the REPL to just before the first changed command,
    then re-steps the changed tail. Handles empty new_commands
    (body truncated to nothing) by clearing all steps.
    """
    new_commands = change.new_commands
    first_diff = change.first_diff

    truncate_to_step = step_range[0] + first_diff - 1
    truncate_to(ctx, qt.repl_name, truncate_to_step)

    tail = new_commands[first_diff:]
    li = change.line_info
    desc = StepCommands("continuing", li.first_changed_line,
                        li.total_lines, len(tail), "(file changed)")
    log(ctx, f"  {qt.name}: {format_step_description(desc)}")
    return step_tail(ctx, qt, tail, first_diff, len(new_commands))


def execute_recover_error_plan(ctx: CheckContext, ri: ResolvedImport,
                                plan: RecoverErrorPlan) -> PlanResult:
    """Re-execute from the failing command for an unchanged broken file."""
    tail = plan.commands[plan.body_steps:]
    desc = describe_plan(plan, ctx, ri)
    log(ctx, f"  {ri_log_name(ri)}: {format_step_description(desc)}")
    result = step_tail(ctx, plan.qt, tail, plan.body_steps,
                       len(plan.commands))
    if result.status == "ok":
        pin_repl(ctx, plan.qt.repl_name)
    return file_result_to_plan(result, "repl")



def ri_name(ri: ResolvedImport) -> str:
    """Display name for a resolved import."""
    if isinstance(ri, FileImport):
        return ri.qualified.theory_name
    return ri.name


def ri_log_name(ri: ResolvedImport) -> str:
    """Qualified name for verbose logging."""
    if isinstance(ri, FileImport):
        return ri.qualified.name
    return ri.name


def execute_skip_plan(ctx: CheckContext, ri: ResolvedImport,
                       entry: FileEntry | None, plan: SkipPlan) -> PlanResult:
    """Execute a SkipPlan: reuse existing state."""
    name = ri_name(ri)
    marker = ctx.read_marker(plan.qt)
    if isinstance(marker, SteppedMarker):
        pin_repl(ctx, plan.qt.repl_name)
    desc = describe_plan(plan, ctx, ri)
    msg = f"  {ri_log_name(ri)}: {_DIM}{format_step_description(desc)}{_RST}"
    if isinstance(marker, HeapVerifiedMarker) or (
            marker is None and plan.heap_freshness != HeapFreshness.NO_SEGMENTS):
        log2(ctx, msg)
    else:
        log(ctx, msg)
    if isinstance(marker, SteppedMarker):
        return PlanOk(DepInfo(name, "repl", status="ok", steps_taken=0))
    elif isinstance(marker, LoadedMarker):
        return PlanOk(DepInfo(name, "from_file", status="ok"))
    elif isinstance(marker, HeapVerifiedMarker) or marker is None:
        return PlanOk(DepInfo(name, "from_heap"))
    else:
        raise TypeError(f"Unknown marker type for {ri}: {type(marker)}")


def execute_load_file_plan(ctx: CheckContext, ri: ResolvedImport,
                            entry: FileEntry | None,
                            plan: LoadFilePlan) -> PlanResult:
    """Execute a LoadFilePlan: load theory via Ir.load_theory."""
    name = ri_name(ri)
    load_name = ri.name if isinstance(ri, ExternalImport) else plan.qt.name
    desc = describe_plan(plan, ctx, ri)
    log(ctx, f"  {ri_log_name(ri)}: {format_step_description(desc)}")
    success, rebuilt = load_theory(ctx, load_name)
    if success:
        # External imports' dep graphs are opaque to I/C: a sibling
        # ExternalImport earlier in build order may have transitively
        # loaded this one into the heap. For FileImports the assert
        # still holds — classification would have produced SkipPlan.
        if not isinstance(ri, ExternalImport):
            assert rebuilt, (
                f"Expected Ir.load_theory to rebuild {ri_log_name(ri)}, "
                f"but it used cached version.")
        if entry:
            write_marker(ctx, plan.qt.name,
                LoadedMarker(entry.content_hash, compute_dep_hashes(ctx, ri)))
        return PlanOk(DepInfo(name, "from_file", status="ok"))
    else:
        if plan.qt.name in ctx.markers:
            ml_expect(ctx.repl.send(
                f'ic_symtab_delete "{ml_escape(plan.qt.name)}"'))
            del ctx.markers[plan.qt.name]
        return PlanDepFailed(DepInfo(
            name, "from_file", status="error",
            error="failed to load theory",
            path=entry.path if entry else None))


def file_result_to_plan(fr: FileResult, resolution: str) -> PlanResult:
    """Convert a FileResult to PlanOk or PlanDepFailed."""
    dep = DepInfo(fr.name, resolution, status=fr.status,
                  steps_taken=fr.steps_taken, error=fr.error,
                  line=fr.line)
    if fr.status == "error":
        return PlanDepFailed(dep)
    return PlanOk(dep)


def execute_incremental_plan(ctx: CheckContext, ri: ResolvedImport,
                              entry: FileEntry, plan: IncrementalPlan,
                              parents: list[str]) -> PlanResult:
    """Execute an IncrementalPlan: truncate and restep changed tail."""
    file_result = incremental_check_file(
        ctx, plan.qt, plan.change_info, plan.step_range)
    # Update marker so subsequent rechecks see the correct hash
    # (otherwise the dep stays ReplChanged and propagates staleness)
    new_cmds = plan.change_info.new_commands
    write_marker(ctx, plan.qt.name,
        SteppedMarker(entry.content_hash, len(new_cmds),
                      plan.segment_spec,
                      dep_hashes=compute_dep_hashes(ctx, ri)))
    if file_result.status == "ok":
        pin_repl(ctx, plan.qt.repl_name)
    return file_result_to_plan(file_result, "repl")


def apply_init_strategy(ctx: CheckContext, ri: ResolvedImport,
                         qt: QualifiedTheory, strategy: InitStrategy,
                         parents: list[str]) -> str | None:
    """Set up REPL base according to the init strategy.

    INIT: remove old REPL, Ir.init fresh from parents.
    REBASE: Ir.rebase (re-resolve parent pins), truncate all steps.

    Returns error message on failure, None on success.
    """
    repl_name = qt.repl_name

    if strategy == InitStrategy.REBASE:
        repl_id = ml_escape(repl_name)
        ml_expect(ctx.repl.send(f'Ir.rebase "{repl_id}"'))
        info = ctx.active_repls[repl_name]
        if info.step_count > 0:
            ml_expect(ctx.repl.send(
                f'Ir.truncate "{repl_id}" ~{info.step_count}'))
            info.step_count = 0
    elif strategy == InitStrategy.INIT:
        ctx.remove_repl(qt)
        return ensure_repl(ctx, parents, repl_name)

    return None


def execute_check_plan(ctx: CheckContext, ri: ResolvedImport,
                        entry: FileEntry, plan: CheckPlan,
                        parents: list[str]) -> PlanResult:
    """Execute a CheckPlan: full check from scratch."""
    if entry.header.has_keywords:
        return PlanDepFailed(DepInfo(
            ri_name(ri), "repl", status="error",
            error=f"Theory '{plan.qt.name}' declares custom keywords "
                  f"and cannot be checked via REPL; remove "
                  f"--always-stepwise or ensure it is in the heap"))
    v = verify_parent_markers(ctx, ri)
    if not v.ok:
        return PlanAbort(
            f"concurrent change detected while checking "
            f"'{ri_log_name(ri)}': dep '{v.changed_dep}' "
            f"was rebuilt by another client?\n"
            f"  expected: {v.expected}\n"
            f"  actual:   {v.actual}")
    entry.status = FileStatus.PENDING
    repl_err = apply_init_strategy(
        ctx, ri, plan.qt, plan.init_strategy, parents)
    if repl_err:
        return PlanAbort(repl_err)

    commands = parse_body_commands(ctx.repl, plan.qt.repl_name, entry.header)
    write_marker(ctx, plan.qt.name,
        SteppedMarker(entry.content_hash, len(commands),
                      dep_hashes=compute_dep_hashes(ctx, ri)))
    desc = StepCommands("stepwise check", entry.header.body_start_line,
                        entry.total_lines, len(commands))
    log(ctx, f"  {ri_log_name(ri)}: {format_step_description(desc)}")
    file_result = check_file(ctx, plan.qt, commands)
    if file_result.status == "ok":
        pin_repl(ctx, plan.qt.repl_name)
    return file_result_to_plan(file_result, "repl")


def execute_target_unchanged_plan(ctx: CheckContext, ri: ResolvedImport,
                                   plan: TargetUnchangedPlan) -> PlanResult:
    """Execute a TargetUnchangedPlan: report ok with 0 steps."""
    if (isinstance(plan.source, FromHeap)
            and plan.source.freshness == HeapFreshness.NO_SEGMENTS):
        return PlanAbort(
            f"Cannot determine freshness: {plan.qt.name} is part of a "
            f"heap that was built without record_theories=true. Either "
            f"restart the I/R server using a --session without "
            f"{plan.qt.name}, or rebuild the heap with "
            f"-o record_theories=true, and then restart the I/R server.")
    desc = describe_plan(plan, ctx, ri)
    log(ctx, f"  {ri_log_name(ri)}: {_DIM}{format_step_description(desc)}{_RST}")
    return PlanOk(DepInfo(ri_name(ri), "repl", status="ok",
                          steps_taken=0))


def execute_segment_init_plan(ctx: CheckContext, ri: ResolvedImport,
                               entry: FileEntry,
                               plan: SegmentInitPlan) -> PlanResult:
    """Execute a SegmentInitPlan: init from heap segment, step tail."""
    diff = plan.diff
    desc = describe_plan(plan, ctx, ri)
    log(ctx, f"  {ri_log_name(ri)}: {format_step_description(desc)}")
    repl_err = ensure_repl(
        ctx, [], plan.qt.repl_name,
        segment_spec=diff.segment_spec)
    if repl_err:
        return PlanAbort(repl_err)
    write_marker(ctx, plan.qt.name,
        SteppedMarker(diff.content_hash, len(diff.tail),
                      diff.segment_spec,
                      dep_hashes=compute_dep_hashes(ctx, ri)))
    file_result = step_after_segment_init(
        ctx, plan.qt, entry,
        diff.content_hash, diff.tail,
        diff.segment_spec, diff.total_commands)
    if file_result is None:
        return PlanAbort(f"Segment init failed for {ri_log_name(ri)}")
    if file_result.status == "ok":
        pin_repl(ctx, plan.qt.repl_name)
    return file_result_to_plan(file_result, "repl")


def dispatch_plan(ctx: CheckContext, ri: ResolvedImport,
                  plan: DepPlan) -> PlanResult:
    """Execute a single dep's plan. Returns PlanResult."""
    entry = ctx.files.get(ri.qualified) if isinstance(ri, FileImport) else None
    if isinstance(plan, SkipPlan):
        return execute_skip_plan(ctx, ri, entry, plan)
    elif isinstance(plan, TargetUnchangedPlan):
        return execute_target_unchanged_plan(ctx, ri, plan)
    elif isinstance(plan, RecoverErrorPlan):
        return execute_recover_error_plan(ctx, ri, plan)
    elif isinstance(plan, LoadFilePlan):
        return execute_load_file_plan(ctx, ri, entry, plan)
    elif isinstance(plan, IncrementalPlan):
        return execute_incremental_plan(
            ctx, ri, entry, plan, ctx.parents_for(ri))
    elif isinstance(plan, CheckPlan):
        return execute_check_plan(
            ctx, ri, entry, plan, ctx.parents_for(ri))
    elif isinstance(plan, SegmentInitPlan):
        return execute_segment_init_plan(ctx, ri, entry, plan)
    raise TypeError(f"Unknown plan type: {type(plan)}")


def run_dep_job(ctx: CheckContext, ri: ResolvedImport,
                 plan: DepPlan, is_target: bool,
                 dep_futures: dict[ResolvedImport, Future],
                 pool: ReplPool) -> PlanResult:
    """Execute one dep's plan, waiting for its direct deps first.

    1. Wait for direct dependency futures (BEFORE acquiring a connection
       to prevent deadlock — otherwise all workers could hold connections
       while blocked on deps that need connections to proceed).
    2. If any dep failed, return stale immediately.
    3. Acquire connection, execute plan, release.
    """
    # Wait for direct deps
    for dep_ri in ctx.dep_graph.get(ri, []):
        if dep_ri in dep_futures:
            dep_result = dep_futures[dep_ri].result()
            if isinstance(dep_result, (PlanDepFailed, PlanAbort)):
                return PlanDepFailed(DepInfo(
                    ri_name(ri), "stale", status="stale",
                    reason=f"depends on failed {ri_name(dep_ri)}"))

    # Acquire connection and execute
    conn = pool.acquire()
    try:
        job_ctx = make_job_ctx(ctx, conn)
        job_ctx.is_target = is_target
        if isinstance(ri, FileImport):
            job_ctx.job_id = ri.qualified.theory_name
        return dispatch_plan(job_ctx, ri, plan)
    finally:
        pool.release(conn)


def remove_stale_repls(ctx: CheckContext,
                       plans: dict[ResolvedImport, DepPlan]) -> None:
    """Remove REPLs whose plans require destruction."""
    to_remove: set[str] = set()
    to_keep: set[str] = set()
    for ri, plan in plans.items():
        if not isinstance(ri, FileImport):
            continue
        rn = ri.qualified.repl_name
        if plan.removes_repl and rn in ctx.active_repls:
            to_remove.add(rn)
        elif not plan.removes_repl and rn in ctx.active_repls:
            to_keep.add(rn)

    origins = {rn: info.origin for rn, info in ctx.active_repls.items()}
    origins.update({rn: info.origin for rn, info in ctx.busy_repls.items()})
    to_remove = expand_with_pin_dependents(origins, to_remove)
    busy_blockers = to_remove & set(ctx.busy_repls)
    if busy_blockers:
        raise RuntimeError(
            f"Cannot remove: busy REPL(s) {busy_blockers} block removal")
    assert not (to_remove & to_keep), (
        f"REBASE/INIT conflict: {to_remove & to_keep} marked for both "
        f"removal and keeping")
    ordered = removal_order(origins, to_remove)
    remove_repls(ctx.repl, ordered)
    for name in ordered:
        del ctx.active_repls[name]
        # Drop the paired SteppedMarker so a future check() does not see
        # an orphan marker pointing at a destroyed REPL. The invariant
        # "SteppedMarker exists ⇔ matching ic.* REPL exists" must hold.
        key = theory_name_from_repl(name).name
        if isinstance(ctx.markers.get(key), SteppedMarker):
            ml_expect(ctx.repl.send(
                f'ic_symtab_delete "{ml_escape(key)}"'))
            del ctx.markers[key]


def warn_no_record_sessions(
        classifications: dict[ResolvedImport, FileClassification],
        target: ResolvedImport) -> None:
    """Warn if any non-target FileImport dep classified as
    InHeap(NO_SEGMENTS): the heap was built without
    record_theories=true, so I/C trusts the heap copy and silently
    ignores edits to the dep's source on disk. Report by session
    name (the actionable unit — rebuilding the heap fixes every
    theory in it at once)."""
    sessions = sorted({
        c.qt.session_name
        for ri, c in classifications.items()
        if ri != target
           and isinstance(ri, FileImport)
           and isinstance(c, InHeap)
           and c.freshness == HeapFreshness.NO_SEGMENTS
    })
    if not sessions:
        return
    sess_list = ", ".join(sessions)
    print(
        f"I/C: WARN: heap session(s) [{sess_list}] were built "
        f"without record_theories=true; edits to dep source files "
        f"in these sessions will be ignored. Rebuild heap with "
        f"-o record_theories=true and restart I/R server to fix.",
        file=sys.stderr, flush=True)


def execute_plans(ctx: CheckContext,
                   deps_in_order: list[ResolvedImport],
                   plans: dict[ResolvedImport, DepPlan]) -> CheckResponse:
    """Execute pre-computed plans in build order."""
    target = deps_in_order[-1] if deps_in_order else None
    if not target:
        return CheckResponse(
            status="ok",
            target=DepInfo("", "repl", status="ok", steps_taken=0))

    remove_stale_repls(ctx, plans)

    pool = ReplPool(ctx.repl.host, ctx.repl.port, ctx.repl.token,
                    size=ctx.pool_size)
    try:
        if ctx.pool_size > 1 and ctx.verbose >= 1 and sys.stderr.isatty():
            ctx.display = ProgressDisplay()
        if ctx.display:
            ctx.display.start()
        dep_futures: dict[ResolvedImport, Future] = {}
        with CancellableExecutor(max_workers=ctx.pool_size) as executor:
            # Submit in topo order: dep futures exist before dependents
            for ri in deps_in_order:
                is_target = (ri == target)
                future = executor.submit(
                    run_dep_job, ctx, ri, plans[ri], is_target,
                    dep_futures, pool)
                dep_futures[ri] = future

            # Collect results in topo order (deterministic response)
            dep_info: dict[ResolvedImport, DepInfo] = {}
            for ri in deps_in_order:
                result = dep_futures[ri].result()
                if isinstance(result, PlanAbort):
                    return CheckResponse(
                        status="error", error=result.error)
                elif isinstance(result, PlanDepFailed):
                    dep_info[ri] = result.dep
                else:
                    dep_info[ri] = result.dep
    finally:
        if ctx.display:
            ctx.display.stop()
            ctx.display = None
        pool.close()

    target_dep = dep_info.pop(target)
    return CheckResponse(
        status="ok", target=target_dep,
        dependencies=list(dep_info.values()))


# --- Entry points ---

def fetch_info(repl: ReplClient) -> dict[str, str]:
    """Parse /info output of the I/R server into a key->value dict."""
    info = ml_expect(repl.send_raw("/info"))
    result: dict[str, str] = {}
    for line in info.splitlines():
        line = line.strip()
        if "=" in line:
            key, _, val = line.partition("=")
            result[key.strip()] = val.strip()
    return result


def fetch_dirs(repl: ReplClient) -> list[str]:
    """Fetch session directories from I/R server via /info."""
    val = fetch_info(repl).get("dir", "")
    return [val] if val and val != "(none)" else []


def remote_prover(repl: ReplClient) -> str | None:
    """Hostname I/R is talking to via I/P, or None if local."""
    val = fetch_info(repl).get("remote", "")
    return val if val and val != "(local)" else None


def check(path: str, repl: ReplClient,
          diamond_strategy: DiamondStrategy = DiamondStrategy.HEURISTIC,
          verbose: int = 0,
          pool_size: int = 1,
          timeout: int = 0,
          interactive: bool = False,
          always_stepwise: bool = False,
          dry_run: bool = False,
          ) -> dict:
    """Check a .thy file. Stateless: all state recovered from I/R + disk."""
    path = os.path.realpath(path)
    if not os.path.isfile(path):
        return {"status": "error", "error": f"File not found: {path}"}

    # Bootstrap: recover state from I/R
    loaded_theories, active_repls, busy_repls = bootstrap(repl)

    # Load I/C ML snippets (ic_parse_spans etc.) if not already loaded
    ensure_snippets_loaded(repl)

    # Configure I/R: enable full_spans for segment-based change detection.
    ml_expect(repl.send('Ir.config (fn {color, show_ignored, full_spans, '
              'show_theory_in_source, auto_replay} => {color=color, '
              'show_ignored=show_ignored, full_spans=true, '
              'show_theory_in_source=show_theory_in_source, '
              'auto_replay=auto_replay})'))

    markers = read_all_markers(repl)
    if not markers and interactive:
        print("I/C: no cached state, comparing heap to files on disk "
              "(might take a while...)", file=sys.stderr, flush=True)

    ctx = CheckContext(
        repl=repl,
        loaded_theories=loaded_theories,
        active_repls=active_repls,
        busy_repls=busy_repls,
        markers=markers,
        diamond_strategy=diamond_strategy,
        verbose=verbose,
        isabelle_symbols=load_isabelle_symbols(repl),
        pool_size=pool_size,
        timeout=timeout,
        always_stepwise=always_stepwise,
    )

    log(ctx, f"  {_DIM}{len(loaded_theories)} loaded theories, "
              f"{len(active_repls)} active REPLs{_RST}")

    dirs = fetch_dirs(repl)

    # Phase 1: Discover sessions and load files
    scan_err = ensure_sessions_scanned(ctx, dirs, path)
    if scan_err:
        return scan_err

    # Phase 2: Resolve target
    name = ctx.path_index.get(path)
    if not name:
        return {"status": "error", "error": f"File not in any session: {path}"}

    entry = ctx.files[name]

    def with_parse_errors(resp: dict) -> dict:
        if ctx.parse_errors:
            resp["parse_errors"] = ctx.parse_errors
        return resp

    if not entry.header.body_ended:
        return with_parse_errors({
            "status": "error",
            "error": f"Theory '{name.theory_name}' has no terminating "
                     f"'end' line",
        })
    if entry.header.has_keywords:
        return with_parse_errors({
            "status": "error",
            "error": f"Theory '{name.theory_name}' declares custom keywords "
                     f"in its header, which I/C cannot handle via REPL",
        })

    # Phase 3: Collect transitive deps in build order
    deps_in_order = transitive_deps_in_build_order(ctx, name)
    log(ctx, f"  {_DIM}{len(deps_in_order)} transitive dependencies "
              f"of {name.theory_name}{_RST}")

    # Abort if any needed dep REPL is busy
    for ri in deps_in_order:
        if isinstance(ri, FileImport) and ri.qualified.repl_name in ctx.busy_repls:
            return with_parse_errors({
                "status": "error",
                "error": f"REPL {ri.qualified.repl_name} is busy "
                         f"(being modified by another client)",
            })

    # Phase 4: Classify
    initial_classes = classify_files(ctx, deps_in_order)
    warn_no_record_sessions(initial_classes, deps_in_order[-1])

    # Phase 5: Staleness propagation
    propagated_classes = dict(initial_classes)
    rebase_rebuilding = propagate_staleness(
        propagated_classes, deps_in_order, ctx.files,
        markers=ctx.markers, active_repls=ctx.active_repls)

    # Phase 6: Build plans
    initial_plans = build_plans(propagated_classes, deps_in_order,
                                always_stepwise=ctx.always_stepwise)

    # Phase 7: Diamond resolution + init strategies
    final_plans = dict(initial_plans)
    resolve_diamonds(final_plans, propagated_classes, deps_in_order, ctx)
    assign_init_strategies(final_plans, rebase_rebuilding,
                           ctx.dep_graph, deps_in_order)
    ctx.theory_ref = compute_theory_refs(final_plans, deps_in_order)

    if dry_run:
        print_dry_run(deps_in_order, initial_classes, propagated_classes,
                      initial_plans, final_plans, ctx)
        return with_parse_errors({"status": "ok", "dry_run": True})

    # Phase 8: Execute
    return with_parse_errors(
        execute_plans(ctx, deps_in_order, final_plans).to_dict())


def clean(repl: ReplClient) -> dict:
    """Remove all ic.* REPLs and clear marker storage."""
    repls_raw = ml_expect(repl.send('Ir.repls ()'))
    active, busy = parse_repls_output(repls_raw)
    if busy:
        return {"status": "error",
                "error": f"Cannot clean: {len(busy)} REPL(s) busy "
                         f"({', '.join(busy)})"}
    origins = {rn: info.origin for rn, info in active.items()}
    ordered = removal_order(origins, set(active))
    remove_repls(repl, ordered)
    if isinstance(repl.send('ic_snippets_loaded'), MlOk):
        ml_expect(repl.send('ic_symtab_clear ()'))
    return {"status": "ok"}


if __name__ == "__main__":
    print("This is the I/C check engine module. "
          "Use ic_client.py for the CLI.", file=sys.stderr)
    sys.exit(1)
