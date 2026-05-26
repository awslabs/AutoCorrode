# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

"""I/C Core: theory parsing, dependency resolution, ROOT/ROOTS session parsing."""

import enum
import hashlib
import os
import re
from dataclasses import dataclass, field


class DiamondStrategy(enum.Enum):
    RELOAD = "reload"
    REPL = "repl"
    HEURISTIC = "heuristic"


class InitStrategy(enum.Enum):
    INIT = "init"      # remove old REPL (if exists), Ir.init fresh
    REBASE = "rebase"  # Ir.rebase existing REPL (updates base to new parent pins)


class FileStatus(enum.Enum):
    PENDING = "pending"
    OK = "ok"
    ERROR = "error"
    STALE = "stale"


# --- Qualified theory names ---

@dataclass(frozen=True, order=True)
class QualifiedTheory:
    """A session-qualified theory name, e.g. 'SomeSession.SomeTheory'."""
    name: str  # always session.theory format

    @property
    def repl_name(self) -> str:
        return f"ic.{self.name}"

    @property
    def theory_name(self) -> str:
        """Bare theory name (last component)."""
        return self.name.split('.')[-1]

    @property
    def session_name(self) -> str:
        """Session name (first component)."""
        return self.name.split('.')[0]

    def __str__(self) -> str:
        return self.name


def qualify_import(imp: str, current_session: str) -> QualifiedTheory:
    """Turn a raw import into a qualified name.

    - Unqualified 'A' in session 'S' → QualifiedTheory('S.A')
    - Already qualified 'S.A' → QualifiedTheory('S.A')
    """
    if '.' in imp:
        return QualifiedTheory(imp)
    return QualifiedTheory(f"{current_session}.{imp}")


# --- Import resolution ---

@dataclass(frozen=True)
class ResolvedImport:
    """Base class for resolved imports."""

    @property
    def sort_key(self) -> str:
        raise NotImplementedError

    def __lt__(self, other: 'ResolvedImport') -> bool:
        return self.sort_key < other.sort_key


@dataclass(frozen=True)
class FileImport(ResolvedImport):
    """Import resolved to a managed source file."""
    qualified: QualifiedTheory

    @property
    def sort_key(self) -> str:
        return self.qualified.name


@dataclass(frozen=True)
class HeapImport(ResolvedImport):
    """Import already available in the heap."""
    name: str

    @property
    def sort_key(self) -> str:
        return self.name


@dataclass(frozen=True)
class ExternalImport(ResolvedImport):
    """Import from an external session, needs Ir.load_theory."""
    name: str

    @property
    def sort_key(self) -> str:
        return self.name


# --- File classification (per-file, no dependency analysis) ---

@dataclass
class FileClassBase:
    """Base for per-file classification."""
    qt: QualifiedTheory

    @property
    def is_rebuilding(self) -> bool:
        """Whether this classification means the dep is being rebuilt."""
        return False

    def display_name(self) -> str:
        return type(self).__name__


class HeapFreshness(enum.Enum):
    VERIFIED = "verified"       # segments compared, source matches heap
    NO_SEGMENTS = "no_segments" # no segments available, freshness unknown


@dataclass
class FromFile:
    """Target was loaded by a previous Ir.load_theory call;
    classify_loaded_repl just verified content_hash + dep_hashes."""
    pass


@dataclass
class FromHeap:
    """Target lives in the Isabelle heap. Freshness depends on whether
    recorded segments were available for diffing against disk."""
    freshness: HeapFreshness


UnchangedSource = FromFile | FromHeap


@dataclass
class InHeap(FileClassBase):
    """Theory in heap, not changed (or unknown)."""
    freshness: HeapFreshness = HeapFreshness.VERIFIED

    def display_name(self) -> str:
        return f"InHeap({self.freshness.value})"


@dataclass
class HeapStaleDep(FileClassBase):
    """Heap theory whose dep was rebuilt — needs fresh REPL check."""
    @property
    def is_rebuilding(self) -> bool:
        return True


@dataclass
class ReplClean(FileClassBase):
    """Has REPL, file unchanged (hash match), previous check OK."""
    in_heap: bool = False  # theory is also in the Isabelle heap


@dataclass
class ReplCachedError(FileClassBase):
    """Has REPL, file unchanged, but previous check had an error."""
    commands: list['BodyCommand']
    body_steps: int         # successful steps before the error
    line_info: 'LineInfo'   # file-line anchors for log messages
    in_heap: bool = False


@dataclass
class ReplChanged(FileClassBase):
    """Has REPL, file changed (hash mismatch)."""
    @property
    def is_rebuilding(self) -> bool:
        return True
    change_info: 'ChangeInfo'
    restep_lines: int
    step_range: tuple[int, int]  # saved from REPL (for incremental truncate)
    new_header: object            # TheoryHeader parsed from disk
    content_hash: str             # SHA256 of disk file
    segment_spec: str | None = None  # if from a segment-init REPL


@dataclass
class NoRepl(FileClassBase):
    """No REPL, needs loading/stepping."""
    @property
    def is_rebuilding(self) -> bool:
        return True


@dataclass
class FileLoaded(FileClassBase):
    """Loaded via Ir.load_theory, file unchanged (marker hash matches disk)."""
    pass


@dataclass
class FileNotLoaded(FileClassBase):
    """Not yet loaded — needs Ir.load_theory."""
    @property
    def is_rebuilding(self) -> bool:
        return True
    pass


@dataclass
class SegmentDiff:
    """Result of comparing disk commands against heap segments."""
    segment_spec: str           # init from this segment
    tail: list['BodyCommand']   # BodyCommands to step after init
    total_commands: int         # total body commands (for logging)
    content_hash: str           # SHA256 of disk file
    line_info: 'LineInfo'       # file-line anchors for log messages


@dataclass
class HeapStale(FileClassBase):
    """Heap theory with recorded segments, source changed on disk."""
    diff: SegmentDiff
    @property
    def is_rebuilding(self) -> bool:
        return True


FileClassification = (InHeap | HeapStaleDep | ReplClean | ReplCachedError
                      | ReplChanged | NoRepl | FileLoaded | FileNotLoaded
                      | HeapStale)


# --- Dep resolution plan (after global analysis) ---

@dataclass
class DepPlan:
    """Base: what to do with a dependency."""
    qt: QualifiedTheory

    @property
    def removes_repl(self) -> bool:
        """Whether this plan destroys the existing REPL."""
        return False

    def display_name(self) -> str:
        return type(self).__name__

    def import_name(self) -> str:
        """Theory name to use when referencing this dep as a parent.
        Default: pinned REPL (plans that create/use a REPL)."""
        return f"pin@{self.qt.repl_name}"


@dataclass
class SkipPlan(DepPlan):
    """No work: REPL exists and is fresh, theory has been loaded,
    or theory is available in the heap."""
    has_stepped_repl: bool = False
    heap_freshness: HeapFreshness | None = None

    def import_name(self) -> str:
        """Theory name to use when referencing this dep as a parent."""
        return f"pin@{self.qt.repl_name}" if self.has_stepped_repl else self.qt.name


@dataclass
class LoadFilePlan(DepPlan):
    """Call Ir.load_theory."""
    @property
    def removes_repl(self) -> bool:
        return True

    def import_name(self) -> str:
        return self.qt.name


@dataclass
class CheckPlan(DepPlan):
    """Full check from scratch — create REPL, step all commands.

    init_strategy controls how the REPL base is set up:
    - INIT: remove old REPL + Ir.init fresh from parent theories
    - REBASE: Ir.rebase existing REPL (updates base to new parent pins)
              + Ir.truncate all + step from scratch
    - None: undecided; assigned by assign_init_strategies after diamond
            resolution.
    """
    init_strategy: InitStrategy | None = None  # assigned by assign_init_strategies

    @property
    def removes_repl(self) -> bool:
        assert self.init_strategy is not None, \
            "removes_repl called before assign_init_strategies"
        return self.init_strategy == InitStrategy.INIT

    def display_name(self) -> str:
        if self.init_strategy:
            return f"CheckPlan({self.init_strategy.value.upper()})"
        return "CheckPlan(?)"


@dataclass
class TargetUnchangedPlan(DepPlan):
    """Target file unchanged since last check — return ok with 0 steps.

    This plan does NOT create a REPL. We rely on this: if a file ever
    had both an active stepped REPL and a loaded theory (two different
    Isabelle theory identity objects), and a diamond conflict chose
    apply_repl, Ir.init would fail with 'Duplicate theory name' due
    to the conflicting identities in the parent ancestry. By not
    creating REPLs for unchanged targets, we avoid this scenario.
    """
    source: UnchangedSource

    def import_name(self) -> str:
        return self.qt.name


@dataclass
class IncrementalPlan(DepPlan):
    """Incremental rebuild — truncate existing REPL, restep changed tail."""
    change_info: 'ChangeInfo'
    step_range: tuple[int, int]
    segment_spec: str | None = None  # preserved for marker update


@dataclass
class SegmentInitPlan(DepPlan):
    """Segment init from heap — init from recorded segment, step tail."""
    diff: SegmentDiff

    @property
    def removes_repl(self) -> bool:
        return True


@dataclass
class RecoverErrorPlan(DepPlan):
    """Re-execute from the failing command for an unchanged broken file."""
    commands: list['BodyCommand']
    body_steps: int         # successful steps before the error
    line_info: 'LineInfo'   # file-line anchors for log messages


@dataclass
class FileResult:
    """Result of checking a single file (target or dep via REPL)."""
    name: str
    status: str  # "ok" | "error"
    steps_taken: int = 0
    error: str | None = None
    line: int | None = None

    def to_dict(self) -> dict:
        d: dict = {"name": self.name, "status": self.status,
                    "steps_taken": self.steps_taken}
        if self.error is not None:
            d["error"] = self.error
        if self.line is not None:
            d["line"] = self.line
        return d


@dataclass
class DepInfo:
    """How a dependency was resolved."""
    name: str
    resolution: str  # "repl" | "from_heap" | "from_file" | "stale"
    status: str | None = None
    error: str | None = None
    steps_taken: int | None = None
    reason: str | None = None
    path: str | None = None
    line: int | None = None

    def to_dict(self) -> dict:
        d: dict = {"name": self.name, "resolution": self.resolution}
        for k in ("status", "error", "steps_taken", "reason", "path", "line"):
            v = getattr(self, k)
            if v is not None:
                d[k] = v
        return d


@dataclass
class CheckResponse:
    """Top-level response from check()."""
    status: str  # "ok" | "error"
    error: str | None = None
    target: DepInfo | None = None
    dependencies: list[DepInfo] = field(default_factory=list)

    def to_dict(self) -> dict:
        d: dict = {"status": self.status}
        if self.error is not None:
            d["error"] = self.error
        if self.target is not None:
            d["target"] = self.target.to_dict()
        if self.dependencies:
            d["dependencies"] = [dep.to_dict() for dep in self.dependencies]
        return d

# --- Plan execution results ---

@dataclass
class PlanOk:
    """Dep succeeded."""
    dep: DepInfo


@dataclass
class PlanDepFailed:
    """Dep was checked/loaded but had errors."""
    dep: DepInfo


@dataclass
class PlanAbort:
    """Fatal error — abort immediately."""
    error: str


PlanResult = PlanOk | PlanDepFailed | PlanAbort


# --- Theory header parsing ---

THEORY_PAT = re.compile(r'(?m)^\s*theory\s+(\S+)')
IMPORTS_PAT = re.compile(r'(?s)\bimports\b\s+(.*?)(?:\bkeywords\b|\babbrevs\b|\bbegin\b|\Z)')
TOKEN_PAT = re.compile(r'"[^"]+"|[^\s"]+')


def strip_comments(text: str) -> str:
    r"""Strip (* ... *) and \<comment> \<open>...\<close> blocks (with nesting)."""
    result = []
    i = 0
    while i < len(text):
        if text[i:i+2] == '(*':
            i += 2
            depth = 1
            while i < len(text) and depth > 0:
                if text[i:i+2] == '(*':
                    depth += 1
                    i += 2
                elif text[i:i+2] == '*)':
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif text[i:].startswith('\\<comment>'):
            i += len('\\<comment>')
            while i < len(text) and text[i] in ' \t\n':
                i += 1
            if text[i:].startswith('\\<open>'):
                i += len('\\<open>')
                depth = 1
                while i < len(text) and depth > 0:
                    if text[i:].startswith('\\<open>'):
                        depth += 1
                        i += len('\\<open>')
                    elif text[i:].startswith('\\<close>'):
                        depth -= 1
                        i += len('\\<close>')
                    else:
                        i += 1
        else:
            result.append(text[i])
            i += 1
    return ''.join(result)


def normalize_theory_id(raw: str) -> str:
    """Normalize a theory import identifier."""
    trimmed = raw.strip()
    if trimmed.startswith('"') and trimmed.endswith('"') and len(trimmed) >= 2:
        trimmed = trimmed[1:-1]
    trimmed = trimmed.rsplit('/', 1)[-1]
    return trimmed.removesuffix('.thy').strip()


# --- Data classes ---

@dataclass
class TheoryHeader:
    name: str
    imports: list[str]
    body: str
    body_start_line: int  # 1-based line of first char after 'begin'
    has_keywords: bool = False  # theory header declares custom keywords
    body_ended: bool = True  # False if no terminating `^end\s*$` was found


@dataclass
class BodyCommand:
    text: str
    file_line: int  # 1-based line number in the .thy file


@dataclass
class LineInfo:
    """File-line anchors for verbose log messages."""
    first_changed_line: int   # 1-based file_line where re-stepping begins
    total_lines: int          # len(file_text.splitlines())


@dataclass
class ChangeInfo:
    """Diff between old and new commands for a changed file."""
    old_commands: list[BodyCommand]
    new_commands: list[BodyCommand]
    first_diff: int  # index of first differing command
    line_info: LineInfo


@dataclass
class FileEntry:
    path: str
    header: TheoryHeader
    session_name: str | None = None
    content_hash: str = ""
    total_lines: int = 0
    status: FileStatus = FileStatus.PENDING
    error_line: int | None = None


@dataclass
class SessionInfo:
    name: str               # e.g. "Misc"
    base: str               # e.g. "HOL"
    directory: str           # absolute path to dir containing ROOT
    session_deps: list[str] = field(default_factory=list)
    directories: list[str] = field(default_factory=list)    # abs paths of extra dirs
    theories: dict[str, str] = field(default_factory=dict)  # name → abs path


@dataclass
class ICState:
    files: dict[str, FileEntry] = field(default_factory=dict)
    build_order: list[str] = field(default_factory=list)
    loaded_theories: set[str] = field(default_factory=set)
    total_steps: int = 0


# --- Theory file parsing ---

def parse_theory_file(text: str) -> TheoryHeader:
    """Parse a .thy file and extract header (name, imports) and body."""
    name_match = THEORY_PAT.search(text)
    if not name_match:
        raise ValueError("No 'theory' declaration found")
    name = normalize_theory_id(name_match.group(1))

    imports_match = IMPORTS_PAT.search(text)
    imports = []
    if imports_match:
        block = strip_comments(imports_match.group(1))
        imports = [normalize_theory_id(t) for t in TOKEN_PAT.findall(block)]
        imports = [i for i in imports if i]

    # Find 'begin' after the theory keyword (IMPORTS_PAT already consumes
    # 'begin' so we search from after the theory name)
    begin_match = re.search(r'\bbegin\b', text[name_match.end():])
    if not begin_match:
        return TheoryHeader(name=name, imports=imports, body="",
                            body_start_line=0)

    header_text = text[name_match.end():name_match.end() + begin_match.start()]
    has_keywords = bool(re.search(r'\bkeywords\b', strip_comments(header_text)))

    body_start = name_match.end() + begin_match.end()

    # Find the last 'end' on its own line (theory-closing end)
    end_match = None
    for m in re.finditer(r'(?m)^end\s*$', text):
        if m.start() > body_start:
            end_match = m

    if end_match:
        body = text[body_start:end_match.start()]
        body_ended = True
    else:
        body = text[body_start:]
        body_ended = False

    body_start_line = text[:body_start].count('\n') + 1

    return TheoryHeader(name=name, imports=imports, body=body,
                        body_start_line=body_start_line,
                        has_keywords=has_keywords,
                        body_ended=body_ended)


def file_content_hash(text: str) -> str:
    """Compute a short hash of file content for change detection."""
    return hashlib.sha256(text.encode()).hexdigest()[:16]


# --- ROOT/ROOTS session parsing ---

_ROOT_KEYWORDS = {
    'sessions', 'directories', 'theories', 'options', 'description',
    'document_files', 'export_files', 'export_classpath',
}


def strip_isabelle_comments(text: str) -> str:
    """Remove (* ... *) comments (with nesting) from text."""
    result = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i+2] == '(*':
            depth += 1
            i += 2
        elif text[i:i+2] == '*)' and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            result.append(text[i])
            i += 1
        else:
            i += 1
    return ''.join(result)


def tokenize_root(text: str) -> list[str]:
    """Tokenize ROOT file text after comment stripping.

    Quoted strings have quotes stripped. Square-bracket blocks are single tokens.
    """
    text = strip_isabelle_comments(text)
    tokens = []
    i = 0
    while i < len(text):
        c = text[i]
        if c in ' \t\n\r':
            i += 1
        elif c == '"':
            # Quoted string — find closing quote, strip quotes
            end = text.index('"', i + 1)
            tokens.append(text[i+1:end])
            i = end + 1
        elif c == '[':
            # Bracket block — single token (for skipping)
            end = text.index(']', i + 1)
            tokens.append(text[i:end+1])
            i = end + 1
        else:
            # Unquoted token
            end = i
            while end < len(text) and text[end] not in ' \t\n\r"[]':
                end += 1
            tokens.append(text[i:end])
            i = end
    return tokens


def parse_root_file(root_path: str) -> SessionInfo:
    """Parse a ROOT file and return a SessionInfo."""
    root_path = os.path.realpath(root_path)
    root_dir = os.path.dirname(root_path)

    with open(root_path, 'r') as f:
        text = f.read()

    tokens = tokenize_root(text)
    if len(tokens) < 4 or tokens[0] != 'session':
        raise ValueError(f"Invalid ROOT file: {root_path}")

    name = tokens[1]
    # Expect: session NAME = BASE +
    # The '=' and '+' might be separate tokens or absent
    idx = 2
    if idx < len(tokens) and tokens[idx] == '=':
        idx += 1
    base = tokens[idx] if idx < len(tokens) else "HOL"
    idx += 1
    if idx < len(tokens) and tokens[idx] == '+':
        idx += 1

    session_deps: list[str] = [base]  # base session is always a dependency
    directory_names: list[str] = []
    theory_names: list[str] = []
    current_block: str | None = None

    while idx < len(tokens):
        tok = tokens[idx]

        if tok in _ROOT_KEYWORDS:
            current_block = tok
            idx += 1
            # Skip optional [...] modifier after keyword
            if idx < len(tokens) and tokens[idx].startswith('['):
                idx += 1
            continue

        if current_block == 'sessions':
            session_deps.append(tok)
        elif current_block == 'directories':
            directory_names.append(tok)
        elif current_block == 'theories':
            theory_names.append(tok)
        # Other blocks (options, description, document_files): skip tokens

        idx += 1

    # Resolve theory names to file paths (flat: "folder/A" → name "A")
    theories: dict[str, str] = {}
    for entry in theory_names:
        thy_name = os.path.basename(entry)  # flatten: folder/A → A
        thy_path = os.path.join(root_dir, entry.replace('/', os.sep) + '.thy')
        theories[thy_name] = os.path.realpath(thy_path)

    extra_dirs = [os.path.realpath(os.path.join(root_dir, d))
                   for d in directory_names]

    return SessionInfo(
        name=name, base=base, directory=root_dir,
        session_deps=session_deps, directories=extra_dirs,
        theories=theories,
    )


def parse_roots_file(roots_path: str) -> list[str]:
    """Parse a ROOTS file and return absolute directory paths."""
    roots_dir = os.path.dirname(os.path.realpath(roots_path))
    dirs = []
    with open(roots_path, 'r') as f:
        for line in f:
            line = line.strip()
            if line:
                dirs.append(os.path.join(roots_dir, line))
    return dirs


def discover_sessions(dirs: list[str]) -> dict[str, SessionInfo]:
    """Discover all sessions from the given directories.

    For each directory: parse ROOT if present, parse ROOTS and recurse into
    listed subdirectories. Raises ValueError on duplicate session names.
    """
    sessions: dict[str, SessionInfo] = {}
    visited: set[str] = set()

    def scan_dir(d: str) -> None:
        d = os.path.realpath(d)
        if d in visited:
            return
        visited.add(d)

        root_path = os.path.join(d, 'ROOT')
        if os.path.isfile(root_path):
            session = parse_root_file(root_path)
            if session.name in sessions:
                raise ValueError(
                    f"Duplicate session '{session.name}': "
                    f"{sessions[session.name].directory} and {d}")
            sessions[session.name] = session

        roots_path = os.path.join(d, 'ROOTS')
        if os.path.isfile(roots_path):
            for subdir in parse_roots_file(roots_path):
                if os.path.isdir(subdir):
                    scan_dir(subdir)

    for d in dirs:
        scan_dir(d)

    return sessions


# --- ML string escaping ---

def ml_escape(text: str) -> str:
    """Escape text for use in an ML string literal."""
    return (text
            .replace('\\', '\\\\')
            .replace('"', '\\"')
            .replace('\n', '\\n')
            .replace('\t', '\\t')
            .replace('\r', ''))


# --- Isabelle symbol handling ---

_SYMBOL_RE = re.compile(r'\\<\^?\w+>')


def symbol_to_byte_offsets(text: str, symbol_offsets: list[int]) -> list[int]:
    """Convert 1-based Isabelle symbol offsets to 1-based byte offsets.

    Isabelle counts \\<name> sequences as single symbols, so symbol offsets
    diverge from byte offsets when the text contains such sequences.
    """
    if not symbol_offsets:
        return []

    # Build mapping: symbol position (1-based) → byte position (1-based)
    targets = set(symbol_offsets)
    max_target = max(symbol_offsets)
    result = {}
    sym_pos = 1  # 1-based symbol position
    byte_pos = 0  # 0-based byte position
    while byte_pos < len(text) and sym_pos <= max_target:
        if sym_pos in targets:
            result[sym_pos] = byte_pos + 1  # 1-based byte offset
        m = _SYMBOL_RE.match(text, byte_pos)
        if m:
            byte_pos = m.end()
        else:
            byte_pos += 1
        sym_pos += 1

    return [result.get(s, s) for s in symbol_offsets]


# --- Command splitting ---

def split_body_by_offsets(body: str, offsets: list[int],
                          body_start_line: int) -> list[BodyCommand]:
    """Split body into commands using 1-based symbol offsets from Ir.parse_spans.

    Isabelle symbol offsets are converted to byte offsets first, since
    \\<name> sequences count as 1 symbol but multiple bytes.

    Args:
        body: The theory body text (between begin and end).
        offsets: 1-based symbol offsets where each command starts.
        body_start_line: 1-based line number in the file where body starts.
    """
    if not offsets:
        return []
    byte_offsets = symbol_to_byte_offsets(body, offsets)
    commands = []
    for i, off in enumerate(byte_offsets):
        start = off - 1  # 0-based
        end = (byte_offsets[i + 1] - 1) if (i + 1 < len(byte_offsets)) else len(body)
        text = body[start:end].strip()
        if text:
            file_line = body_start_line + body[:start].count('\n')
            commands.append(BodyCommand(text=text, file_line=file_line))
    return commands


# --- Dependency resolution ---

DepGraph = dict[ResolvedImport, list[ResolvedImport]]


def resolve_dependencies(files: dict[QualifiedTheory, FileEntry],
                         loaded_theories: set[str],
                         ) -> tuple[list[ResolvedImport], DepGraph]:
    """Resolve all dependencies and return (build_order, dep_graph).

    All imports (file, heap, external) go into the dep graph.
    dep_graph values preserve import order from the theory header.
    Heap and external imports have no outgoing edges.
    Raises ValueError on dependency cycles.
    """
    dep_graph: DepGraph = {}

    for qt, entry in files.items():
        ri_self = FileImport(qt)
        deps: list[ResolvedImport] = []
        for imp in entry.header.imports:
            ri = resolve_import(imp, qt.session_name, files, loaded_theories)
            if ri not in dep_graph:
                dep_graph[ri] = []
            deps.append(ri)
        dep_graph[ri_self] = deps

    return topological_sort(dep_graph), dep_graph


def resolve_import(imp: str, current_session: str,
                    files: dict[QualifiedTheory, FileEntry],
                    loaded_theories: set[str],
                    ) -> ResolvedImport:
    """Resolve a single import to FileImport, HeapImport, or ExternalImport.

    File deps take priority — if a theory has a source file in `files`,
    it is a file dependency. Otherwise, if the import is present in
    `loaded_theories` (from Ir.theories()), it is a heap import.
    Anything else is external (needs Ir.load_theory at execution time).
    """
    qualified = qualify_import(imp, current_session)
    if qualified in files:
        return FileImport(qualified)
    if imp in loaded_theories or qualified.name in loaded_theories:
        return HeapImport(imp)
    return ExternalImport(imp)


def topological_sort(graph: dict[str, set[str]]) -> list[str]:
    """Topological sort using Kahn's algorithm. Raises ValueError on cycles."""
    # Deduplicate deps for in-degree computation (lists may have repeats)
    unique_deps = {n: set(graph[n]) & set(graph) for n in graph}
    in_degree = {n: len(unique_deps[n]) for n in graph}

    queue = sorted([n for n in graph if in_degree[n] == 0])
    result = []

    while queue:
        node = queue.pop(0)
        result.append(node)
        for n, deps in unique_deps.items():
            if node in deps:
                in_degree[n] -= 1
                if in_degree[n] == 0:
                    # Insert sorted for deterministic order
                    idx = 0
                    while idx < len(queue) and queue[idx] < n:
                        idx += 1
                    queue.insert(idx, n)

    if len(result) != len(graph):
        remaining = set(graph) - set(result)
        cycle = find_cycle(graph, remaining)
        raise ValueError(f"Dependency cycle: {' -> '.join(str(n) for n in cycle)}")

    return result


def find_cycle(graph: dict[str, set[str]], nodes: set[str]) -> list[str]:
    """Find a cycle among the given nodes."""
    visited: set[str] = set()
    path: list[str] = []

    def dfs(node: str) -> list[str] | None:
        if node in visited:
            if node in path:
                idx = path.index(node)
                return path[idx:] + [node]
            return None
        visited.add(node)
        path.append(node)
        for dep in graph.get(node, set()):
            if dep in nodes:
                result = dfs(dep)
                if result:
                    return result
        path.pop()
        return None

    for n in sorted(nodes):
        visited.clear()
        path.clear()
        result = dfs(n)
        if result:
            return result
    return list(nodes)  # fallback

