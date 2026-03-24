"""Isabelle heap database utilities and HeapInfo facade.

Shared library used by ir/repl.py (HeapInfo class) and ip/heap-db-inspect
(lower-level utilities).  All Isabelle heap DB queries, path resolution,
digest checking, and timing analysis live here.
"""

import hashlib
import os
import re
import sqlite3
import subprocess

try:
    import zstandard
    HAS_ZSTD = True
except ImportError:
    HAS_ZSTD = False


# ---------------------------------------------------------------------------
# Isabelle environment and path resolution
# ---------------------------------------------------------------------------

_isabelle_env_cache = {}  # (var, isabelle_bin) -> value


def isabelle_getenv(var, isabelle_bin=None):
    """Resolve an Isabelle environment variable.

    Checks os.environ first, then ``isabelle getenv``.
    *isabelle_bin* defaults to ``$ISABELLE_TOOL`` or ``"isabelle"``.
    """
    if isabelle_bin is None:
        isabelle_bin = os.environ.get("ISABELLE_TOOL", "isabelle")
    key = (var, isabelle_bin)
    if key not in _isabelle_env_cache:
        val = os.environ.get(var, "")
        if not val:
            try:
                r = subprocess.run(
                    [isabelle_bin, "getenv", "-b", var],
                    capture_output=True, text=True, timeout=5)
                val = r.stdout.strip()
            except Exception:
                val = ""
        _isabelle_env_cache[key] = val
    return _isabelle_env_cache[key]


def resolve_path(name, isabelle_bin=None):
    """Resolve symbolic Isabelle path to filesystem path.

    Returns None if unresolvable (including ``~~/`` system paths).
    """
    if name.startswith("~~/"):
        return None  # ISABELLE_HOME files don't change
    if name.startswith("~/"):
        return os.path.expanduser(name)
    if name.startswith("$"):
        slash = name.find("/")
        if slash < 0:
            return None
        var = name[1:slash]
        base = isabelle_getenv(var, isabelle_bin)
        return os.path.join(base, name[slash + 1:]) if base else None
    if name.startswith("/"):
        return name
    return None


# ---------------------------------------------------------------------------
# File hashing and symbol-offset-to-line mapping
# ---------------------------------------------------------------------------

def file_sha1(path):
    """Compute SHA1 of a file, or None if unreadable."""
    try:
        return hashlib.sha1(open(path, "rb").read()).hexdigest()
    except OSError:
        return None


_file_content_cache = {}


def file_lines(path):
    """Get cached symbol-offset-to-line table for a file.

    Isabelle uses symbol offsets where ``\\<name>`` counts as 1 symbol.
    Returns list of symbol offsets at each line start, or None.
    """
    if path not in _file_content_cache:
        try:
            content = open(path, "r", errors="replace").read()
            line_starts = [0]  # symbol offset at start of each line
            sym = 0
            i = 0
            while i < len(content):
                if content[i] == "\n":
                    sym += 1
                    line_starts.append(sym)
                elif content[i] == "\\" and i + 1 < len(content) and content[i + 1] == "<":
                    end = content.find(">", i)
                    if end >= 0:
                        i = end
                    sym += 1
                else:
                    sym += 1
                i += 1
            _file_content_cache[path] = line_starts
        except OSError:
            _file_content_cache[path] = None
    return _file_content_cache[path]


def offset_to_line(path, offset):
    """Convert 1-based Isabelle symbol offset to 1-based line number."""
    line_starts = file_lines(path)
    if line_starts is None:
        return None
    offset = int(offset)
    lo, hi = 0, len(line_starts) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if line_starts[mid] <= offset:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


# ---------------------------------------------------------------------------
# Source checking
# ---------------------------------------------------------------------------

_SYSTEM_PREFIXES = ("~~/src/Pure/", "~~/src/HOL/", "~~/src/Tools/")


def is_system_source(name):
    return any(name.startswith(p) for p in _SYSTEM_PREFIXES)


class SourceChecker:
    """Check source file digests against filesystem."""

    def __init__(self, conn, session, isabelle_bin=None):
        self.rows = conn.execute(
            "SELECT name, digest FROM isabelle_sources WHERE session_name=? ORDER BY name",
            (session,)).fetchall()
        self._isabelle_bin = isabelle_bin
        self._checked = {}  # name -> (resolved_path, matches)
        # Pre-resolve all $VAR prefixes so env vars are populated
        for name, _ in self.rows:
            if name.startswith("$"):
                slash = name.find("/")
                if slash > 0:
                    isabelle_getenv(name[1:slash], isabelle_bin)

    def check(self, name, digest):
        if name not in self._checked:
            path = resolve_path(name, self._isabelle_bin)
            if path and os.path.isfile(path):
                actual = file_sha1(path)
                self._checked[name] = (path, actual == digest)
            else:
                self._checked[name] = (path, None)  # None = can't check
        return self._checked[name]

    def get_line(self, name, offset):
        """Get line number for a file+offset, only if digest matches."""
        entry = self._checked.get(name)
        if not entry:
            for n, d in self.rows:
                if n == name:
                    self.check(n, d)
                    break
            entry = self._checked.get(name)
        if entry and entry[1] is True and entry[0]:
            return offset_to_line(entry[0], offset)
        return None


# ---------------------------------------------------------------------------
# Blob decoding (zstd + YXML)
# ---------------------------------------------------------------------------

def decompress_blob(blob):
    if not blob:
        return ""
    if blob[:4] == b'\x28\xb5\x2f\xfd':  # zstd magic
        if not HAS_ZSTD:
            return None  # signal missing dependency
        data = zstandard.ZstdDecompressor().decompress(blob, max_output_size=50*1024*1024)
        return data.decode("utf-8", errors="replace")
    return blob.decode("utf-8", errors="replace") if isinstance(blob, bytes) else blob


def parse_yxml_records(text):
    """Parse YXML-encoded list of property records."""
    if not text:
        return []
    records = []
    for entry in text.split("\x05\x06\x05"):
        props = {}
        for part in entry.split("\x06"):
            part = part.strip("\x05:").strip()
            if "=" in part:
                k, v = part.split("=", 1)
                if k:
                    props[k] = v
        if props:
            records.append(props)
    return records


def decode_yxml_props(data):
    if not data:
        return {}
    text = data.decode("utf-8", errors="replace") if isinstance(data, bytes) else data
    props = {}
    for part in text.split("\x06"):
        part = part.strip("\x05:").strip()
        if "=" in part:
            k, v = part.split("=", 1)
            if k:
                props[k] = v
    return props


# ---------------------------------------------------------------------------
# Formatting helpers
# ---------------------------------------------------------------------------

def fmt_time(secs_str):
    try:
        s = float(secs_str)
    except (ValueError, TypeError):
        return str(secs_str)
    if s < 60:
        return f"{s:.1f}s"
    m, s = divmod(s, 60)
    if m < 60:
        return f"{int(m)}m {s:.0f}s"
    h, m = divmod(m, 60)
    return f"{int(h)}h {int(m)}m {s:.0f}s"


# ---------------------------------------------------------------------------
# HeapInfo — high-level facade for ir/repl.py and ir/mcp_server.py
# ---------------------------------------------------------------------------

class HeapInfo:
    """Query an Isabelle session heap database (.db file)."""

    def __init__(self, db_path, session, isabelle_bin="isabelle"):
        self.db_path = db_path
        self._session = session
        self._isabelle_bin = isabelle_bin
        self._conn = sqlite3.connect(db_path, check_same_thread=False)
        self._checker = None
        self._timing_records = None  # lazy

    @staticmethod
    def discover(session, isabelle_bin, ml_identifier="", heaps_dir=None):
        """Find the heap DB for *session*.

        Discovery order for the heaps directory:
          1. Explicit *heaps_dir* parameter
          2. ``ISABELLE_HEAPS_OVERRIDE`` env var
          3. ``isabelle getenv -b ISABELLE_HEAPS``
          4. ``isabelle getenv -b ISABELLE_HOME_USER`` + ``/heaps``

        Then looks for ``<heaps>/<ml_identifier>/log/<session>.db``,
        falling back to ``<heaps>/log/<session>.db``.
        """
        if not heaps_dir:
            heaps_dir = os.environ.get("ISABELLE_HEAPS_OVERRIDE", "")
        if not heaps_dir:
            try:
                r = subprocess.run(
                    [isabelle_bin, "getenv", "-b", "ISABELLE_HEAPS"],
                    capture_output=True, text=True, timeout=10)
                heaps_dir = r.stdout.strip()
            except Exception:
                pass
        if not heaps_dir:
            try:
                r = subprocess.run(
                    [isabelle_bin, "getenv", "-b", "ISABELLE_HOME_USER"],
                    capture_output=True, text=True, timeout=10)
                home_user = r.stdout.strip()
                if home_user:
                    heaps_dir = os.path.join(home_user, "heaps")
            except Exception:
                pass
        if not heaps_dir:
            return None

        candidates = []
        if ml_identifier:
            candidates.append(
                os.path.join(heaps_dir, ml_identifier, "log", f"{session}.db"))
        candidates.append(
            os.path.join(heaps_dir, "log", f"{session}.db"))
        # Scan platform subdirectories if ml_identifier didn't match
        if os.path.isdir(heaps_dir):
            for entry in os.listdir(heaps_dir):
                if ml_identifier and entry == ml_identifier:
                    continue  # already tried
                db = os.path.join(heaps_dir, entry, "log", f"{session}.db")
                if db not in candidates:
                    candidates.append(db)

        for path in candidates:
            if os.path.isfile(path):
                return HeapInfo(path, session, isabelle_bin)
        return None

    # -- sources --

    def _ensure_checker(self):
        if self._checker is None:
            self._checker = SourceChecker(
                self._conn, self._session, self._isabelle_bin)
        return self._checker

    def source_files(self):
        """Non-system source files with digest verification.

        Returns ``[{"name", "path", "digest", "status"}]`` where
        *status* is one of ``"verified"``, ``"changed"``, ``"missing"``,
        ``"unresolved"``.
        """
        checker = self._ensure_checker()
        result = []
        for name, digest in checker.rows:
            if is_system_source(name):
                continue
            path, matches = checker.check(name, digest)
            if matches is True:
                status = "verified"
            elif matches is False:
                status = "changed"
            elif path is not None:
                status = "missing"
            else:
                status = "unresolved"
            result.append({
                "name": name,
                "path": path,
                "digest": digest,
                "status": status,
            })
        return result

    def unresolved_env_vars(self):
        """Environment variables referenced by source paths that could not be resolved."""
        checker = self._ensure_checker()
        unresolved = set()
        for name, _ in checker.rows:
            if name.startswith("$"):
                slash = name.find("/")
                if slash > 0:
                    var = name[1:slash]
                    if not isabelle_getenv(var, self._isabelle_bin):
                        unresolved.add(var)
        return unresolved

    def resolved_env_vars(self):
        """Environment variables referenced by source paths that were resolved.

        Returns ``{var: value}`` for all ``$VAR/...`` source paths
        where the variable could be resolved.
        """
        checker = self._ensure_checker()
        result = {}
        for name, _ in checker.rows:
            if name.startswith("$"):
                slash = name.find("/")
                if slash > 0:
                    var = name[1:slash]
                    val = isabelle_getenv(var, self._isabelle_bin)
                    if val:
                        result[var] = val
        return result

    # -- timings --

    def _ensure_timing_records(self):
        if self._timing_records is not None:
            return self._timing_records
        blob = self._conn.execute(
            "SELECT command_timings FROM isabelle_session_info WHERE session_name=?",
            (self._session,)).fetchone()
        if not blob or not blob[0]:
            self._timing_records = []
            return self._timing_records
        text = decompress_blob(blob[0])
        if text is None:
            self._timing_records = []
            return self._timing_records
        records = parse_yxml_records(text)
        # Filter out system sources
        self._timing_records = [
            r for r in records if not is_system_source(r.get("file", ""))]
        return self._timing_records

    def timing_hotspots(self, top_n=20, file_filter=None):
        """Formatted text: slowest commands and per-file aggregation."""
        records = self._ensure_timing_records()
        if file_filter:
            records = [r for r in records if file_filter in r.get("file", "")]
        if not records:
            if file_filter:
                return f"No commands matching '{file_filter}'"
            return "No command timing data available"

        checker = self._ensure_checker()
        # Pre-check files so get_line works
        for r in records:
            f = r.get("file", "")
            if f:
                for n, d in checker.rows:
                    if n == f:
                        checker.check(n, d)
                        break

        timed = [(float(r.get("elapsed", "0")), r) for r in records]
        timed.sort(key=lambda x: -x[0])

        lines = [f"Slowest commands (top {min(top_n, len(timed))}):", ""]
        for elapsed, r in timed[:top_n]:
            name = r.get("name", "?")
            f = r.get("file", "")
            offset = r.get("offset", "")
            loc = ""
            if f and offset:
                line = checker.get_line(f, offset)
                if line:
                    loc = f":L{line}"
                else:
                    loc = f"+{offset} (source unavailable / out of sync)"
            for prefix in ("$ISABELLE_PROJECT_BASE/", "~~/src/"):
                f = f.replace(prefix, "")
            lines.append(f"  {elapsed:6.2f}s  {name:20s} {f}{loc}")

        # Per-file aggregation
        file_times = {}
        for elapsed, r in timed:
            f = r.get("file", "(unknown)")
            file_times[f] = file_times.get(f, 0.0) + elapsed
        by_file = sorted(file_times.items(), key=lambda x: -x[1])
        total_time = sum(t for _, t in by_file)

        lines.append("")
        lines.append(f"Time per file (top {min(top_n, len(by_file))}, "
                      f"total {fmt_time(str(total_time))}):")
        lines.append("")
        for f, t in by_file[:top_n]:
            for prefix in ("$ISABELLE_PROJECT_BASE/", "~~/src/"):
                f = f.replace(prefix, "")
            pct = 100 * t / total_time if total_time else 0
            lines.append(f"  {t:6.1f}s {pct:4.1f}%  {f}")

        return "\n".join(lines)

    def timing_by_offset(self):
        """``{(file, offset): elapsed}`` for all timed commands."""
        records = self._ensure_timing_records()
        result = {}
        for r in records:
            f = r.get("file", "")
            offset = r.get("offset", "")
            elapsed = r.get("elapsed", "")
            if f and offset and elapsed:
                try:
                    result[(f, int(offset))] = float(elapsed)
                except (ValueError, TypeError):
                    continue
        return result

    def close(self):
        if self._conn:
            self._conn.close()
            self._conn = None
