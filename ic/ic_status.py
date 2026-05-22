"""I/C Status: read-only display of I/R and I/C state.

Pure query — does not modify any I/R or I/C state.
Designed to run concurrently with an in-progress check().
"""

import sys

from ic_repl import ReplClient, MlOk, strip_ml_noise
from ic_check import (
    bootstrap, read_all_markers, fetch_dirs,
    theory_name_from_repl,
    SteppedMarker, LoadedMarker, HeapVerifiedMarker,
    marker_hash, ml_expect,
)


def progress_bar(step_count: int, cmd_count: int, width: int = 20) -> str:
    """Format a progress bar: [====    ] step/total."""
    if cmd_count <= 0:
        filled = width
    else:
        filled = width * step_count // cmd_count
    bar = "=" * filled + " " * (width - filled)
    return f"[{bar}] {step_count}/{cmd_count}"


def has_repl(repl_name: str, active_repls: dict, busy_repls: dict) -> bool:
    """True if a REPL with this name exists, busy or active."""
    return repl_name in active_repls or repl_name in busy_repls


def status(repl: ReplClient, verbose: int = 0) -> None:
    """Display I/C status. Read-only — no I/R state changes."""
    loaded_theories, active_repls, busy_repls = bootstrap(repl)

    # Read markers — may fail if snippets not loaded (no I/C state yet)
    result = repl.send('ic_symtab_get_all ()')
    if isinstance(result, MlOk):
        markers = read_all_markers(repl)
    else:
        markers = {}

    n_repls = len(active_repls) + len(busy_repls)
    n_markers = len(markers)
    print(f"I/C Status: {len(loaded_theories)} theories, "
          f"{n_repls} REPLs, {n_markers} markers")

    if not active_repls and not busy_repls and not markers:
        print("\n  (no I/C state)")
        return

    # Categorize each marker
    stepping: list[tuple[str, str]] = []     # (qualified_name, display_line)
    done: list[tuple[str, str]] = []
    stale: list[tuple[str, str]] = []
    loaded: list[str] = []
    heap_verified: list[str] = []
    orphan_repls: list[str] = []
    orphan_markers: list[tuple[str, str]] = []

    # Process busy REPLs: render same bar as active, with busy suffix
    for name, info in sorted(busy_repls.items()):
        qt_name = theory_name_from_repl(name).name
        marker = markers.get(qt_name)
        busy_tag = f"  busy [{info.operation}] {info.elapsed}"
        if isinstance(marker, SteppedMarker):
            bar = progress_bar(info.step_count, marker.cmd_count)
            seg = (f"  (segment {marker.segment_spec})"
                   if marker.segment_spec else "")
            stepping.append((qt_name, f"{bar}{seg}{busy_tag}"))
        else:
            orphan_repls.append(qt_name)


    # Process stepped markers (REPLs)
    for name, info in sorted(active_repls.items()):
        qt_name = theory_name_from_repl(name).name
        marker = markers.get(qt_name)
        if not isinstance(marker, SteppedMarker):
            orphan_repls.append(qt_name)
            continue

        bar = progress_bar(info.step_count, marker.cmd_count)
        seg = f"  (segment {marker.segment_spec})" if marker.segment_spec else ""
        line = f"{bar}{seg}"

        if info.step_count < marker.cmd_count:
            stepping.append((qt_name, line))
        else:
            done.append((qt_name, line))

    # Check dep staleness for all SteppedMarker and LoadedMarker entries
    for name, marker in sorted(markers.items()):
        if not isinstance(marker, (SteppedMarker, LoadedMarker)):
            continue
        stale_deps = []
        for dep_name, dep_hash in marker.dep_hashes.items():
            dep_marker = markers.get(dep_name)
            if dep_marker is not None and marker_hash(dep_marker) != dep_hash:
                stale_deps.append(dep_name)
        if stale_deps:
            stale.append((name, f"marker changed for deps: {', '.join(stale_deps)}"))

    # Categorize non-stepped markers
    for name, marker in sorted(markers.items()):
        if isinstance(marker, SteppedMarker):
            # Already handled above via active_repls.
            # Check for orphan: stepped marker but no REPL (active or busy).
            repl_name = f"ic.{name}"
            if not has_repl(repl_name, active_repls, busy_repls):
                orphan_markers.append((name, "stepped marker, no REPL"))
        elif isinstance(marker, LoadedMarker):
            loaded.append(name)
        elif isinstance(marker, HeapVerifiedMarker):
            heap_verified.append(name)

    def print_section(header: str, entries: list[tuple[str, str]]) -> None:
        """Print a section with name-aligned detail columns."""
        if not entries:
            return
        w = max(len(name) for name, _ in entries)
        print(f"\n  {header} ({len(entries)}):")
        for name, detail in entries:
            print(f"    {name.ljust(w)}  {detail}")

    def print_name_section(header: str, names: list[str]) -> None:
        """Print a section of bare names."""
        if not names:
            return
        print(f"\n  {header} ({len(names)}):")
        for name in names:
            print(f"    {name}")

    # Print sections — always show stepping/stale, counts or full lists for rest
    print_section("Stepping", stepping)
    print_section("Stale", stale)
    print_section("Orphan REPLs",
                  [(n, "(no marker)") for n in sorted(orphan_repls)])
    print_section("Orphan markers", orphan_markers)

    if verbose >= 1:
        print_section("Done", done)
        print_name_section("Loaded", loaded)
        print_name_section("Heap verified", heap_verified)
    else:
        counts = []
        if done:
            counts.append(f"{len(done)} REPLs done")
        if loaded:
            counts.append(f"{len(loaded)} loaded")
        if heap_verified:
            counts.append(f"{len(heap_verified)} heap verified")
        if counts:
            print(f"\n  {', '.join(counts)}")
