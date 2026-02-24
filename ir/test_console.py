#!/usr/bin/env python3
"""Test ir.ML via isabelle console.

Assumes the session heap is already built.

Usage: python3 test_console.py [--isabelle PATH] [--session SESSION] [--dir DIR]
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import time

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
IR_ML = os.path.join(SCRIPT_DIR, "ir.ML")

# ANSI
_RED = "\033[31m"
_GREEN = "\033[32m"
_YELLOW = "\033[33m"
_BOLD = "\033[1m"
_DIM = "\033[2m"
_RESET = "\033[0m"
_SYM_OK = f"{_GREEN}✓{_RESET}"
_SYM_FAIL = f"{_RED}✗{_RESET}"
_SYM_SKIP = f"{_YELLOW}–{_RESET}"
_SYM_BUSY = f"{_YELLOW}↻{_RESET}"
_CLEAR_LINE = "\r\033[2K"

passed = 0
failed = 0


def run_console(isabelle, session, directory, ml_commands):
    """Pipe ml_commands into isabelle console, return (exit_code, output)."""
    cmd = [isabelle, "console"]
    if directory:
        cmd += ["-d", directory]
    cmd += ["-l", session, "-n"]
    result = subprocess.run(
        cmd, input=ml_commands + "\n",
        capture_output=True, text=True, timeout=120)
    return result.returncode, result.stdout + result.stderr


def run_test(name, isabelle, session, directory, ml_commands):
    global passed, failed
    print(f"  {_SYM_BUSY} {name}", end="", flush=True)
    t0 = time.time()
    try:
        rc, output = run_console(isabelle, session, directory, ml_commands)
        elapsed = time.time() - t0
        if rc != 0 or re.search(r"^Exception-|^exception .+ raised|^Error[- ]|^ML error",
                                    output, re.MULTILINE):
            print(f"{_CLEAR_LINE}  {_SYM_FAIL} {name} {_DIM}({elapsed:.1f}s){_RESET}")
            for line in output.splitlines()[-5:]:
                print(f"    {_DIM}{line}{_RESET}")
            failed += 1
        else:
            print(f"{_CLEAR_LINE}  {_SYM_OK} {name} {_DIM}({elapsed:.1f}s){_RESET}")
            passed += 1
    except Exception as e:
        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_FAIL} {name}: {e} {_DIM}({elapsed:.1f}s){_RESET}")
        failed += 1


def use(ml):
    return f'use "{IR_ML}"; {ml}'


def main():
    p = argparse.ArgumentParser(description="Test ir.ML via isabelle console")
    p.add_argument("--isabelle", default=os.environ.get("ISABELLE", "isabelle"))
    p.add_argument("--session", default="HOL")
    p.add_argument("--dir", default=None)
    p.add_argument("--require-source", action="store_true",
                   help="Fail if source commands are not available")
    args = p.parse_args()

    # Preflight checks
    if not shutil.which(args.isabelle):
        print(f"{_SYM_FAIL} isabelle not found: {args.isabelle}", file=sys.stderr)
        sys.exit(1)
    if not os.path.isfile(IR_ML):
        print(f"{_SYM_FAIL} ir.ML not found: {IR_ML}", file=sys.stderr)
        sys.exit(1)

    # Probe source availability up front
    print(f"{_BOLD}Probing{_RESET} source availability "
          f"{_DIM}(session={args.session}){_RESET}", flush=True)
    print(f"  {_SYM_BUSY} loading heap", end="", flush=True)
    t0 = time.time()
    _, probe_output = run_console(
        args.isabelle, args.session, args.dir, f'use "{IR_ML}";')
    has_source = "source commands available" in probe_output and "not available" not in probe_output
    avail_thy = None

    if has_source:
        m = re.search(r"source commands available \((\d+) theories?\)", probe_output)
        n_theories = m.group(1) if m else "?"
        _, seg_output = run_console(
            args.isabelle, args.session, args.dir,
            use('(Ir.source "Main" 0 0 handle ERROR msg => writeln msg);'))
        if "No recorded segments" not in seg_output:
            avail_thy = "Main"
        else:
            m = re.search(r'Available: (\S+)', seg_output)
            if m:
                avail_thy = m.group(1).rstrip(',')
        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_OK} source commands available "
              f"({n_theories} theories, sample: {avail_thy or 'none'}) "
              f"{_DIM}({elapsed:.1f}s){_RESET}")
    else:
        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_SKIP} source commands not available "
              f"{_DIM}({elapsed:.1f}s){_RESET}")
        if args.require_source:
            print(f"{_SYM_FAIL} --require-source set but source commands not available")
            sys.exit(1)

    # Run tests
    print(f"\n{_BOLD}Running{_RESET} ir.ML console tests "
          f"{_DIM}(session={args.session}){_RESET}")

    run = lambda name, ml: run_test(name, args.isabelle, args.session, args.dir, ml)

    run("load ir.ML",
        f'use "{IR_ML}";')

    run("help",
        use('Ir.help ();'))

    run("theories",
        use('Ir.theories ();'))

    run("init + show",
        use('Ir.init "t1" "Main"; Ir.show ();'))

    run("step + state",
        use('Ir.init "t1" "Main"; Ir.step "lemma True by simp"; Ir.state ~1;'))

    run("text",
        use('Ir.init "t1" "Main"; Ir.step "lemma True by simp"; Ir.text ();'))

    run("edit + replay",
        use('Ir.init "t1" "Main"; Ir.step "lemma True by simp"; '
            'Ir.edit 0 "lemma True by auto"; Ir.replay ();'))

    run("truncate",
        use('Ir.init "t1" "Main"; Ir.step "lemma True by simp"; '
            'Ir.step "lemma True by auto"; Ir.truncate 0;'))

    run("fork + focus + merge",
        use('Ir.init "t1" "Main"; Ir.step "lemma True by simp"; '
            'Ir.fork "t2" 0; Ir.focus "t2"; '
            'Ir.step "lemma True by auto"; Ir.merge ();'))

    run("repls + remove",
        use('Ir.init "t1" "Main"; Ir.init "t2" "Main"; '
            'Ir.repls (); Ir.remove "t2";'))

    if has_source:
        run_test("source (missing theory)", args.isabelle, args.session, args.dir,
                 use('(Ir.source "NonExistent.Theory" 0 0 handle ERROR msg => '
                     'if String.isSubstring "No recorded segments" msg '
                     'orelse String.isSubstring "undefined entry" msg '
                     'then writeln "OK: expected error" '
                     'else raise (ERROR msg));'))
        if avail_thy:
            run_test("source", args.isabelle, args.session, args.dir,
                     use(f'Ir.source "{avail_thy}" 0 3;'))
        else:
            print(f"  {_SYM_SKIP} source listing {_DIM}(no stored theories){_RESET}")
    else:
        run_test("source (graceful error without segments)",
                 args.isabelle, args.session, args.dir,
                 use('(Ir.source "Main" 0 3 handle ERROR _ => ());'))

    run("config",
        use('Ir.config (fn c => {color = false, show_ignored = #show_ignored c, '
            'full_spans = #full_spans c, show_theory_in_source = #show_theory_in_source c, '
            'auto_replay = #auto_replay c});'))

    # Summary
    total = passed + failed
    if failed == 0:
        print(f"\n{_SYM_OK} {_BOLD}{passed}/{total} passed{_RESET}")
    else:
        print(f"\n{_SYM_FAIL} {_BOLD}{passed}/{total} passed, "
              f"{_RED}{failed} failed{_RESET}")
    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()
