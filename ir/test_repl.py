#!/usr/bin/env python3
"""Test repl.py TCP server: single-client and multi-client.

Assumes the session heap is already built.

Usage: python3 test_repl.py [--isabelle PATH] [--session SESSION] [--dir DIR]
"""
import argparse
import os
import random
import signal
import socket
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

SENTINEL = "<<DONE>>"
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def find_isabelle(isabelle_arg=None):
    """Find Isabelle installation (same logic as repl.py)."""
    candidates = []
    if isabelle_arg:
        expanded = os.path.expanduser(isabelle_arg)
        if os.path.isdir(expanded):
            candidates.extend([
                os.path.join(expanded, "bin", "isabelle"),
                os.path.join(expanded, "isabelle"),
            ])
        else:
            candidates.append(expanded)
    else:
        if sys.platform == "darwin":
            candidates.extend([
                "/Applications/Isabelle2025-2.app/bin/isabelle",
                os.path.expanduser("~/Isabelle2025-2.app/bin/isabelle"),
                os.path.expanduser("~/Isabelle2025-2-experimental.app/bin/isabelle"),
            ])
        else:
            candidates.extend([
                os.path.expanduser("~/Isabelle2025-2/bin/isabelle"),
            ])
    for c in candidates:
        if os.path.isfile(c) and os.access(c, os.X_OK):
            return c
    raise RuntimeError(
        f"Isabelle not found. Tried: {', '.join(candidates)}\n"
        f"Use --isabelle to specify the path.")

# ANSI
_RED = "\033[31m"
_GREEN = "\033[32m"
_YELLOW = "\033[33m"
_BOLD = "\033[1m"
_DIM = "\033[2m"
_RESET = "\033[0m"
_SYM_OK = f"{_GREEN}✓{_RESET}"
_SYM_FAIL = f"{_RED}✗{_RESET}"
_SYM_BUSY = f"{_YELLOW}↻{_RESET}"
_CLEAR_LINE = "\r\033[2K"


def find_free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def send_recv(sock, cmd, timeout=5):
    """Send a command and read until sentinel."""
    old = sock.gettimeout()
    sock.settimeout(timeout)
    try:
        sock.sendall((cmd.strip() + "\n").encode())
        buf = b""
        while True:
            chunk = sock.recv(4096)
            if not chunk:
                raise EOFError("Connection closed")
            buf += chunk
            text = buf.decode("utf-8", errors="replace")
            if SENTINEL in text:
                return text[:text.index(SENTINEL)].strip()
    finally:
        sock.settimeout(old)


def authenticate(sock, token):
    """Send token as first line and expect OK response."""
    if token:
        sock.sendall((token + "\n").encode())
        buf = b""
        sock.settimeout(5)
        while b"\n" not in buf:
            chunk = sock.recv(1024)
            if not chunk:
                raise RuntimeError("Connection closed during auth")
            buf += chunk
        if not buf.startswith(b"OK"):
            raise RuntimeError(f"Auth failed: {buf!r}")


def connect(port, retries=120, delay=2.0, proc=None, token=""):
    """Connect to the server, retrying until ready."""
    for i in range(retries):
        if proc is not None and proc.poll() is not None:
            raise RuntimeError(f"Server process exited (rc={proc.returncode})")
        try:
            s = socket.create_connection(("127.0.0.1", port), timeout=5)
            authenticate(s, token)
            return s
        except (ConnectionRefusedError, OSError):
            time.sleep(delay)
    raise RuntimeError(f"Server not ready after {retries * delay}s")


passed = 0
failed = 0


def run_test(name, fn):
    global passed, failed
    print(f"  {_SYM_BUSY} {name}", end="", flush=True)
    t0 = time.time()
    try:
        fn()
        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_OK} {name} {_DIM}({elapsed:.1f}s){_RESET}")
        passed += 1
        return True
    except AssertionError as e:
        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_FAIL} {name} {_DIM}({elapsed:.1f}s){_RESET}")
        for line in str(e).splitlines():
            print(f"    {_DIM}{line}{_RESET}")
        failed += 1
        return False
    except Exception as e:
        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_FAIL} {name}: {type(e).__name__}: {e} "
              f"{_DIM}({elapsed:.1f}s){_RESET}")
        failed += 1
        return False


def q(s):
    """ML-quote a string."""
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'


def core_tests(sock, prefix):
    """Generate reusable core tests. Returns list of (name, fn) pairs.

    Each test is self-contained: creates REPLs with {prefix}_ prefixed IDs
    and removes them afterwards. Can be run concurrently with different
    prefixes on separate connections.
    """
    r = f"{prefix}_r"   # shared REPL for sequential tests
    tests = []

    def test_help():
        out = send_recv(sock, 'Ir.help ();')
        assert "Ir.init" in out, f"Expected help text, got:\n{out}"
    tests.append(("help", test_help))

    def test_theories():
        out = send_recv(sock, 'Ir.theories ();')
        assert "Main" in out, f"Expected Main theory, got:\n{out}"
    tests.append(("theories", test_theories))

    def test_init_show():
        send_recv(sock, f'Ir.init {q(r)} ["Main"];')
        out = send_recv(sock, f'Ir.show {q(r)};')
        assert r in out, f"Expected REPL {r}, got:\n{out}"
    tests.append(("init_show", test_init_show))

    def test_step():
        out = send_recv(sock, f'Ir.step {q(r)} "lemma dummy: True by simp";')
        assert "theorem dummy: True" in out, f"Unexpected output:\n{out}"
    tests.append(("step", test_step))

    def test_state():
        send_recv(sock, f'Ir.step {q(r)} "lemma foo: True";')
        out = send_recv(sock, f'Ir.state {q(r)} ~1;')
        assert "goal (1 subgoal):" in out, f"Unexpected state:\n{out}"
    tests.append(("state", test_state))

    def test_text():
        out = send_recv(sock, f'Ir.text {q(r)};')
        assert "lemma" in out, f"Expected lemma text, got:\n{out}"
    tests.append(("text", test_text))

    def test_edit_replay():
        send_recv(sock, f'Ir.edit {q(r)} 0 "lemma True by auto";')
        send_recv(sock, f'Ir.replay {q(r)};')
    tests.append(("edit_replay", test_edit_replay))

    def test_fork_merge():
        fr = f"{prefix}_fork"
        send_recv(sock, f'Ir.fork {q(r)} {q(fr)} 0;')
        send_recv(sock, f'Ir.step {q(fr)} "lemma True by auto";')
        send_recv(sock, f'Ir.merge {q(fr)};')
    tests.append(("fork_merge", test_fork_merge))

    def test_truncate_negative():
        t = f"{prefix}_trn"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma a: True by simp";')
        send_recv(sock, f'Ir.step {q(t)} "lemma b: True by simp";')
        send_recv(sock, f'Ir.step {q(t)} "lemma c: True by simp";')
        out = send_recv(sock, f'Ir.truncate {q(t)} ~1;')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.truncate {q(t)} ~1;')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "1 step" in out, f"Expected 1 step, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("truncate_negative", test_truncate_negative))

    def test_truncate_negative_multi():
        t = f"{prefix}_trn2"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma a: True by simp";')
        send_recv(sock, f'Ir.step {q(t)} "lemma b: True by simp";')
        send_recv(sock, f'Ir.step {q(t)} "lemma c: True by simp";')
        out = send_recv(sock, f'Ir.truncate {q(t)} ~2;')
        assert "dropped 2" in out, f"Expected dropped 2, got:\n{out}"
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "1 step" in out, f"Expected 1 step, got:\n{out}"
        out = send_recv(sock, f'Ir.truncate {q(t)} ~1;')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "0 step" in out, f"Expected 0 steps, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("truncate_negative_multi", test_truncate_negative_multi))

    def test_back():
        t = f"{prefix}_bk"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma x: True by simp";')
        send_recv(sock, f'Ir.step {q(t)} "lemma y: True by simp";')
        out = send_recv(sock, f'Ir.back {q(t)};')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "1 step" in out, f"Expected 1 step, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("back", test_back))

    def test_back_to_empty():
        t = f"{prefix}_bke"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma z: True by simp";')
        out = send_recv(sock, f'Ir.back {q(t)};')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "0 step" in out, f"Expected 0 steps, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("back_to_empty", test_back_to_empty))

    def test_repls():
        out = send_recv(sock, 'Ir.repls ();')
        assert r in out, f"Expected {r} in repls, got:\n{out}"
    tests.append(("repls", test_repls))

    def test_remove():
        t = f"{prefix}_tmp"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("remove", test_remove))

    def test_config():
        send_recv(sock, 'Ir.config (fn c => '
                  '{color = false, show_ignored = #show_ignored c, '
                  'full_spans = #full_spans c, '
                  'show_theory_in_source = #show_theory_in_source c, '
                  'auto_replay = #auto_replay c});')
    tests.append(("config", test_config))

    def test_multiline_step():
        t = f"{prefix}_ml1"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        out = send_recv(sock, f'Ir.step {q(t)} "lemma ml_test: True\\nby simp";')
        assert "ml_test" in out, f"Expected ml_test theorem, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("multiline_step", test_multiline_step))

    def test_multiline_step_raw_newline():
        t = f"{prefix}_ml2"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        out = send_recv(sock, f'Ir.step {q(t)} "lemma ml_raw: True\nby simp";')
        assert "ml_raw" in out, f"Expected ml_raw theorem, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("multiline_step_raw_newline", test_multiline_step_raw_newline))

    def test_ft_name():
        t = f"{prefix}_ft1"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        out = send_recv(sock, f'Ir.find_theorems {q(t)} 3 "name: conjI";')
        assert "conjI" in out, f"Expected conjI, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("ft_name", test_ft_name))

    def test_ft_after_step():
        t = f"{prefix}_ft2"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma {prefix}_lem: True by simp";')
        out = send_recv(sock, f'Ir.find_theorems {q(t)} 3 "name: {prefix}_lem";')
        assert f"{prefix}_lem" in out, f"Expected {prefix}_lem, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("ft_after_step", test_ft_after_step))

    def test_ft_pattern():
        t = f"{prefix}_ftp"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        out = send_recv(sock, f'Ir.find_theorems {q(t)} 3 "\\\"(_ + _) + _ = _ + (_ + _)\\\"";')
        assert "add_ac" in out, f"Expected add_ac, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("ft_pattern", test_ft_pattern))

    def test_ft_simp():
        t = f"{prefix}_fts"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        out = send_recv(sock, f'Ir.find_theorems {q(t)} 5 "simp:\\\"_ + _\\\"";')
        assert "theorem" in out or "lemma" in out, f"Expected theorems, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("ft_simp", test_ft_simp))

    def test_ft_solves():
        t = f"{prefix}_ftso"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma test_goal: True";')
        out = send_recv(sock, f'Ir.find_theorems {q(t)} 5 "solves";')
        assert "theorem" in out or "lemma" in out, f"Expected theorems, got:\n{out}"
        send_recv(sock, f'Ir.step {q(t)} "by simp";')
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("ft_solves", test_ft_solves))

    def test_ft_negation():
        t = f"{prefix}_ftn"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        out = send_recv(sock, f'Ir.find_theorems {q(t)} 5 "-name:conjI";')
        assert "conjI" not in out, f"Expected no conjI, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("ft_negation", test_ft_negation))

    # Cleanup: remove the shared REPL
    def cleanup():
        send_recv(sock, f'Ir.remove {q(r)};')
    tests.append(("cleanup", cleanup))

    return tests


def main():
    p = argparse.ArgumentParser(description="Test repl.py TCP server")
    p.add_argument("--isabelle", default=None,
                   help="Path to Isabelle executable (auto-detected if not provided)")
    p.add_argument("--session", default="HOL")
    p.add_argument("--dir", default=None)
    p.add_argument("--server-only", action="store_true",
                   help="Pass --server-only to repl.py")
    p.add_argument("--port", type=int, default=9147,
                   help="Port to probe for an existing repl.py (default: 9147)")
    p.add_argument("--token", default=None,
                   help="Auth token for an existing repl.py (reads IR_AUTH_TOKEN env if not set)")
    p.add_argument("--require-source", action="store_true",
                   help="Fail if source commands are not available")
    p.add_argument("--stress-runs", type=int, default=100,
                   help="Number of core test suite runs in the stress test (default: 100)")
    p.add_argument("--stress-clients", type=int, default=20,
                   help="Max concurrent clients in the stress test (default: 20)")
    p.add_argument("--stress-drop-pct", type=int, default=10,
                   help="Percentage of stress runs that randomly drop the connection (default: 10)")
    args = p.parse_args()

    try:
        args.isabelle = find_isabelle(args.isabelle)
    except RuntimeError as e:
        print(f"{_SYM_FAIL} {e}", file=sys.stderr)
        sys.exit(1)

    repl_py = os.path.join(SCRIPT_DIR, "repl.py")
    proc = None  # only set if we start our own repl.py
    ext_token = args.token or os.environ.get("IR_AUTH_TOKEN", "")

    # Try connecting to an already-running repl.py
    try:
        sock = socket.create_connection(("127.0.0.1", args.port), timeout=2)
        authenticate(sock, ext_token)
        # Quick probe: does it speak the sentinel protocol?
        out = send_recv(sock, 'Ir.help ();', timeout=10)
        if "Ir.init" not in out:
            raise ConnectionError("not an I/R server")
        sock.close()
        port = args.port
        token = ext_token
        print(f"{_SYM_OK} Connected to existing repl.py on port {port}",
              flush=True)
    except (ConnectionRefusedError, ConnectionError, OSError, socket.timeout):
        # No existing server — start our own
        port = find_free_port()
        print(f"{_BOLD}Starting{_RESET} repl.py "
              f"{_DIM}(port={port}, session={args.session}){_RESET}",
              flush=True)
        print(f"  {_SYM_BUSY} loading heap", end="", flush=True)

        cmd = [sys.executable, repl_py,
             "--port", str(port),
             "--isabelle", args.isabelle,
             "--session", args.session]
        if args.dir:
            cmd += ["--dir", args.dir]
        if args.server_only:
            cmd.append("--server-only")

        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )

    t0 = time.time()
    if proc is not None:
        token = ""  # will be read from stdout

    try:
        if proc is not None:
            # Read token from repl.py stdout
            import re
            deadline = time.time() + 300
            while time.time() < deadline:
                line = proc.stdout.readline().decode("utf-8", errors="replace")
                if not line:
                    break
                m = re.search(r'IR_Repl\.token: (\S+)', line)
                if m:
                    token = m.group(1)
                    break
            # Drain stdout in background to avoid blocking
            def _drain():
                for _ in proc.stdout:
                    pass
            threading.Thread(target=_drain, daemon=True).start()

            try:
                sock = connect(port, proc=proc, token=token)
            except RuntimeError:
                elapsed = time.time() - t0
                print(f"{_CLEAR_LINE}  {_SYM_FAIL} server failed to start "
                      f"{_DIM}({elapsed:.1f}s){_RESET}")
                # Show stderr for debugging
                if proc.stderr:
                    err = proc.stderr.read().decode("utf-8", errors="replace")
                    if err.strip():
                        for line in err.strip().splitlines()[:20]:
                            print(f"    {_DIM}{line}{_RESET}")
                if proc.poll() is None:
                    os.killpg(proc.pid, signal.SIGTERM)
                    try:
                        proc.wait(timeout=10)
                    except Exception as e:
                        print(f"    {_DIM}(could not stop server: {e}){_RESET}")
                sys.exit(1)

            elapsed = time.time() - t0
            print(f"{_CLEAR_LINE}  {_SYM_OK} connected "
                  f"{_DIM}({elapsed:.1f}s){_RESET}")
        else:
            sock = connect(port, token=token)

        # -- Core tests (reusable across single/multi-client contexts) --
        print(f"\n{_BOLD}Running{_RESET} single-client tests")

        for name, fn in core_tests(sock, "s"):
            run_test(name, fn)

        # -- Single-client-only tests (expensive / global side effects) --

        def test_source():
            if args.require_source:
                out = send_recv(sock, 'Ir.source "Main" 0 3;')
                assert "Main" in out, f"Expected source output, got:\n{out}"
            else:
                send_recv(sock, 'Ir.source "Main" 0 3 handle ERROR _ => ();')
        run_test("source", test_source)

        def test_load_theory():
            out = send_recv(sock, 'Ir.load_theory "HOL-Library.Multiset";', timeout=300)
            assert "Loaded theory" in out, f"Expected loaded confirmation, got:\n{out}"
            out = send_recv(sock, 'Ir.theories ();')
            assert "Multiset" in out, f"Expected Multiset in theories, got:\n{out}"
            send_recv(sock, 'Ir.init "lt1" ["HOL-Library.Multiset"];')
            out = send_recv(sock, 'Ir.step "lt1" "term \\"{#} :: nat multiset\\"";')
            assert "multiset" in out, f"Expected multiset type, got:\n{out}"
            send_recv(sock, 'Ir.remove "lt1";')
        run_test("load_theory", test_load_theory)

        def test_load_theory_source():
            send_recv(sock, 'Ir.load_theory "HOL-Library.Multiset";', timeout=300)
            out = send_recv(sock, 'Ir.source "HOL-Library.Multiset" 0 5;')
            assert "Multiset" in out, f"Expected Multiset in source, got:\n{out}"
            send_recv(sock, 'Ir.init "lts1" ["HOL-Library.Multiset:4"];')
            out = send_recv(sock, 'Ir.show "lts1";')
            assert "Multiset:4" in out, f"Expected origin Multiset:4, got:\n{out}"
            send_recv(sock, 'Ir.remove "lts1";')
        run_test("load_theory_source", test_load_theory_source)

        def test_load_theory_already_loaded():
            out = send_recv(sock, 'Ir.load_theory "Main";', timeout=20)
            assert "Loaded theory" in out, f"Expected loaded confirmation, got:\n{out}"
        run_test("load_theory_already_loaded", test_load_theory_already_loaded)

        sock.close()

        # -- Multi-client tests --
        print(f"\n{_BOLD}Running{_RESET} multi-client tests")

        def test_concurrent_core_suites():
            """Two clients run the full core test suite concurrently."""
            s1 = connect(port, token=token)
            s2 = connect(port, token=token)
            errors = [None, None]

            def run_suite(idx, s, prefix):
                try:
                    for _name, fn in core_tests(s, prefix):
                        fn()
                except Exception as e:
                    errors[idx] = e

            t1 = threading.Thread(target=run_suite, args=(0, s1, "c1"))
            t2 = threading.Thread(target=run_suite, args=(1, s2, "c2"))
            t1.start()
            t2.start()
            t1.join(timeout=120)
            t2.join(timeout=120)

            for i in range(2):
                if errors[i]:
                    raise errors[i]
            s1.close()
            s2.close()

        def test_client_disconnect():
            """A client disconnects; server stays alive for new clients."""
            s1 = connect(port, token=token)
            send_recv(s1, 'Ir.help ();')
            s1.close()
            time.sleep(0.5)
            s2 = connect(port, token=token)
            out = send_recv(s2, 'Ir.help ();')
            assert "Ir.init" in out
            s2.close()

        for t in [test_concurrent_core_suites, test_client_disconnect]:
            run_test(t.__name__, t)

        # -- Stress tests --
        n_runs = args.stress_runs
        max_clients = args.stress_clients
        drop_pct = args.stress_drop_pct
        print(f"\n{_BOLD}Running{_RESET} stress tests "
              f"{_DIM}({n_runs} runs, {max_clients} max concurrent, "
              f"{drop_pct}% rude disconnects){_RESET}")

        def test_stress():
            """Run N core test suites across a thread pool, verifying all pass."""
            ok = 0
            errs = []
            lock = threading.Lock()

            def run_one(i):
                nonlocal ok
                time.sleep(random.uniform(0, 2))
                s = connect(port, token=token)
                try:
                    for _name, fn in core_tests(s, f"st{i}"):
                        fn()
                    with lock:
                        ok += 1
                except Exception as e:
                    with lock:
                        errs.append((i, e))
                finally:
                    s.close()

            with ThreadPoolExecutor(max_workers=max_clients) as pool:
                futures = [pool.submit(run_one, i) for i in range(n_runs)]
                for f in as_completed(futures):
                    f.result()  # propagate unexpected executor errors

            if errs:
                summary = "; ".join(f"run {i}: {e}" for i, e in errs[:5])
                if len(errs) > 5:
                    summary += f" ... and {len(errs) - 5} more"
                raise AssertionError(
                    f"{len(errs)}/{n_runs} runs failed: {summary}")

        def test_rude_disconnect():
            """Clients randomly drop connections mid-request; server stays healthy."""
            ok = 0
            drops = 0
            errs = []
            lock = threading.Lock()

            def run_one(i):
                nonlocal ok, drops
                should_drop = random.random() < (drop_pct / 100.0)
                time.sleep(random.uniform(0, 2))
                s = connect(port, token=token)
                try:
                    tests = core_tests(s, f"rd{i}")
                    if should_drop and len(tests) > 2:
                        # Run a few tests, then close the socket mid-suite
                        cutoff = random.randint(1, len(tests) - 2)
                        for _name, fn in tests[:cutoff]:
                            fn()
                        s.close()
                        with lock:
                            drops += 1
                        return
                    for _name, fn in tests:
                        fn()
                    with lock:
                        ok += 1
                except (ConnectionResetError, BrokenPipeError, EOFError, OSError):
                    # Expected for rude disconnects
                    with lock:
                        drops += 1
                except Exception as e:
                    with lock:
                        errs.append((i, e))
                finally:
                    try:
                        s.close()
                    except Exception:
                        pass

            with ThreadPoolExecutor(max_workers=max_clients) as pool:
                futures = [pool.submit(run_one, i) for i in range(n_runs)]
                for f in as_completed(futures):
                    f.result()

            if errs:
                summary = "; ".join(f"run {i}: {e}" for i, e in errs[:5])
                if len(errs) > 5:
                    summary += f" ... and {len(errs) - 5} more"
                raise AssertionError(
                    f"{len(errs)}/{n_runs} runs failed ({drops} planned drops): "
                    f"{summary}")

            # After the chaos, verify the server is still healthy
            probe = connect(port, token=token)
            out = send_recv(probe, 'Ir.help ();')
            assert "Ir.init" in out, f"Server unhealthy after stress: {out}"
            probe.close()

        run_test("stress", test_stress)
        run_test("rude_disconnect", test_rude_disconnect)

    finally:
        if proc is not None and proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)

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
