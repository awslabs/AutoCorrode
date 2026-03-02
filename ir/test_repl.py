#!/usr/bin/env python3
"""Test repl.py TCP server: single-client and multi-client.

Assumes the session heap is already built.

Usage: python3 test_repl.py [--isabelle PATH] [--session SESSION] [--dir DIR]
"""
import argparse
import os
import signal
import socket
import subprocess
import sys
import threading
import time

SENTINEL = "<<DONE>>"
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

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


def connect(port, retries=120, delay=2.0, proc=None):
    """Connect to the server, retrying until ready."""
    for i in range(retries):
        if proc is not None and proc.poll() is not None:
            raise RuntimeError(f"Server process exited (rc={proc.returncode})")
        try:
            s = socket.create_connection(("127.0.0.1", port), timeout=5)
            return s
        except (ConnectionRefusedError, OSError):
            time.sleep(delay)
    raise RuntimeError(f"Server not ready after {retries * delay}s")


passed = 0
failed = 0


def run_test(name, fn, prefix=None):
    global passed, failed
    label = f"[{prefix}] {name}" if prefix else name
    print(f"  {_SYM_BUSY} {label}", end="", flush=True)
    t0 = time.time()
    try:
        fn()
        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_OK} {label} {_DIM}({elapsed:.1f}s){_RESET}")
        passed += 1
        return True
    except AssertionError as e:
        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_FAIL} {label} {_DIM}({elapsed:.1f}s){_RESET}")
        for line in str(e).splitlines():
            print(f"    {_DIM}{line}{_RESET}")
        failed += 1
        return False
    except Exception as e:
        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_FAIL} {label}: {type(e).__name__}: {e} "
              f"{_DIM}({elapsed:.1f}s){_RESET}")
        failed += 1
        return False


# ---------------------------------------------------------------------------
# Core single-threaded tests — takes a socket and a fresh REPL id prefix
# ---------------------------------------------------------------------------

def core_tests(sock, rid, require_source=False):
    """Return a list of (name, test_fn) pairs using the given REPL id prefix."""
    tests = []

    def test_help():
        out = send_recv(sock, 'Ir.help ();')
        assert "Ir.init" in out, f"Expected help text, got:\n{out}"
    tests.append(test_help)

    def test_theories():
        out = send_recv(sock, 'Ir.theories ();')
        assert "Main" in out, f"Expected Main theory, got:\n{out}"
    tests.append(test_theories)

    def test_init_show():
        r = f"{rid}_is"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        out = send_recv(sock, f'Ir.show "{r}";')
        assert r in out, f"Expected REPL {r}, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_init_show)

    def test_step():
        r = f"{rid}_st"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        out = send_recv(sock, f'Ir.step "{r}" "lemma dummy: True by simp";')
        assert "theorem dummy: True" in out, f"Unexpected output:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_step)

    def test_state():
        r = f"{rid}_sa"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.step "{r}" "lemma foo: True";')
        out = send_recv(sock, f'Ir.state "{r}" ~1;')
        assert "goal" in out, f"Unexpected state:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_state)

    def test_text():
        r = f"{rid}_tx"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.step "{r}" "lemma True by simp";')
        out = send_recv(sock, f'Ir.text "{r}";')
        assert "lemma" in out, f"Expected lemma text, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_text)

    def test_edit_replay():
        r = f"{rid}_er"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.step "{r}" "lemma True by simp";')
        send_recv(sock, f'Ir.edit "{r}" 0 "lemma True by auto";')
        send_recv(sock, f'Ir.replay "{r}";')
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_edit_replay)

    def test_fork_merge():
        r = f"{rid}_fm"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.step "{r}" "lemma True by simp";')
        send_recv(sock, f'Ir.fork "{r}" "{r}_sub" 0;')
        send_recv(sock, f'Ir.step "{r}_sub" "lemma True by auto";')
        send_recv(sock, f'Ir.merge "{r}_sub";')
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_fork_merge)

    def test_truncate_negative():
        r = f"{rid}_tn"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.step "{r}" "lemma a: True by simp";')
        send_recv(sock, f'Ir.step "{r}" "lemma b: True by simp";')
        send_recv(sock, f'Ir.step "{r}" "lemma c: True by simp";')
        out = send_recv(sock, f'Ir.truncate "{r}" ~1;')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.truncate "{r}" ~1;')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.show "{r}";')
        assert "1 step" in out, f"Expected 1 step, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_truncate_negative)

    def test_truncate_negative_multi():
        r = f"{rid}_tnm"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.step "{r}" "lemma a: True by simp";')
        send_recv(sock, f'Ir.step "{r}" "lemma b: True by simp";')
        send_recv(sock, f'Ir.step "{r}" "lemma c: True by simp";')
        out = send_recv(sock, f'Ir.truncate "{r}" ~2;')
        assert "dropped 2" in out, f"Expected dropped 2, got:\n{out}"
        out = send_recv(sock, f'Ir.show "{r}";')
        assert "1 step" in out, f"Expected 1 step, got:\n{out}"
        out = send_recv(sock, f'Ir.truncate "{r}" ~1;')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.show "{r}";')
        assert "0 step" in out, f"Expected 0 steps, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_truncate_negative_multi)

    def test_back():
        r = f"{rid}_bk"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.step "{r}" "lemma x: True by simp";')
        send_recv(sock, f'Ir.step "{r}" "lemma y: True by simp";')
        out = send_recv(sock, f'Ir.back "{r}";')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.show "{r}";')
        assert "1 step" in out, f"Expected 1 step, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_back)

    def test_back_to_empty():
        r = f"{rid}_bke"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.step "{r}" "lemma z: True by simp";')
        out = send_recv(sock, f'Ir.back "{r}";')
        assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
        out = send_recv(sock, f'Ir.show "{r}";')
        assert "0 step" in out, f"Expected 0 steps, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_back_to_empty)

    def test_repls():
        r = f"{rid}_rp"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        out = send_recv(sock, 'Ir.repls ();')
        assert r in out, f"Expected {r} in repls, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_repls)

    def test_source():
        if require_source:
            out = send_recv(sock, 'Ir.source "Main" 0 3;')
            assert "Main" in out, f"Expected source output, got:\n{out}"
        else:
            send_recv(sock, 'Ir.source "Main" 0 3 handle ERROR _ => ();')
    tests.append(test_source)

    def test_remove():
        r = f"{rid}_rm"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_remove)

    def test_config():
        send_recv(sock, 'Ir.config (fn c => '
                  '{color = false, show_ignored = #show_ignored c, '
                  'full_spans = #full_spans c, '
                  'show_theory_in_source = #show_theory_in_source c, '
                  'auto_replay = #auto_replay c});')
    tests.append(test_config)

    def test_multiline_step():
        r = f"{rid}_ml1"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        out = send_recv(sock, f'Ir.step "{r}" "lemma ml_test: True\\nby simp";')
        assert "ml_test" in out, f"Expected ml_test theorem, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_multiline_step)

    def test_multiline_step_raw_newline():
        r = f"{rid}_ml2"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        out = send_recv(sock, f'Ir.step "{r}" "lemma ml_raw: True\nby simp";')
        assert "ml_raw" in out, f"Expected ml_raw theorem, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_multiline_step_raw_newline)

    def test_ft_name():
        r = f"{rid}_ft1"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        out = send_recv(sock, f'Ir.find_theorems "{r}" 3 "name: conjI";')
        assert "conjI" in out, f"Expected conjI, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_ft_name)

    def test_ft_after_step():
        r = f"{rid}_ft2"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        send_recv(sock, f'Ir.step "{r}" "lemma ft2_lem: True by simp";')
        out = send_recv(sock, f'Ir.find_theorems "{r}" 3 "name: ft2_lem";')
        assert "ft2_lem" in out, f"Expected ft2_lem, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_ft_after_step)

    def test_ft_pattern():
        r = f"{rid}_ftp"
        send_recv(sock, f'Ir.init "{r}" ["Main"];')
        out = send_recv(sock, f'Ir.find_theorems "{r}" 3 "\\\"(_ + _) + _ = _ + (_ + _)\\\"";')
        assert "add_ac" in out, f"Expected add_ac, got:\n{out}"
        send_recv(sock, f'Ir.remove "{r}";')
    tests.append(test_ft_pattern)

    # def test_load_theory():
    #     r = f"{rid}_lt"
    #     out = send_recv(sock, 'Ir.load_theory "HOL-Library.Multiset";', timeout=300)
    #     assert "Loaded theory" in out, f"Expected loaded confirmation, got:\n{out}"
    #     out = send_recv(sock, 'Ir.theories ();')
    #     assert "Multiset" in out, f"Expected Multiset in theories, got:\n{out}"
    #     send_recv(sock, f'Ir.init "{r}" ["HOL-Library.Multiset"];')
    #     out = send_recv(sock, f'Ir.step "{r}" "term \\\"{{#}} :: nat multiset\\\""  ;')
    #     assert "multiset" in out, f"Expected multiset type, got:\n{out}"
    #     send_recv(sock, f'Ir.remove "{r}";')
    # tests.append(test_load_theory)

    # def test_load_theory_source():
    #     r = f"{rid}_lts"
    #     send_recv(sock, 'Ir.load_theory "HOL-Library.Multiset";', timeout=300)
    #     out = send_recv(sock, 'Ir.source "HOL-Library.Multiset" 0 5;')
    #     assert "Multiset" in out, f"Expected Multiset in source, got:\n{out}"
    #     send_recv(sock, f'Ir.init "{r}" ["HOL-Library.Multiset:4"];')
    #     out = send_recv(sock, f'Ir.show "{r}";')
    #     assert "Multiset:4" in out, f"Expected origin Multiset:4, got:\n{out}"
    #     send_recv(sock, f'Ir.remove "{r}";')
    # tests.append(test_load_theory_source)

    # def test_load_theory_already_loaded():
    #     out = send_recv(sock, 'Ir.load_theory "Main";', timeout=20)
    #     assert "Loaded theory" in out, f"Expected loaded confirmation, got:\n{out}"
    # tests.append(test_load_theory_already_loaded)

    def test_sleep():
        """ML-level sleep to verify concurrent execution."""
        out = send_recv(sock, 'OS.Process.sleep (Time.fromMilliseconds 500); val _ = writeln "awake";', timeout=10)
        assert "awake" in out, f"Expected awake, got:\n{out}"
    tests.append(test_sleep)

    return tests


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    global passed, failed

    p = argparse.ArgumentParser(description="Test repl.py TCP server")
    p.add_argument("--isabelle", default=os.environ.get(
        "ISABELLE", "isabelle"))
    p.add_argument("--session", default="HOL")
    p.add_argument("--dir", default=None)
    p.add_argument("--server-only", action="store_true",
                   help="Pass --server-only to repl.py")
    p.add_argument("--port", type=int, default=9147,
                   help="Port to probe for an existing repl.py (default: 9147)")
    p.add_argument("--require-source", action="store_true",
                   help="Fail if source commands are not available")
    p.add_argument("-N", "--concurrency", type=int, default=16,
                   help="Number of concurrent test clients (default: 16)")
    args = p.parse_args()

    repl_py = os.path.join(SCRIPT_DIR, "repl.py")
    proc = None  # only set if we start our own repl.py

    # Try connecting to an already-running repl.py
    try:
        sock = socket.create_connection(("127.0.0.1", args.port), timeout=2)
        sock.sendall(b'Ir.help ();\n')
        buf = b""
        sock.settimeout(10)
        while SENTINEL.encode() not in buf:
            chunk = sock.recv(4096)
            if not chunk:
                raise ConnectionError("closed")
            buf += chunk
        if b"Ir.init" not in buf:
            raise ConnectionError("not an I/R server")
        sock.close()
        port = args.port
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
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )

    t0 = time.time()

    try:
        if proc is not None:
            try:
                sock = connect(port, proc=proc)
            except RuntimeError:
                elapsed = time.time() - t0
                print(f"{_CLEAR_LINE}  {_SYM_FAIL} server failed to start "
                      f"{_DIM}({elapsed:.1f}s){_RESET}")
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
            sock = connect(port)

        # -- Single-client tests (run 1) --
        print(f"\n{_BOLD}Running{_RESET} single-client tests (run 1 — cold)")
        for t in core_tests(sock, "t1", require_source=args.require_source):
            run_test(t.__name__, t)
        sock.close()

        # -- Single-client tests (run 2) --
        sock = connect(port)
        print(f"\n{_BOLD}Running{_RESET} single-client tests (run 2 — warm)")
        for t in core_tests(sock, "t2", require_source=args.require_source):
            run_test(t.__name__, t)
        sock.close()

        # -- Multi-client tests --
        print(f"\n{_BOLD}Running{_RESET} multi-client tests")

        def test_client_disconnect():
            s1 = connect(port)
            send_recv(s1, 'Ir.help ();')
            s1.close()
            time.sleep(0.5)
            s2 = connect(port)
            out = send_recv(s2, 'Ir.help ();')
            assert "Ir.init" in out
            s2.close()

        run_test("test_client_disconnect", test_client_disconnect)

        # -- Concurrent core tests --
        N = args.concurrency
        print(f"\n{_BOLD}Running{_RESET} {N} concurrent test clients")

        conc_errors = []
        conc_lock = threading.Lock()

        def run_client(idx):
            """Run core_tests on a fresh socket with a unique REPL prefix."""
            prefix = f"c{idx}"
            t0 = time.time()
            print(f"  {_SYM_BUSY} [{prefix}] started", flush=True)
            try:
                s = connect(port)
                for t in core_tests(s, prefix,
                                    require_source=args.require_source):
                    run_test(t.__name__, t, prefix=prefix)
                s.close()
                elapsed = time.time() - t0
                print(f"  {_SYM_OK} [{prefix}] done {_DIM}({elapsed:.1f}s){_RESET}",
                      flush=True)
            except Exception as e:
                elapsed = time.time() - t0
                print(f"  {_SYM_FAIL} [{prefix}] failed after {elapsed:.1f}s: "
                      f"{type(e).__name__}: {e}", flush=True)
                with conc_lock:
                    conc_errors.append((idx, e))

        threads = []
        for i in range(N):
            t = threading.Thread(target=run_client, args=(i,))
            threads.append(t)
            t.start()
        for t in threads:
            t.join(timeout=600)
        if conc_errors:
            for idx, e in conc_errors:
                print(f"  {_SYM_FAIL} [c{idx}] {type(e).__name__}: {e}")

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
