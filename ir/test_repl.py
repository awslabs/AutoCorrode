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


def connect(port, retries=120, delay=2.0):
    """Connect to the server, retrying until ready."""
    for i in range(retries):
        try:
            s = socket.create_connection(("127.0.0.1", port), timeout=5)
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


def main():
    p = argparse.ArgumentParser(description="Test repl.py TCP server")
    p.add_argument("--isabelle", default=os.environ.get(
        "ISABELLE", "isabelle"))
    p.add_argument("--session", default="HOL")
    p.add_argument("--dir", default=None)
    p.add_argument("--server-only", action="store_true",
                   help="Pass --server-only to repl.py")
    args = p.parse_args()

    port = find_free_port()
    repl_py = os.path.join(SCRIPT_DIR, "repl.py")

    # Start repl.py
    print(f"{_BOLD}Starting{_RESET} repl.py "
          f"{_DIM}(port={port}, session={args.session}){_RESET}", flush=True)
    print(f"  {_SYM_BUSY} loading heap", end="", flush=True)
    t0 = time.time()

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

    try:
        try:
            sock = connect(port)
        except RuntimeError:
            elapsed = time.time() - t0
            print(f"{_CLEAR_LINE}  {_SYM_FAIL} server failed to start "
                  f"{_DIM}({elapsed:.1f}s){_RESET}")
            # Kill the process
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=10)
            except Exception as e:
                print(f"    {_DIM}(could not stop server: {e}){_RESET}")
            sys.exit(1)

        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_OK} connected "
              f"{_DIM}({elapsed:.1f}s){_RESET}")

        # -- Single-client tests --
        print(f"\n{_BOLD}Running{_RESET} single-client tests")

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
            send_recv(sock, 'Ir.init "t1" ["Main"];')
            out = send_recv(sock, 'Ir.show ();')
            assert "t1" in out, f"Expected REPL t1, got:\n{out}"

        tests.append(test_init_show)

        def test_step():
            out = send_recv(sock, 'Ir.step "lemma dummy: True by simp";')
            assert "theorem dummy: True" in out, f"Unexpected output: \n{out}"

        tests.append(test_step)

        def test_state():
            send_recv(sock, 'Ir.step "lemma foo: True";')
            out = send_recv(sock, 'Ir.state ~1;')
            assert "goal (1 subgoal):", f"Unexpected state:\n{out}"

        tests.append(test_state)

        def test_text():
            out = send_recv(sock, 'Ir.text ();')
            assert "lemma" in out, f"Expected lemma text, got:\n{out}"

        tests.append(test_text)

        def test_edit_replay():
            send_recv(sock, 'Ir.edit 0 "lemma True by auto";')
            send_recv(sock, 'Ir.replay ();')

        tests.append(test_edit_replay)

        def test_fork_focus_merge():
            send_recv(sock, 'Ir.fork "t2" 0;')
            send_recv(sock, 'Ir.focus "t2";')
            send_recv(sock, 'Ir.step "lemma True by auto";')
            send_recv(sock, 'Ir.merge ();')

        tests.append(test_fork_focus_merge)

        def test_truncate_negative():
            send_recv(sock, 'Ir.init "trn" ["Main"];')
            send_recv(sock, 'Ir.step "lemma a: True by simp";')
            send_recv(sock, 'Ir.step "lemma b: True by simp";')
            send_recv(sock, 'Ir.step "lemma c: True by simp";')
            out = send_recv(sock, 'Ir.truncate ~1;')
            assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
            out = send_recv(sock, 'Ir.truncate ~1;')
            assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
            out = send_recv(sock, 'Ir.show ();')
            assert "1 step" in out, f"Expected 1 step, got:\n{out}"
            send_recv(sock, 'Ir.remove "trn";')
        tests.append(test_truncate_negative)

        def test_truncate_negative_multi():
            send_recv(sock, 'Ir.init "trn2" ["Main"];')
            send_recv(sock, 'Ir.step "lemma a: True by simp";')
            send_recv(sock, 'Ir.step "lemma b: True by simp";')
            send_recv(sock, 'Ir.step "lemma c: True by simp";')
            out = send_recv(sock, 'Ir.truncate ~2;')
            assert "dropped 2" in out, f"Expected dropped 2, got:\n{out}"
            out = send_recv(sock, 'Ir.show ();')
            assert "1 step" in out, f"Expected 1 step, got:\n{out}"
            # Now truncate ~1 to empty
            out = send_recv(sock, 'Ir.truncate ~1;')
            assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
            out = send_recv(sock, 'Ir.show ();')
            assert "0 step" in out, f"Expected 0 steps, got:\n{out}"
            send_recv(sock, 'Ir.remove "trn2";')
        tests.append(test_truncate_negative_multi)

        def test_back():
            send_recv(sock, 'Ir.init "bk" ["Main"];')
            send_recv(sock, 'Ir.step "lemma x: True by simp";')
            send_recv(sock, 'Ir.step "lemma y: True by simp";')
            out = send_recv(sock, 'Ir.back ();')
            assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
            out = send_recv(sock, 'Ir.show ();')
            assert "1 step" in out, f"Expected 1 step, got:\n{out}"
            send_recv(sock, 'Ir.remove "bk";')
        tests.append(test_back)

        def test_back_to_empty():
            send_recv(sock, 'Ir.init "bke" ["Main"];')
            send_recv(sock, 'Ir.step "lemma z: True by simp";')
            out = send_recv(sock, 'Ir.back ();')
            assert "dropped 1" in out, f"Expected dropped 1, got:\n{out}"
            out = send_recv(sock, 'Ir.show ();')
            assert "0 step" in out, f"Expected 0 steps, got:\n{out}"
            send_recv(sock, 'Ir.remove "bke";')
        tests.append(test_back_to_empty)

        def test_repls():
            out = send_recv(sock, 'Ir.repls ();')
            assert "t1" in out, f"Expected t1 in repls, got:\n{out}"

        tests.append(test_repls)

        def test_source():
            send_recv(sock, 'Ir.source "Main" 0 3 handle ERROR _ => ();')

        tests.append(test_source)

        def test_remove():
            send_recv(sock, 'Ir.init "tmp" ["Main"];')
            send_recv(sock, 'Ir.remove "tmp";')

        tests.append(test_remove)

        def test_config():
            send_recv(sock, 'Ir.config (fn c => '
                      '{color = false, show_ignored = #show_ignored c, '
                      'full_spans = #full_spans c, '
                      'show_theory_in_source = #show_theory_in_source c, '
                      'auto_replay = #auto_replay c});')

        tests.append(test_config)

        def test_multiline_step():
            """Multi-line Isar text sent as escaped ML string (via MCP path)."""
            send_recv(sock, 'Ir.init "ml1" ["Main"];')
            # Multi-line: lemma + proof on separate lines, escaped as ML string
            out = send_recv(sock, 'Ir.step "lemma ml_test: True\\nby simp";')
            assert "ml_test" in out, f"Expected ml_test theorem, got:\n{out}"
            send_recv(sock, 'Ir.remove "ml1";')

        tests.append(test_multiline_step)

        def test_multiline_step_raw_newline():
            """Multi-line Isar text with raw newline (TCP multi-line accumulation)."""
            send_recv(sock, 'Ir.init "ml2" ["Main"];')
            # Raw newline: TCP handler accumulates lines until ;
            out = send_recv(sock, 'Ir.step "lemma ml_raw: True\nby simp";')
            assert "ml_raw" in out, f"Expected ml_raw theorem, got:\n{out}"
            send_recv(sock, 'Ir.remove "ml2";')

        tests.append(test_multiline_step_raw_newline)

        # -- find_theorems tests --
        def test_ft_single_theory_immediate_library():
            send_recv(sock, 'Ir.init "ft1" ["Main"];')
            out = send_recv(sock, 'Ir.find_theorems 3 "name: conjI";')
            assert "conjI" in out, f"Expected conjI, got:\n{out}"
            send_recv(sock, 'Ir.remove "ft1";')

        tests.append(test_ft_single_theory_immediate_library)

        def test_ft_single_theory_after_lemma_library():
            send_recv(sock, 'Ir.init "ft2" ["Main"];')
            send_recv(sock, 'Ir.step "lemma ft2_lem: True by simp";')
            out = send_recv(sock, 'Ir.find_theorems 3 "name: conjI";')
            assert "conjI" in out, f"Expected conjI, got:\n{out}"
            send_recv(sock, 'Ir.remove "ft2";')

        tests.append(test_ft_single_theory_after_lemma_library)

        def test_ft_single_theory_after_lemma_repl_fact():
            send_recv(sock, 'Ir.init "ft3" ["Main"];')
            send_recv(sock, 'Ir.step "lemma ft3_lem: True by simp";')
            out = send_recv(sock, 'Ir.find_theorems 3 "name: ft3_lem";')
            assert "ft3_lem" in out, f"Expected ft3_lem, got:\n{out}"
            send_recv(sock, 'Ir.remove "ft3";')

        tests.append(test_ft_single_theory_after_lemma_repl_fact)

        def test_ft_multi_theory_immediate_library():
            send_recv(sock, 'Ir.init "ft4" ["Main", "Complex_Main"];')
            out = send_recv(sock, 'Ir.find_theorems 3 "name: conjI";')
            assert "conjI" in out, f"Expected conjI, got:\n{out}"
            send_recv(sock, 'Ir.remove "ft4";')

        tests.append(test_ft_multi_theory_immediate_library)

        def test_ft_multi_theory_after_lemma_repl_fact():
            send_recv(sock, 'Ir.init "ft5" ["Main", "Complex_Main"];')
            send_recv(sock, 'Ir.step "lemma ft5_lem: True by simp";')
            out = send_recv(sock, 'Ir.find_theorems 3 "name: ft5_lem";')
            assert "ft5_lem" in out, f"Expected ft5_lem, got:\n{out}"
            send_recv(sock, 'Ir.remove "ft5";')

        tests.append(test_ft_multi_theory_after_lemma_repl_fact)

        def test_load_theory():
            """load_theory loads a theory not in the heap, making it available for init."""
            out = send_recv(sock, 'Ir.load_theory "HOL-Library.Multiset";', timeout=300)
            assert "Loaded theory" in out, f"Expected loaded confirmation, got:\n{out}"
            # It should now appear in theories listing
            out = send_recv(sock, 'Ir.theories ();')
            assert "Multiset" in out, f"Expected Multiset in theories, got:\n{out}"
            # And we should be able to init a REPL on it
            send_recv(sock, 'Ir.init "lt1" ["HOL-Library.Multiset"];')
            out = send_recv(sock, 'Ir.step "term \\"{#} :: nat multiset\\"";')
            assert "multiset" in out, f"Expected multiset type, got:\n{out}"
            send_recv(sock, 'Ir.remove "lt1";')

        tests.append(test_load_theory)

        def test_load_theory_already_loaded():
            """load_theory on an already-loaded theory is a no-op."""
            out = send_recv(sock, 'Ir.load_theory "Main";', timeout=20)
            assert "Loaded theory" in out, f"Expected loaded confirmation, got:\n{out}"

        tests.append(test_load_theory_already_loaded)

        for t in tests:
            run_test(t.__name__, t)

        sock.close()

        # Cleanup from single-client tests
        cleanup_sock = connect(port)
        send_recv(cleanup_sock, 'Ir.remove "t1";')
        cleanup_sock.close()

        # -- Multi-client tests --
        print(f"\n{_BOLD}Running{_RESET} multi-client tests")

        def test_concurrent_clients():
            """Two clients send commands concurrently; both get valid responses."""
            s1 = connect(port)
            s2 = connect(port)
            results = [None, None]
            errors = [None, None]

            def client(idx, sock, cmd):
                try:
                    results[idx] = send_recv(sock, cmd)
                except Exception as e:
                    errors[idx] = e

            send_recv(s1, 'Ir.init "mc1" ["Main"];')
            send_recv(s1, 'Ir.init "mc2" ["Main"];')

            t1 = threading.Thread(target=client,
                                  args=(0, s1, 'Ir.focus "mc1"; Ir.theories ();'))
            t2 = threading.Thread(target=client,
                                  args=(1, s2, 'Ir.focus "mc2"; Ir.theories ();'))
            t1.start()
            t2.start()
            t1.join(timeout=60)
            t2.join(timeout=60)

            for i in range(2):
                if errors[i]:
                    raise errors[i]
                assert results[i] is not None, f"Client {i} got no result"

            send_recv(s1, 'Ir.remove "mc1";')
            send_recv(s1, 'Ir.remove "mc2";')
            s1.close()
            s2.close()

        def test_client_disconnect():
            """A client disconnects; server stays alive for new clients."""
            s1 = connect(port)
            send_recv(s1, 'Ir.help ();')
            s1.close()
            time.sleep(0.5)
            s2 = connect(port)
            out = send_recv(s2, 'Ir.help ();')
            assert "Ir.init" in out
            s2.close()

        for t in [test_concurrent_clients, test_client_disconnect]:
            run_test(t.__name__, t)

    finally:
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
