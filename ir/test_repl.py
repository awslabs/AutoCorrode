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


def send_recv(sock, cmd):
    """Send a command and read until sentinel."""
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
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )

    try:
        try:
            sock = connect(port)
        except RuntimeError:
            elapsed = time.time() - t0
            print(f"{_CLEAR_LINE}  {_SYM_FAIL} server failed to start "
                  f"{_DIM}({elapsed:.1f}s){_RESET}")
            # Kill the process so we can drain its output
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                out, _ = proc.communicate(timeout=10)
                if out:
                    print(f"  Server output (last 3000 chars):")
                    for line in out.decode("utf-8", errors="replace")[-3000:].splitlines():
                        print(f"    {_DIM}{line}{_RESET}")
            except Exception as e:
                print(f"    {_DIM}(could not read output: {e}){_RESET}")
            sys.exit(1)

        elapsed = time.time() - t0
        print(f"{_CLEAR_LINE}  {_SYM_OK} connected "
              f"{_DIM}({elapsed:.1f}s){_RESET}")

        # -- Single-client tests --
        print(f"\n{_BOLD}Running{_RESET} single-client tests")

        def test_help():
            out = send_recv(sock, 'Explore.help ();')
            assert "Explore.init" in out, f"Expected help text, got:\n{out}"

        def test_theories():
            out = send_recv(sock, 'Explore.theories ();')
            assert "Main" in out, f"Expected Main theory, got:\n{out}"

        def test_init_show():
            send_recv(sock, 'Explore.init "t1" "Main";')
            out = send_recv(sock, 'Explore.show ();')
            assert "t1" in out, f"Expected REPL t1, got:\n{out}"

        def test_step():
            out = send_recv(sock, 'Explore.step "lemma dummy: True by simp";')
            assert "theorem dummy: True" in out, f"Unexpected output: \n{out}"

        def test_state():
            send_recv(sock, 'Explore.step "lemma foo: True";')
            out = send_recv(sock, 'Explore.state ~1;')
            assert "goal (1 subgoal):", f"Unexpected state:\n{out}"

        def test_text():
            out = send_recv(sock, 'Explore.text ();')
            assert "lemma" in out, f"Expected lemma text, got:\n{out}"

        def test_edit_replay():
            send_recv(sock, 'Explore.edit 0 "lemma True by auto";')
            send_recv(sock, 'Explore.replay ();')

        def test_fork_focus_merge():
            send_recv(sock, 'Explore.fork "t2" 0;')
            send_recv(sock, 'Explore.focus "t2";')
            send_recv(sock, 'Explore.step "lemma True by auto";')
            send_recv(sock, 'Explore.merge ();')

        def test_repls():
            out = send_recv(sock, 'Explore.repls ();')
            assert "t1" in out, f"Expected t1 in repls, got:\n{out}"

        def test_source():
            send_recv(sock, 'Explore.source "Main" 0 3 handle ERROR _ => ();')

        def test_remove():
            send_recv(sock, 'Explore.init "tmp" "Main";')
            send_recv(sock, 'Explore.remove "tmp";')

        def test_config():
            send_recv(sock, 'Explore.config (fn c => '
                      '{color = false, show_ignored = #show_ignored c, '
                      'full_spans = #full_spans c, '
                      'show_theory_in_source = #show_theory_in_source c, '
                      'auto_replay = #auto_replay c});')

        def test_multiline_step():
            """Multi-line Isar text sent as escaped ML string (via MCP path)."""
            send_recv(sock, 'Explore.init "ml1" "Main";')
            # Multi-line: lemma + proof on separate lines, escaped as ML string
            out = send_recv(sock, 'Explore.step "lemma ml_test: True\\nby simp";')
            assert "ml_test" in out, f"Expected ml_test theorem, got:\n{out}"
            send_recv(sock, 'Explore.remove "ml1";')

        def test_multiline_step_raw_newline():
            """Multi-line Isar text with raw newline (TCP multi-line accumulation)."""
            send_recv(sock, 'Explore.init "ml2" "Main";')
            # Raw newline: TCP handler accumulates lines until ;
            out = send_recv(sock, 'Explore.step "lemma ml_raw: True\nby simp";')
            assert "ml_raw" in out, f"Expected ml_raw theorem, got:\n{out}"
            send_recv(sock, 'Explore.remove "ml2";')

        for t in [test_help, test_theories, test_init_show, test_step,
                  test_state, test_text, test_edit_replay, test_fork_focus_merge,
                  test_repls, test_source, test_remove, test_config,
                  test_multiline_step, test_multiline_step_raw_newline]:
            run_test(t.__name__, t)

        sock.close()

        # Cleanup from single-client tests
        cleanup_sock = connect(port)
        send_recv(cleanup_sock, 'Explore.remove "t1";')
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

            send_recv(s1, 'Explore.init "mc1" "Main";')
            send_recv(s1, 'Explore.init "mc2" "Main";')

            t1 = threading.Thread(target=client,
                                  args=(0, s1, 'Explore.focus "mc1"; Explore.theories ();'))
            t2 = threading.Thread(target=client,
                                  args=(1, s2, 'Explore.focus "mc2"; Explore.theories ();'))
            t1.start()
            t2.start()
            t1.join(timeout=60)
            t2.join(timeout=60)

            for i in range(2):
                if errors[i]:
                    raise errors[i]
                assert results[i] is not None, f"Client {i} got no result"

            send_recv(s1, 'Explore.remove "mc1";')
            send_recv(s1, 'Explore.remove "mc2";')
            s1.close()
            s2.close()

        def test_client_disconnect():
            """A client disconnects; server stays alive for new clients."""
            s1 = connect(port)
            send_recv(s1, 'Explore.help ();')
            s1.close()
            time.sleep(0.5)
            s2 = connect(port)
            out = send_recv(s2, 'Explore.help ();')
            assert "Explore.init" in out
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
