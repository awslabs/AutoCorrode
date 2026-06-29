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

    def test_truncate_deep_descendants():
        """Truncate must remove grandchildren, not just direct children."""
        t = f"{prefix}_tdd"
        s = f"{prefix}_tdd_s"
        u = f"{prefix}_tdd_t"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma a: True by simp";')
        send_recv(sock, f'Ir.fork {q(t)} {q(s)} 1;')
        send_recv(sock, f'Ir.step {q(s)} "lemma b: True by simp";')
        send_recv(sock, f'Ir.fork {q(s)} {q(u)} 1;')
        # u is a grandchild of t (t -> s -> u)
        # Truncate t to step 0 — s (forked at state 1) becomes orphaned,
        # and u (a descendant of s) should also be removed.
        send_recv(sock, f'Ir.truncate {q(t)} ~1;')
        out = send_recv(sock, 'Ir.repls ();')
        assert s not in out, f"Expected {s} removed, got:\n{out}"
        assert u not in out, f"Expected {u} (grandchild) removed, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("truncate_deep_descendants", test_truncate_deep_descendants))

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

    def test_pin_basic():
        """Pin a REPL, step, re-pin."""
        t = f"{prefix}_pin1"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma True by simp";')
        out = send_recv(sock, f'Ir.pin {q(t)};')
        assert "Pinned" in out, f"Expected Pinned, got:\n{out}"
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "pinned" in out, f"Expected pinned in show, got:\n{out}"
        send_recv(sock, f'Ir.step {q(t)} "lemma True by simp";')
        out = send_recv(sock, f'Ir.pin {q(t)};')
        assert "Pinned" in out, f"Expected Pinned on re-pin, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("pin_basic", test_pin_basic))

    def test_pin_stale_on_step():
        """Pin becomes stale after stepping."""
        t = f"{prefix}_pin2"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.pin {q(t)};')
        send_recv(sock, f'Ir.step {q(t)} "lemma True by simp";')
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "stale" in out, f"Expected stale in show, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("pin_stale_on_step", test_pin_stale_on_step))

    def test_pin_repin_clears_stale():
        """Re-pinning clears staleness."""
        t = f"{prefix}_pin3"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.pin {q(t)};')
        send_recv(sock, f'Ir.step {q(t)} "lemma True by simp";')
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "stale" in out, f"Expected stale, got:\n{out}"
        send_recv(sock, f'Ir.pin {q(t)};')
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "stale" not in out, f"Expected no stale after re-pin, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("pin_repin_clears_stale", test_pin_repin_clears_stale))

    def test_pin_during_proof():
        """Pinning while in a proof state should fail."""
        t = f"{prefix}_pinpf"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma True";')
        out = send_recv(sock, f'Ir.pin {q(t)} handle ERROR msg => writeln ("ERR: " ^ msg);')
        assert "ERR:" in out and "proof state" in out, \
            f"Expected proof state error, got:\n{out}"
        send_recv(sock, f'Ir.step {q(t)} "by simp";')
        # After closing the proof, pin should succeed
        out = send_recv(sock, f'Ir.pin {q(t)};')
        assert "Pinned" in out, f"Expected Pinned after proof, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("pin_during_proof", test_pin_during_proof))

    def test_unpin():
        """Unpin removes the pin."""
        t = f"{prefix}_pin4"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.pin {q(t)};')
        out = send_recv(sock, f'Ir.unpin {q(t)};')
        assert "Unpinned" in out, f"Expected Unpinned, got:\n{out}"
        out = send_recv(sock, f'Ir.show {q(t)};')
        assert "pinned" not in out, f"Expected no pin in show, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("unpin", test_unpin))

    def test_unpin_nonexistent():
        """Unpin a REPL that has no pin."""
        t = f"{prefix}_pin5"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        out = send_recv(sock, f'Ir.unpin {q(t)} handle ERROR msg => writeln ("ERR: " ^ msg);')
        assert "ERR:" in out and "not pinned" in out, \
            f"Expected error about not pinned, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("unpin_nonexistent", test_unpin_nonexistent))

    def test_init_from_pin():
        """Init a new REPL from a pinned REPL."""
        src = f"{prefix}_pis"
        dst = f"{prefix}_pid"
        send_recv(sock, f'Ir.init {q(src)} ["Main"];')
        send_recv(sock, f'Ir.step {q(src)} "lemma {prefix}_pinlem: True by simp";')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.init {q(dst)} ["pin@{src}"];')
        out = send_recv(sock, f'Ir.find_theorems {q(dst)} 3 "name: {prefix}_pinlem";')
        assert f"{prefix}_pinlem" in out, \
            f"Expected {prefix}_pinlem visible in dst, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(dst)};')
        send_recv(sock, f'Ir.remove {q(src)};')
    tests.append(("init_from_pin", test_init_from_pin))

    def test_init_from_pin_mixed():
        """Init from a pinned REPL plus a regular theory."""
        src = f"{prefix}_pms"
        dst = f"{prefix}_pmd"
        send_recv(sock, f'Ir.init {q(src)} ["Main"];')
        send_recv(sock, f'Ir.step {q(src)} "lemma {prefix}_pmlem: True by simp";')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.init {q(dst)} ["pin@{src}", "Main"];')
        out = send_recv(sock, f'Ir.find_theorems {q(dst)} 3 "name: {prefix}_pmlem";')
        assert f"{prefix}_pmlem" in out, \
            f"Expected {prefix}_pmlem visible in dst, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(dst)};')
        send_recv(sock, f'Ir.remove {q(src)};')
    tests.append(("init_from_pin_mixed", test_init_from_pin_mixed))

    def test_init_from_stale_pin_rejected():
        """Init from a stale pin should fail."""
        src = f"{prefix}_pss"
        dst = f"{prefix}_psd"
        send_recv(sock, f'Ir.init {q(src)} ["Main"];')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.step {q(src)} "lemma True by simp";')
        out = send_recv(sock, f'Ir.init {q(dst)} ["pin@{src}"] '
                        f'handle ERROR msg => writeln ("ERR: " ^ msg);')
        assert "ERR:" in out and "stale" in out, \
            f"Expected stale error, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(src)};')
    tests.append(("init_from_stale_pin_rejected", test_init_from_stale_pin_rejected))

    def test_init_from_pin_chain():
        """Chain: A -> pin -> B -> step -> pin B -> C from pin@B."""
        a = f"{prefix}_pca"
        b = f"{prefix}_pcb"
        c = f"{prefix}_pcc"
        send_recv(sock, f'Ir.init {q(a)} ["Main"];')
        send_recv(sock, f'Ir.step {q(a)} "lemma {prefix}_pca_lem: True by simp";')
        send_recv(sock, f'Ir.pin {q(a)};')
        send_recv(sock, f'Ir.init {q(b)} ["pin@{a}"];')
        send_recv(sock, f'Ir.step {q(b)} "lemma {prefix}_pcb_lem: True by simp";')
        send_recv(sock, f'Ir.pin {q(b)};')
        send_recv(sock, f'Ir.init {q(c)} ["pin@{b}"];')
        out = send_recv(sock, f'Ir.find_theorems {q(c)} 3 "name: {prefix}_pca_lem";')
        assert f"{prefix}_pca_lem" in out, \
            f"Expected {prefix}_pca_lem visible in C, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(c)};')
        send_recv(sock, f'Ir.remove {q(b)};')
        send_recv(sock, f'Ir.remove {q(a)};')
    tests.append(("init_from_pin_chain", test_init_from_pin_chain))

    def test_init_from_multi_pins():
        """Init from two pinned REPLs, lemmas from both visible."""
        a = f"{prefix}_mpa"
        b = f"{prefix}_mpb"
        dst = f"{prefix}_mpd"
        send_recv(sock, f'Ir.init {q(a)} ["Main"];')
        send_recv(sock, f'Ir.step {q(a)} "lemma {prefix}_mpa_lem: True by simp";')
        send_recv(sock, f'Ir.pin {q(a)};')
        send_recv(sock, f'Ir.init {q(b)} ["Main"];')
        send_recv(sock, f'Ir.step {q(b)} "lemma {prefix}_mpb_lem: True by simp";')
        send_recv(sock, f'Ir.pin {q(b)};')
        send_recv(sock, f'Ir.init {q(dst)} ["pin@{a}", "pin@{b}"];')
        out_a = send_recv(sock, f'Ir.find_theorems {q(dst)} 3 "name: {prefix}_mpa_lem";')
        assert f"{prefix}_mpa_lem" in out_a, \
            f"Expected {prefix}_mpa_lem visible in dst, got:\n{out_a}"
        out_b = send_recv(sock, f'Ir.find_theorems {q(dst)} 3 "name: {prefix}_mpb_lem";')
        assert f"{prefix}_mpb_lem" in out_b, \
            f"Expected {prefix}_mpb_lem visible in dst, got:\n{out_b}"
        send_recv(sock, f'Ir.remove {q(dst)};')
        send_recv(sock, f'Ir.remove {q(b)};')
        send_recv(sock, f'Ir.remove {q(a)};')
    tests.append(("init_from_multi_pins", test_init_from_multi_pins))

    def test_unpin_with_dependent_rejected():
        """Unpin should fail if another REPL depends on the pin."""
        src = f"{prefix}_pds"
        dst = f"{prefix}_pdd"
        send_recv(sock, f'Ir.init {q(src)} ["Main"];')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.init {q(dst)} ["pin@{src}"];')
        out = send_recv(sock, f'Ir.unpin {q(src)} '
                        f'handle ERROR msg => writeln ("ERR: " ^ msg);')
        assert "ERR:" in out and "depend" in out, \
            f"Expected dependency error, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(dst)};')
        send_recv(sock, f'Ir.unpin {q(src)};')
        send_recv(sock, f'Ir.remove {q(src)};')
    tests.append(("unpin_with_dependent_rejected", test_unpin_with_dependent_rejected))

    def test_remove_pinned_with_dependent():
        """Remove should fail if the REPL has a pin with dependents."""
        src = f"{prefix}_prs"
        dst = f"{prefix}_prd"
        send_recv(sock, f'Ir.init {q(src)} ["Main"];')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.init {q(dst)} ["pin@{src}"];')
        out = send_recv(sock, f'Ir.remove {q(src)} '
                        f'handle ERROR msg => writeln ("ERR: " ^ msg);')
        assert "ERR:" in out and "depend" in out, \
            f"Expected dependency error, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(dst)};')
        send_recv(sock, f'Ir.remove {q(src)};')
    tests.append(("remove_pinned_with_dependent", test_remove_pinned_with_dependent))

    def test_rebase_pin_noop():
        """Rebase when pins are up to date is a no-op."""
        src = f"{prefix}_rn_s"
        dst = f"{prefix}_rn_d"
        send_recv(sock, f'Ir.init {q(src)} ["Main"];')
        send_recv(sock, f'Ir.step {q(src)} "lemma True by simp";')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.init {q(dst)} ["pin@{src}"];')
        send_recv(sock, f'Ir.step {q(dst)} "lemma True by simp";')
        out = send_recv(sock, f'Ir.rebase {q(dst)};')
        assert "up to date" in out, f"Expected up to date, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(dst)};')
        send_recv(sock, f'Ir.remove {q(src)};')
    tests.append(("rebase_pin_noop", test_rebase_pin_noop))

    def test_rebase_pin_updated():
        """Rebase replays steps on updated pin."""
        src = f"{prefix}_ru_s"
        dst = f"{prefix}_ru_d"
        send_recv(sock, f'Ir.init {q(src)} ["Main"];')
        send_recv(sock, f'Ir.step {q(src)} "lemma {prefix}_ru_a: True by simp";')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.init {q(dst)} ["pin@{src}"];')
        send_recv(sock, f'Ir.step {q(dst)} "lemma {prefix}_ru_b: True by simp";')
        # Update source and re-pin
        send_recv(sock, f'Ir.step {q(src)} "lemma {prefix}_ru_c: True by simp";')
        send_recv(sock, f'Ir.pin {q(src)};')
        out = send_recv(sock, f'Ir.rebase {q(dst)};')
        assert "stale" in out, f"Expected stale, got:\n{out}"
        # Steps are stale; replay to re-execute them
        send_recv(sock, f'Ir.replay {q(dst)};')
        # dst should see both its own lemma and the new one from src
        out_b = send_recv(sock, f'Ir.find_theorems {q(dst)} 3 "name: {prefix}_ru_b";')
        assert f"{prefix}_ru_b" in out_b, \
            f"Expected {prefix}_ru_b after rebase+replay, got:\n{out_b}"
        out_c = send_recv(sock, f'Ir.find_theorems {q(dst)} 3 "name: {prefix}_ru_c";')
        assert f"{prefix}_ru_c" in out_c, \
            f"Expected {prefix}_ru_c after rebase+replay, got:\n{out_c}"
        send_recv(sock, f'Ir.remove {q(dst)};')
        send_recv(sock, f'Ir.remove {q(src)};')
    tests.append(("rebase_pin_updated", test_rebase_pin_updated))

    def test_rebase_pin_stale_error():
        """Rebase fails if pin is stale (not re-pinned)."""
        src = f"{prefix}_rs_s"
        dst = f"{prefix}_rs_d"
        send_recv(sock, f'Ir.init {q(src)} ["Main"];')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.init {q(dst)} ["pin@{src}"];')
        send_recv(sock, f'Ir.step {q(src)} "lemma True by simp";')
        out = send_recv(sock, f'Ir.rebase {q(dst)} '
                        f'handle ERROR msg => writeln ("ERR: " ^ msg);')
        assert "ERR:" in out and "stale" in out, \
            f"Expected stale error, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(dst)};')
        send_recv(sock, f'Ir.remove {q(src)};')
    tests.append(("rebase_pin_stale_error", test_rebase_pin_stale_error))

    def test_rebase_marks_own_pin_stale():
        """Rebasing a pinned REPL marks its own pin stale."""
        src = f"{prefix}_rps_s"
        mid = f"{prefix}_rps_m"
        send_recv(sock, f'Ir.init {q(src)} ["Main"];')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.init {q(mid)} ["pin@{src}"];')
        send_recv(sock, f'Ir.step {q(mid)} "lemma True by simp";')
        send_recv(sock, f'Ir.pin {q(mid)};')
        out = send_recv(sock, f'Ir.show {q(mid)};')
        assert "stale" not in out, f"Expected pin not stale before rebase, got:\n{out}"
        # Update src, re-pin, rebase mid
        send_recv(sock, f'Ir.step {q(src)} "lemma True by simp";')
        send_recv(sock, f'Ir.pin {q(src)};')
        send_recv(sock, f'Ir.rebase {q(mid)};')
        out = send_recv(sock, f'Ir.show {q(mid)};')
        assert "stale" in out, f"Expected pin stale after rebase, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(mid)};')
        send_recv(sock, f'Ir.remove {q(src)};')
    tests.append(("rebase_marks_own_pin_stale", test_rebase_marks_own_pin_stale))

    def test_rebase_no_pins_is_noop():
        """Rebase on a REPL with no pins is a no-op."""
        t = f"{prefix}_rnp"
        send_recv(sock, f'Ir.init {q(t)} ["Main"];')
        send_recv(sock, f'Ir.step {q(t)} "lemma True by simp";')
        out = send_recv(sock, f'Ir.rebase {q(t)};')
        assert "up to date" in out, f"Expected up to date, got:\n{out}"
        send_recv(sock, f'Ir.remove {q(t)};')
    tests.append(("rebase_no_pins_is_noop", test_rebase_no_pins_is_noop))

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

        def test_segment_init_mid_proof_qed():
            """Regression test for AutoCorrode#230: Ir.init at a
            heap-recorded mid-proof segment, stepping through qed must
            register the theorem.

            Background: when a theory is built with record_theories=true AND
            parallel proofs enabled, Toplevel.element_result forks each
            lemma body via Proof.future_proof, which rewrites the goal's
            after_qed to a stub that does not call Local_Theory.notes_kind.
            Every segment recorded inside that future captures the stubbed
            Proof.state, so a naive qed against such a state runs the stub
            and the theorem is never registered.  The splicer compensates
            by substituting the heap-recorded post-qed state at the
            proof-exit transition.

            Uses HOL-Library.Multiset (already loaded by test_load_theory).
            Lemma `in_countE` has segments:
              183: lemma in_countE (declaration)
              185: proof -
              187: from assms (mid-proof)
              ...
              207: qed

            Init at seg 187 (mid-proof, chain mode after `from assms`),
            step the remainder through qed, assert `thm in_countE` resolves.
            """
            send_recv(sock,
                      'Ir.init "seg_bug" ["HOL-Library.Multiset:187"];')
            send_recv(sock, 'Ir.step "seg_bug" '
                      '"have \\"count M x > 0\\" by simp";', timeout=10)
            send_recv(sock, 'Ir.step "seg_bug" '
                      '"then obtain n where \\"count M x = Suc n\\" '
                      'using gr0_conv_Suc by blast";', timeout=10)
            send_recv(sock, 'Ir.step "seg_bug" '
                      '"with that show thesis .";', timeout=10)
            qed_out = send_recv(sock, 'Ir.step "seg_bug" "qed";',
                                timeout=10)
            thm_out = send_recv(sock,
                                'Ir.step "seg_bug" "thm in_countE";',
                                timeout=10)
            send_recv(sock, 'Ir.remove "seg_bug";')
            assert "Undefined fact" not in thm_out, (
                "REGRESSION: Ir.init at a heap-recorded mid-proof segment "
                "(HOL-Library.Multiset:187), then stepping through qed, "
                "did not register the theorem.  The splicer should have "
                "substituted the recorded post-qed state.  "
                f"qed output: {qed_out!r}.  thm output: {thm_out!r}")
        run_test("segment_init_mid_proof_qed",
                 test_segment_init_mid_proof_qed)

        def test_segment_init_mid_proof_oops():
            """oops at the outermost proof exit must NOT splice in the
            recorded post-qed state — it should leave the theorem unregistered.
            """
            def thm_resolves(repl_id, name):
                out = send_recv(sock,
                                f'Ir.step {q(repl_id)} "thm {name}";',
                                timeout=10)
                return "Undefined fact" not in out

            send_recv(sock,
                      'Ir.init "seg_oops" ["HOL-Library.Multiset:187"];')
            # Step the body but use oops to abandon, not qed.
            send_recv(sock, 'Ir.step "seg_oops" '
                      '"have \\"count M x > 0\\" by simp";', timeout=10)
            send_recv(sock, 'Ir.step "seg_oops" "oops";', timeout=10)
            resolves = thm_resolves("seg_oops", "in_countE")
            send_recv(sock, 'Ir.remove "seg_oops";')
            assert not resolves, (
                "BUG: after oops at mid-proof segment init, in_countE was "
                "spuriously registered. Splice should have been disarmed by "
                "the oops transition.")
        run_test("segment_init_mid_proof_oops",
                 test_segment_init_mid_proof_oops)

        def test_segment_init_mid_proof_subproof():
            """A sub-proof inside the body (have ... proof ... qed) must
            not consume the splice; the splice should only fire on the
            outermost qed.  Init at seg 185 (post `proof -`, before chain)
            so we can interleave a sub-proof cleanly.
            """
            def thm_resolves(repl_id, name):
                out = send_recv(sock,
                                f'Ir.step {q(repl_id)} "thm {name}";',
                                timeout=10)
                return "Undefined fact" not in out

            send_recv(sock,
                      'Ir.init "seg_sub" ["HOL-Library.Multiset:185"];')
            # First a structured sub-proof for an irrelevant fact — its
            # internal qed must NOT consume the splice.
            send_recv(sock, 'Ir.step "seg_sub" '
                      '"have helper: \\"True\\" proof show ?thesis '
                      'by simp qed";', timeout=30)
            # Now the actual proof body.
            send_recv(sock, 'Ir.step "seg_sub" '
                      '"from assms have \\"count M x > 0\\" by simp";', timeout=10)
            send_recv(sock, 'Ir.step "seg_sub" '
                      '"then obtain n where \\"count M x = Suc n\\" '
                      'using gr0_conv_Suc by blast";', timeout=10)
            send_recv(sock, 'Ir.step "seg_sub" '
                      '"with that show thesis .";', timeout=10)
            send_recv(sock, 'Ir.step "seg_sub" "qed";', timeout=10)
            resolves = thm_resolves("seg_sub", "in_countE")
            send_recv(sock, 'Ir.remove "seg_sub";')
            assert resolves, (
                "BUG: outer qed after a structured sub-proof failed to "
                "splice. The inner qed must not consume the splice.")
        run_test("segment_init_mid_proof_subproof",
                 test_segment_init_mid_proof_subproof)

        def test_segment_init_mid_proof_truncate_replay():
            """Truncate past the spliced qed and step a different finisher;
            the splice must re-arm and the new qed must register the theorem.
            """
            def thm_resolves(repl_id, name):
                out = send_recv(sock,
                                f'Ir.step {q(repl_id)} "thm {name}";',
                                timeout=10)
                return "Undefined fact" not in out

            send_recv(sock,
                      'Ir.init "seg_tr" ["HOL-Library.Multiset:187"];')
            send_recv(sock, 'Ir.step "seg_tr" '
                      '"have \\"count M x > 0\\" by simp";', timeout=10)
            send_recv(sock, 'Ir.step "seg_tr" '
                      '"then obtain n where \\"count M x = Suc n\\" '
                      'using gr0_conv_Suc by blast";', timeout=10)
            send_recv(sock, 'Ir.step "seg_tr" '
                      '"with that show thesis .";', timeout=10)
            send_recv(sock, 'Ir.step "seg_tr" "qed";', timeout=10)
            assert thm_resolves("seg_tr", "in_countE"), \
                "Initial qed should have spliced and registered."
            # Truncate past qed, leaving the body steps but not qed.
            send_recv(sock, 'Ir.truncate "seg_tr" ~2;')
            # After truncation the splice should be re-armed.  A fresh qed
            # must register the theorem again.
            send_recv(sock, 'Ir.step "seg_tr" "qed";', timeout=10)
            resolves = thm_resolves("seg_tr", "in_countE")
            send_recv(sock, 'Ir.remove "seg_tr";')
            assert resolves, (
                "BUG: after truncating past the spliced qed and stepping "
                "a fresh qed, the theorem was not registered. The splice "
                "should have re-armed.")
        run_test("segment_init_mid_proof_truncate_replay",
                 test_segment_init_mid_proof_truncate_replay)

        def test_segment_init_mid_proof_edit_replay():
            """Edit an early step in the body of a spliced proof.  With the
            default auto_replay=true, Ir.edit invokes replay_repl on the
            trailing stale steps, which must re-arm the splicer from initial
            and thread it through so that the terminating qed splices in again.
            """
            def thm_resolves(repl_id, name):
                out = send_recv(sock,
                                f'Ir.step {q(repl_id)} "thm {name}";',
                                timeout=10)
                return "Undefined fact" not in out

            # This test relies on auto_replay being on (the default) so that
            # Ir.edit drives replay_repl.  Bail out if the global was flipped.
            cfg = send_recv(sock,
                            'writeln (Bool.toString (#auto_replay (Ir.get_cfg ())));')
            assert "true" in cfg, (
                "Test precondition failed: auto_replay must be true (default) "
                f"to exercise replay via Ir.edit. Got: {cfg!r}")

            send_recv(sock,
                      'Ir.init "seg_er" ["HOL-Library.Multiset:187"];')
            send_recv(sock, 'Ir.step "seg_er" '
                      '"have h: \\"count M x > 0\\" by simp";', timeout=10)
            send_recv(sock, 'Ir.step "seg_er" '
                      '"then obtain n where \\"count M x = Suc n\\" '
                      'using gr0_conv_Suc by blast";', timeout=10)
            send_recv(sock, 'Ir.step "seg_er" '
                      '"with that show thesis .";', timeout=10)
            send_recv(sock, 'Ir.step "seg_er" "qed";', timeout=10)
            assert thm_resolves("seg_er", "in_countE"), \
                "Initial qed should have spliced and registered."
            # Edit step 0; auto_replay drives replay_repl on stale steps 1-3,
            # which must re-arm the splicer so the trailing qed splices again.
            send_recv(sock, 'Ir.edit "seg_er" 0 '
                      '"have h2: \\"0 < count M x\\" by simp";', timeout=10)
            resolves = thm_resolves("seg_er", "in_countE")
            send_recv(sock, 'Ir.remove "seg_er";')
            assert resolves, (
                "BUG: after edit-triggered replay, the qed splice did not "
                "re-fire. replay_repl must re-arm the splicer from initial "
                "and thread it through stale steps.")
        run_test("segment_init_mid_proof_edit_replay",
                 test_segment_init_mid_proof_edit_replay)

        def test_segment_init_mid_proof_deep_oops():
            """oops nested inside a structured sub-proof must disarm the
            splicer just like a top-level oops.  In Isabelle, `oops` (via
            Toplevel.forget_proof) always pops to the original outer theory
            regardless of nesting depth — the entire proof is forgotten.
            So `is_proof` transitions true -> false on that one command, and
            our splicer must treat it like a top-level oops: disarm without
            firing.
            """
            def thm_resolves(repl_id, name):
                out = send_recv(sock,
                                f'Ir.step {q(repl_id)} "thm {name}";',
                                timeout=10)
                return "Undefined fact" not in out

            send_recv(sock,
                      'Ir.init "seg_doops" ["HOL-Library.Multiset:187"];')
            # Consume the chain with a real have so we end in proof state.
            send_recv(sock, 'Ir.step "seg_doops" '
                      '"have h: \\"count M x > 0\\" by simp";', timeout=10)
            # Open a sub-proof for an irrelevant fact, then oops from inside.
            send_recv(sock, 'Ir.step "seg_doops" '
                      '"have helper: \\"True\\" proof -";', timeout=10)
            # The oops here pops the WHOLE proof, not just the sub-proof —
            # forget_proof always exits to the outer theory.
            send_recv(sock, 'Ir.step "seg_doops" "oops";', timeout=10)
            resolves = thm_resolves("seg_doops", "in_countE")
            # A subsequent qed would have nothing to close; verify we are no
            # longer in proof mode by attempting one and expecting an error.
            qed_out = send_recv(sock, 'Ir.step "seg_doops" "qed";',
                                timeout=10)
            send_recv(sock, 'Ir.remove "seg_doops";')
            assert not resolves, (
                "BUG: deep oops at mid-proof segment init spuriously "
                "registered in_countE. The inner-block oops still pops to "
                "bare theory and must disarm the splicer.")
            assert "ERR" in qed_out, (
                "After deep oops, expected `qed` to fail (we should be at "
                f"theory level, not in a proof). Got:\n{qed_out}")
        run_test("segment_init_mid_proof_deep_oops",
                 test_segment_init_mid_proof_deep_oops)

        # The two tests below confirm that local-theory state is preserved
        # through both qed (splicer fires) and oops (splicer disarms) when
        # initing at a mid-proof segment inside a locale/context/experiment.
        # We use HOL-Library.Multiset's `context comp_fun_commute` block,
        # specifically the proof body of `lemma fold_mset_fusion` (state
        # mode after `interpret comp_fun_commute g by (fact assms)`).
        # Sibling lemma `fold_mset_fun_left_comm` lives in the same context
        # and is used as the canary for locale-scoped visibility.
        FUSION_BODY_SEG = 2419  # post-`interpret ...` inside fold_mset_fusion

        def test_segment_init_mid_proof_oops_in_locale_preserves_locale():
            """oops mid-proof inside a context block must keep us inside the
            block.  The current implementation: oops disarms the splicer and
            uses the user's actual post-state, which comes from
            Toplevel.forget_proof.  forget_proof returns Theory orig_gthy,
            and orig_gthy was captured at the original lemma's begin_proof
            time — inside the context block.  So locale-scoped names remain
            accessible after oops.
            """
            send_recv(sock,
                      f'Ir.init "loc_oops" ["HOL-Library.Multiset:{FUSION_BODY_SEG}"];')
            send_recv(sock, 'Ir.step "loc_oops" "oops";', timeout=10)
            # The proof was discarded — fold_mset_fusion must NOT be registered.
            test_out = send_recv(sock,
                                  'Ir.step "loc_oops" "thm fold_mset_fusion";',
                                  timeout=10)
            # Pre-existing locale-scoped sibling must still be accessible.
            sibling_out = send_recv(sock,
                                     'Ir.step "loc_oops" "thm fold_mset_fun_left_comm";',
                                     timeout=10)
            send_recv(sock, 'Ir.remove "loc_oops";')
            assert "Undefined fact" in test_out, (
                "After oops the proof should have been discarded; "
                f"fold_mset_fusion must NOT be registered.  Got:\n{test_out}")
            assert "Undefined fact" not in sibling_out, (
                "After oops inside a context block, the sibling lemma "
                "fold_mset_fun_left_comm should still be accessible (we "
                f"should remain inside the block).  Got:\n{sibling_out}")
        run_test("segment_init_mid_proof_oops_in_locale_preserves_locale",
                 test_segment_init_mid_proof_oops_in_locale_preserves_locale)

        def test_segment_init_mid_proof_qed_in_locale_preserves_locale():
            """qed mid-proof inside a context block must keep us inside the
            block AND register the new theorem.  Current behavior: the
            splicer fires and substitutes the heap-recorded post-qed segment.
            That segment was recorded after the original qed ran during heap
            build — its state is still inside the context block (the block
            wasn't closed yet by `end`).  So both the new theorem and
            existing locale-scoped names are accessible.
            """
            send_recv(sock,
                      f'Ir.init "loc_qed" ["HOL-Library.Multiset:{FUSION_BODY_SEG}"];')
            # Step the rest of fold_mset_fusion's body and close it.
            send_recv(sock, 'Ir.step "loc_qed" '
                      '"from * show ?thesis by (induct A) auto";',
                      timeout=10)
            send_recv(sock, 'Ir.step "loc_qed" "qed";', timeout=10)
            # Newly registered lemma (via splice)
            test_out = send_recv(sock,
                                  'Ir.step "loc_qed" "thm fold_mset_fusion";',
                                  timeout=10)
            # Pre-existing locale-scoped sibling
            sibling_out = send_recv(sock,
                                     'Ir.step "loc_qed" "thm fold_mset_fun_left_comm";',
                                     timeout=10)
            send_recv(sock, 'Ir.remove "loc_qed";')
            assert "Undefined fact" not in test_out, (
                "After qed, the splicer should have registered "
                f"fold_mset_fusion.  Got:\n{test_out}")
            assert "Undefined fact" not in sibling_out, (
                "After qed inside a context block, the sibling lemma "
                "fold_mset_fun_left_comm should still be accessible (we "
                f"should remain inside the block).  Got:\n{sibling_out}")
        run_test("segment_init_mid_proof_qed_in_locale_preserves_locale",
                 test_segment_init_mid_proof_qed_in_locale_preserves_locale)

        def test_segment_init_mid_proof_fork_qed():
            """Fork from a mid-proof segment-init REPL at the base state,
            step body + qed in the fork.  The fork inherits the parent's
            splicer, so the theorem must be registered in the fork.
            """
            send_recv(sock,
                      'Ir.init "seg_fk" ["HOL-Library.Multiset:187"];')
            send_recv(sock, 'Ir.fork "seg_fk" "seg_fk_child" 0;')
            send_recv(sock, 'Ir.step "seg_fk_child" '
                      '"have \\"count M x > 0\\" by simp";', timeout=10)
            send_recv(sock, 'Ir.step "seg_fk_child" '
                      '"then obtain n where \\"count M x = Suc n\\" '
                      'using gr0_conv_Suc by blast";', timeout=10)
            send_recv(sock, 'Ir.step "seg_fk_child" '
                      '"with that show thesis .";', timeout=10)
            send_recv(sock, 'Ir.step "seg_fk_child" "qed";', timeout=10)
            thm_out = send_recv(sock,
                                'Ir.step "seg_fk_child" "thm in_countE";',
                                timeout=10)
            send_recv(sock, 'Ir.remove "seg_fk";')
            assert "Undefined fact" not in thm_out, (
                "After forking from a mid-proof segment-init REPL and "
                "stepping through qed in the fork, the theorem should be "
                "registered.  The fork must inherit the parent's splicer.  "
                f"Got:\n{thm_out}")
        run_test("segment_init_mid_proof_fork_qed",
                 test_segment_init_mid_proof_fork_qed)

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
