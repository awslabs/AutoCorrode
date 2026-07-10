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

        # -- `repl.py cli` one-shot client (subprocess against this server) --

        def run_cli(*cli_args, want_rc=0):
            """Run `repl.py cli VERB --port P --token T [ARGS...]` as a subprocess
            against the running server, returning (stdout, stderr). Asserts rc.
            Options go right after the verb (before any args / `--`), since `--`
            makes everything after it literal."""
            verb, rest = cli_args[0], list(cli_args[1:])
            cmd = [sys.executable, repl_py, "cli", verb,
                   "--port", str(port), "--token", token, *rest]
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
            assert r.returncode == want_rc, (
                f"cli {' '.join(cli_args)}: expected rc={want_rc}, got {r.returncode}\n"
                f"stdout:\n{r.stdout}\nstderr:\n{r.stderr}")
            return r.stdout, r.stderr

        def test_cli_help():
            # `cli help` and `cli --help` print the verb table (no server needed).
            for variant in (["help"], ["--help"]):
                r = subprocess.run([sys.executable, repl_py, "cli", *variant],
                                   capture_output=True, text=True, timeout=30)
                assert r.returncode == 0, f"cli {variant}: rc={r.returncode}"
                assert "raw EXPR" in r.stdout and "Ir.theories ()" in r.stdout, \
                    f"cli {variant}: verb table missing:\n{r.stdout}"
                assert "-> Ir.step" in r.stdout, f"raw forms missing:\n{r.stdout}"
        run_test("cli_help", test_cli_help)

        def test_cli_theories():
            out, _ = run_cli("theories")
            assert "Main" in out, f"cli theories should list Main, got:\n{out}"
        run_test("cli_theories", test_cli_theories)

        def test_cli_typed_roundtrip():
            # init -> step (a complete lemma) -> state -1 (negative int) -> remove,
            # all through the CLI's typed verbs.
            run_cli("init", "cli_r", "Main")
            out, _ = run_cli("step", "cli_r", "lemma cli_foo: True by simp")
            assert out.strip() != "", f"cli step produced no output:\n{out}"
            out, _ = run_cli("state", "cli_r", "-1")   # negative int -> ML ~1
            assert out.strip() != "", "cli state -1 produced no output"
            run_cli("remove", "cli_r")
        run_test("cli_typed_roundtrip", test_cli_typed_roundtrip)

        def test_cli_find_theorems_autoquote():
            # A bare (unquoted) term pattern is an outer-syntax error to
            # find_theorems; the CLI auto-quotes it (matching the MCP tool), so
            # `find-theorems R N '<term>'` works without the user quoting it.
            run_cli("init", "cli_ftq", "Main")
            # Bare term -> auto-quoted -> should find rev_rev_ident.
            out, _ = run_cli("find-theorems", "cli_ftq", "5", "rev (rev _)")
            assert "rev_rev_ident" in out, \
                f"bare-term find-theorems should auto-quote and match:\n{out}"
            assert "syntax error" not in out.lower(), \
                f"bare-term find-theorems should not error:\n{out}"
            # name: criterion must stay unquoted and still work.
            out, _ = run_cli("find-theorems", "cli_ftq", "3", "name: conjI")
            assert "conjI" in out, f"name: find-theorems broke:\n{out}"
            # An already-quoted term is left as-is (idempotent).
            out, _ = run_cli("find-theorems", "cli_ftq", "5", '"rev (rev _)"')
            assert "rev_rev_ident" in out, \
                f"already-quoted find-theorems regressed:\n{out}"
            run_cli("remove", "cli_ftq")
        run_test("cli_find_theorems_autoquote", test_cli_find_theorems_autoquote)

        def test_cli_raw():
            out, _ = run_cli("raw", "Ir.theories ()")
            assert "Main" in out, f"cli raw should list Main, got:\n{out}"

        run_test("cli_raw", test_cli_raw)

        def test_cli_separator():
            # `--` separates options from args; a negative IDX after it still
            # parses (and reaches ML as ~1).
            run_cli("init", "cli_sep", "Main")
            run_cli("step", "cli_sep", "lemma cli_sep_l: True by simp")
            out, _ = run_cli("state", "--", "cli_sep", "-1")
            assert out.strip() != "", "cli state -- cli_sep -1 produced no output"
            run_cli("remove", "cli_sep")
        run_test("cli_separator", test_cli_separator)

        def test_cli_ml_error_exit1():
            # An ML error (operating on a non-existent REPL) -> ERR -> exit 1,
            # with the message on stderr.
            _, err = run_cli("step", "no_such_repl_zzz", "lemma x: True by simp",
                             want_rc=1)
            assert err.strip() != "", "cli ML error should print to stderr"
        run_test("cli_ml_error_exit1", test_cli_ml_error_exit1)

        def test_cli_usage_exit2():
            # Wrong arity / unknown verb / bad int -> usage error, exit 2.
            run_cli("state", "only_one_arg", want_rc=2)
            run_cli("no_such_verb", want_rc=2)
            run_cli("state", "r", "not_an_int", want_rc=2)
        run_test("cli_usage_exit2", test_cli_usage_exit2)

        def test_cli_conn_refused_exit2():
            # A bad port -> connection failure -> exit 2 (not 1).
            r = subprocess.run(
                [sys.executable, repl_py, "cli", "theories", "--port", "1"],
                capture_output=True, text=True, timeout=30)
            assert r.returncode == 2, f"cli on dead port: expected rc=2, got {r.returncode}"
        run_test("cli_conn_refused_exit2", test_cli_conn_refused_exit2)

        # -- Benchmark: persistent TCP vs. per-call `cli` subprocess --
        # Both fire N serialized `Ir.theories ()`. The TCP path reuses one
        # connection (what I/Q / the MCP server do); the cli path pays a fresh
        # python3 + connect + auth per call (what a shell loop does). This
        # quantifies the per-invocation overhead of the one-shot CLI — it is a
        # measurement, not a latency assertion (only basic correctness is checked).
        def bench_tcp_vs_cli():
            n = int(os.environ.get("IR_BENCH_ITERS", "20"))
            # warm both paths once (JIT / connection setup) before timing.
            assert "Main" in send_recv(sock, "Ir.theories ();")
            run_cli("theories")

            t0 = time.perf_counter()
            for _ in range(n):
                out = send_recv(sock, "Ir.theories ();")
                assert "Main" in out, f"tcp theories missing Main:\n{out}"
            tcp_s = time.perf_counter() - t0

            t0 = time.perf_counter()
            for _ in range(n):
                out, _ = run_cli("theories")
                assert "Main" in out, f"cli theories missing Main:\n{out}"
            cli_s = time.perf_counter() - t0

            tcp_ms, cli_ms = tcp_s / n * 1000, cli_s / n * 1000
            ratio = (cli_ms / tcp_ms) if tcp_ms > 0 else float("inf")
            print(f"\n    {_BOLD}I/R theories() x{n}{_RESET}  "
                  f"persistent TCP: {_GREEN}{tcp_ms:.1f} ms/call{_RESET}   "
                  f"cli subprocess: {_YELLOW}{cli_ms:.1f} ms/call{_RESET}   "
                  f"({ratio:.0f}x overhead per shell call)")
        run_test("bench_tcp_vs_cli", bench_tcp_vs_cli)

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

        def test_pool_exhausted():
            """When the ML pool is saturated, a further command must return
            a well-formed 'Pool exhausted' ERR frame within a bounded window
            (--pool-acquire-timeout, default 30s), and the client's
            connection must stay open so a follow-up command succeeds once
            the pool drains.

            Holds slots for 45s (> 30s default) so the probe deterministically
            trips the timeout rather than waiting for the holders to release.
            """
            n_busy = 5
            busy_duration_ms = 45_000  # must exceed --pool-acquire-timeout
            timeout_slack_s = 10.0     # how much longer than the timeout we'll
                                       # wait for the ERR frame before failing
            barrier_up = threading.Event()
            errors = []
            lock = threading.Lock()

            def hold_slot():
                try:
                    s = connect(port, token=token)
                    try:
                        barrier_up.set()  # ok if racy — first thread's fine
                        send_recv(
                            s,
                            f'OS.Process.sleep (Time.fromMilliseconds '
                            f'{busy_duration_ms});',
                            timeout=busy_duration_ms / 1000.0 + 5.0)
                    finally:
                        s.close()
                except Exception as e:
                    with lock:
                        errors.append(("hold_slot", repr(e)))

            holders = [threading.Thread(target=hold_slot, daemon=True)
                       for _ in range(n_busy)]
            for h in holders:
                h.start()

            # Wait for at least the first holder to get into its send_recv
            # (proxy for "slots are being consumed"). Then give the others a
            # short head-start so ALL are past pool.acquire before we probe.
            assert barrier_up.wait(timeout=5.0), \
                "slot-holder threads did not start in time"
            time.sleep(0.5)

            # Probe: open a fresh connection and send a command that would
            # normally take milliseconds. It should come back as an ERR frame
            # bounded by --pool-acquire-timeout, well before the 45s hold ends.
            probe_sock = connect(port, token=token)
            try:
                t0 = time.time()
                # recv timeout must exceed the server's pool-acquire-timeout
                # (default 30s) plus slack.
                probe_recv_timeout = 30.0 + timeout_slack_s
                out = send_recv(probe_sock, 'Ir.help ();',
                                timeout=probe_recv_timeout)
                probe_elapsed = time.time() - t0

                assert "Pool exhausted" in out, (
                    f"Expected 'Pool exhausted' in probe reply, got (in "
                    f"{probe_elapsed:.2f}s):\n{out}")
                # The probe must NOT have waited for holders to release (that
                # would be ~45s). Allow up to 30s (default timeout) + slack.
                assert probe_elapsed < 30.0 + timeout_slack_s, (
                    f"Probe returned only after {probe_elapsed:.2f}s — that's "
                    f"waiting for slow commands to release, not the "
                    f"pool-acquire-timeout")

                # Now wait for the busy holders to drain, then confirm the
                # same probe connection can still be used.
                for h in holders:
                    h.join(timeout=busy_duration_ms / 1000.0 + 10.0)
                    assert not h.is_alive(), \
                        "slot-holder thread did not finish"
                if errors:
                    raise AssertionError(f"slot-holder errors: {errors}")

                # Same connection — not a fresh connect — proves the server
                # did not close it after the pool-exhausted reply.
                out2 = send_recv(probe_sock, 'Ir.help ();', timeout=10.0)
                assert "Ir.init" in out2, (
                    f"Follow-up command on retained connection failed:\n{out2}")
            finally:
                probe_sock.close()

        run_test("pool_exhausted", test_pool_exhausted)

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
