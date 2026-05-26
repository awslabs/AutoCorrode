#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

"""Integration tests for I/C. Requires a running I/R REPL.

Test fixtures live in test/ as proper .thy files.

Usage:
    # Start I/R REPL first:
    python3 ../ir/repl.py --port 9147

    # Then run tests:
    python3 test_ic_integration.py [--repl-port 9147]
"""

import argparse
import os
import secrets
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import unittest

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
TEST_DIR = os.path.join(SCRIPT_DIR, "test")
sys.path.insert(0, SCRIPT_DIR)

import contextlib
import functools
import io

from ic_repl import ReplClient
from ic_core import DiamondStrategy
from ic_check import check, clean, print_heapdiff
from ic_client import print_response
from ic_status import status

_is_remote = bool(os.environ.get("ISABELLE_REMOTE"))

# IC_POOL_SIZE=N overrides the default pool_size for all check() calls,
# allowing the full test suite to exercise parallel execution.
_pool_size = int(os.environ.get("IC_POOL_SIZE", 1))
if _pool_size > 1:
    check = functools.partial(check, pool_size=_pool_size)

# ISABELLE_REMOTE implies always_stepwise (Ir.load_theory can't read
# local files on the remote host).
if os.environ.get("ISABELLE_REMOTE"):
    check = functools.partial(check, always_stepwise=True)

IR_DIR = os.path.join(os.path.dirname(SCRIPT_DIR), "ir")
TEMPLATE_DIR = os.path.join(TEST_DIR, "_templates")


def install_templates():
    """Copy all template files to their fixture directories.

    Templates in test/_templates/<subdir>/<file> are copied to
    test/<subdir>/<file>. Called before each test to ensure clean state.
    """
    for dirpath, _, filenames in os.walk(TEMPLATE_DIR):
        for fname in filenames:
            src = os.path.join(dirpath, fname)
            rel = os.path.relpath(src, TEMPLATE_DIR)
            dst = os.path.join(TEST_DIR, rel)
            shutil.copy2(src, dst)


def remove_templates():
    """Remove all files that were copied from _templates."""
    for dirpath, _, filenames in os.walk(TEMPLATE_DIR):
        for fname in filenames:
            rel = os.path.relpath(os.path.join(dirpath, fname), TEMPLATE_DIR)
            dst = os.path.join(TEST_DIR, rel)
            try:
                os.remove(dst)
            except FileNotFoundError:
                pass


def find_free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


class ReplProcess:
    """Manage an I/R REPL subprocess for testing."""

    def __init__(self, session="HOL", dirs=None, no_bash_server=False,
                 isabelle=None):
        self.session = session
        self.dirs = dirs or []
        self.no_bash_server = no_bash_server
        self.isabelle = isabelle
        self.port = find_free_port()
        self.token = secrets.token_urlsafe(24)
        self.proc = None
        self._repl = None
        self._log_file = None

    def start(self, timeout=120) -> ReplClient:
        """Start REPL, wait for readiness, return connected ReplClient."""
        print(f"  Starting I/R REPL (session={self.session}, "
              f"port={self.port})...", file=sys.stderr, flush=True)
        start = time.monotonic()

        env = os.environ.copy()
        env["IR_AUTH_TOKEN"] = self.token
        cmd = [sys.executable, os.path.join(IR_DIR, "repl.py"),
               "--session", self.session,
               "--port", str(self.port),
               "--server-only"]
        if self.isabelle:
            cmd += ["--isabelle", self.isabelle]
        for d in self.dirs:
            cmd += ["--dir", d]
        if self.no_bash_server:
            cmd.append("--no-bash-server")

        self._log_file = tempfile.NamedTemporaryFile(
            mode='w+', prefix='ir_repl_', suffix='.log', delete=False)
        self.proc = subprocess.Popen(
            cmd, stdout=self._log_file, stderr=subprocess.STDOUT,
            env=env)

        deadline = start + timeout
        while time.monotonic() < deadline:
            if self.proc.poll() is not None:
                self._log_file.flush()
                self._log_file.seek(0)
                tail = self._log_file.read()[-2000:]
                raise RuntimeError(
                    f"I/R REPL process died (exit {self.proc.returncode})"
                    f":\n{tail}")
            try:
                probe = ReplClient(port=self.port, token=self.token)
                probe.connect()
                result = probe.send('Ir.help ()', timeout=10)
                probe.close()
                if "Ir.init" in result.output:
                    elapsed = int(time.monotonic() - start)
                    print(f"  I/R REPL ready on port {self.port} ({elapsed}s)",
                          file=sys.stderr, flush=True)
                    self._repl = ReplClient(port=self.port, token=self.token)
                    self._repl.connect()
                    return self._repl
            except (ConnectionRefusedError, OSError, socket.timeout):
                pass
            time.sleep(1)

        self.stop()
        raise RuntimeError(
            f"I/R REPL not ready after {timeout}s on port {self.port}")

    def stop(self):
        """Shut down REPL subprocess gracefully via SIGTERM."""
        if self._repl:
            self._repl.close()
            self._repl = None
        if self._log_file:
            try:
                self._log_file.close()
                os.unlink(self._log_file.name)
            except OSError:
                pass
            self._log_file = None
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()  # SIGTERM → repl.py cleans up Poly/ML etc.
            try:
                self.proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                print(f"  WARNING: I/R REPL (PID {self.proc.pid}) did not "
                      f"exit after SIGTERM, sending SIGKILL",
                      file=sys.stderr, flush=True)
                self.proc.kill()
                self.proc.wait(timeout=5)
            print(f"  Shut down I/R REPL (PID {self.proc.pid})",
                  file=sys.stderr, flush=True)


def fixture_dir(name):
    """Return absolute path to a test fixture directory."""
    return os.path.join(TEST_DIR, name)


def find_dep(resp, name):
    """Find a dependency by name in the structured check response."""
    for d in resp.get("dependencies", []):
        if d["name"] == name:
            return d
    return None


def fixture_file(name, thy):
    """Return absolute path to a .thy file in a test fixture directory."""
    return os.path.join(TEST_DIR, name, f"{thy}.thy")




class TestICSIntegration(unittest.TestCase):
    """Integration tests that require a running I/R REPL."""

    repl = None
    repl_proc = None
    isabelle_path = None  # set by main() from --isabelle / $ISABELLE

    @classmethod
    def setUpClass(cls):
        cls.repl_proc = ReplProcess(
            session="HOL", dirs=[TEST_DIR], isabelle=cls.isabelle_path)
        cls.repl = cls.repl_proc.start()
        clean(cls.repl)

    @classmethod
    def tearDownClass(cls):
        if cls.repl:
            try:
                clean(cls.repl)
            except Exception:
                pass
        if cls.repl_proc:
            cls.repl_proc.stop()
        remove_templates()

    def setUp(self):
        """Restore template files and clean REPL state before each test."""
        install_templates()
        clean(self.repl)

    def test_auto_scan_and_check(self):
        """Checking Scan_B.thy discovers session, loads Scan_A via Ir.load_theory, checks Scan_B."""
        resp = check(
            fixture_file("scan_simple", "Scan_B"),
            self.repl)
        self.assertEqual(resp["status"], "ok")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["name"], "Scan_B")
        self.assertEqual(resp["target"]["steps_taken"], 1)

    def test_target_after_load_is_unchanged_from_file(self):
        """Target that was loaded via Ir.load_theory in a prior check
        must short-circuit to TargetUnchangedPlan(source=FromFile())
        on the next check — not error out the way a NO_SEGMENTS heap
        target does. Locks in that the FromFile/FromHeap split treats
        load-theory targets as a real OK.

        After editing Scan_A, the next check must detect the change
        and not falsely report unchanged — the LoadedMarker hash no
        longer matches disk, so classification falls out of FileLoaded.
        """
        scan_a = fixture_file("scan_simple", "Scan_A")
        scan_b = fixture_file("scan_simple", "Scan_B")

        # First: check Scan_B → Scan_A loaded via Ir.load_theory,
        # LoadedMarker written for Scan_A.
        resp = check(scan_b, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

        # Second: re-check Scan_A as target. classify_loaded_repl sees
        # its LoadedMarker, content_hash and dep_hashes still match,
        # so classification = FileLoaded → TargetUnchangedPlan(FromFile).
        resp = check(scan_a, self.repl)
        self.assertEqual(resp["status"], "ok",
                         msg=f"Expected ok, got: {resp}")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["name"], "Scan_A")
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Third: edit Scan_A and re-check. The LoadedMarker hash no
        # longer matches disk → classification leaves FileLoaded, the
        # change must be picked up and re-stepped.
        with open(scan_a, 'w') as f:
            f.write('theory Scan_A\n  imports Main\nbegin\n\n'
                    'definition a_val where "a_val = (43::nat)"\n\n'
                    'end\n')
        resp = check(scan_a, self.repl)
        self.assertEqual(resp["status"], "ok",
                         msg=f"Expected ok after edit, got: {resp}")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertGreater(resp["target"]["steps_taken"], 0,
                           msg=f"Edit must be re-stepped, got: {resp['target']}")

    def test_check_single(self):
        """Check a single file with no dependencies beyond heap."""
        resp = check(
            fixture_file("check_all", "Check_All"),
            self.repl)
        self.assertEqual(resp["status"], "ok")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 3)

    def test_symlinked_target_path_resolution(self):
        """Target whose path traverses a symlink should resolve to its session.

        Mirrors a reported failure where the user's CWD reached a session
        through a symlink (e.g. /Users/x/workplace -> /Volumes/workplace),
        so the absolute target path didn't share a prefix with the
        session's stored directory and produced 'File not in any session'.
        """
        real_dir = fixture_dir("check_all")
        tmpdir = tempfile.mkdtemp(prefix="ic_symlink_")
        try:
            link = os.path.join(tmpdir, "check_all_link")
            os.symlink(real_dir, link)
            link_thy = os.path.join(link, "Check_All.thy")
            resp = check(link_thy, self.repl)
            self.assertEqual(
                resp["status"], "ok",
                msg=f"Symlinked target should resolve: {resp}")
            self.assertEqual(resp["target"]["status"], "ok")
        finally:
            shutil.rmtree(tmpdir, ignore_errors=True)

    def test_recheck_no_changes(self):
        """Re-checking an unchanged file reports steps_taken=0."""
        path = fixture_file("check_all", "Check_All")
        resp1 = check(path, self.repl)
        self.assertEqual(resp1["target"]["status"], "ok")
        self.assertGreater(resp1["target"]["steps_taken"], 0)

        resp2 = check(path, self.repl)
        self.assertEqual(resp2["target"]["status"], "ok")
        self.assertEqual(resp2["target"]["steps_taken"], 0)

    def test_recheck_error_no_changes(self):
        """Re-checking a failed file without changes recovers the cached error.

        The file has 5 successful definitions before the failing lemma,
        ensuring that a full reprocess would give steps_taken >> 1.
        The recheck must re-execute only the failing command (steps_taken=1).
        """
        path = fixture_file("recheck_error", "Rchk_Err")
        resp1 = check(path, self.repl)
        self.assertEqual(resp1["target"]["status"], "error")
        self.assertEqual(resp1["target"]["error"],
                         'Failed to apply initial proof method:\n'
                         'goal (1 subgoal):\n'
                         ' 1. 0 = 1\n'
                         'At command "by"')
        self.assertEqual(resp1["target"]["line"], 15)
        # 5 definitions + lemma + by(fail) = 7 steps
        self.assertEqual(resp1["target"]["steps_taken"], 7)

        resp2 = check(path, self.repl)
        self.assertEqual(resp2["target"]["status"], "error")
        self.assertEqual(resp2["target"]["line"], 15)
        self.assertEqual(resp2["target"]["error"], resp1["target"]["error"])
        # Only the failing command is re-executed, not the whole file
        self.assertEqual(resp2["target"]["steps_taken"], 1)

    def test_check_error_with_line(self):
        """check_error/Check_Error.thy: definition succeeds, lemma "(0::nat) = 1" fails."""
        resp = check(
            fixture_file("check_error", "Check_Error"),
            self.repl)
        t = resp["target"]
        self.assertEqual(t["status"], "error")
        self.assertEqual(t["error"],
                         'Failed to apply initial proof method:\n'
                         'goal (1 subgoal):\n'
                         ' 1. 0 = 1\n'
                         'At command "by"')
        self.assertEqual(t["line"], 6)
        self.assertEqual(t["steps_taken"], 3)

    def test_rebuild_after_fix(self):
        """Rebuild_Brk.thy fails, overwrite with fixed version, re-check succeeds."""
        resp = check(
            fixture_file("rebuild_broken", "Rebuild_Brk"),
            self.repl)
        t = resp["target"]
        self.assertEqual(t["status"], "error")
        self.assertEqual(t["error"],
                         'Failed to apply initial proof method:\n'
                         'goal (1 subgoal):\n'
                         ' 1. 1 = 2\n'
                         'At command "by"')
        self.assertEqual(t["line"], 5)
        self.assertEqual(t["steps_taken"], 2)

        # Overwrite with fixed version (install_templates restores before next test)
        shutil.copy2(
            fixture_file("rebuild_fixed", "Rebuild_Brk"),
            fixture_file("rebuild_broken", "Rebuild_Brk"))

        resp = check(
            fixture_file("rebuild_broken", "Rebuild_Brk"),
            self.repl)
        self.assertEqual(resp["status"], "ok")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 2)

    def test_dependency_chain(self):
        """Checking DC_B loads dep DC_A via Ir.load_theory, then steps DC_B."""
        resp = check(
            fixture_file("dep_chain", "DC_B"),
            self.repl)
        self.assertEqual(resp["status"], "ok")
        self.assertEqual(resp["target"]["status"], "ok")
        # definition + lemma + unfolding + by eval = 4
        self.assertEqual(resp["target"]["steps_taken"], 4)
        dc_a = find_dep(resp, "DC_A")
        self.assertIsNotNone(dc_a)
        if not _is_remote:
            self.assertEqual(dc_a["resolution"], "from_file")

    def test_always_stepwise_steps_dep_via_repl(self):
        """--always-stepwise uses CheckPlan instead of Ir.load_theory for file deps."""
        resp = check(
            fixture_file("stepwise_basic", "SW_B"),
            self.repl, always_stepwise=True)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")
        sw_a = find_dep(resp, "SW_A")
        self.assertIsNotNone(sw_a)
        self.assertEqual(sw_a["resolution"], "repl")
        self.assertGreater(sw_a["steps_taken"], 0)

    def test_always_stepwise_recheck_after_dep_change(self):
        """--always-stepwise: changing a dep and re-checking must not crash.

        Regression: resolve_diamonds treated all NoRepl deps as
        LoadFilePlan candidates and overwrote their CheckPlan(REBASE)
        with CheckPlan(INIT), triggering a REBASE/INIT conflict in
        remove_stale_repls when pin-dep expansion added the target.
        """
        dep_dir = fixture_dir("stepwise_recheck")
        a_path = os.path.join(dep_dir, "SWR_A.thy")
        c_path = os.path.join(dep_dir, "SWR_C.thy")

        resp = check(c_path, self.repl, always_stepwise=True)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")

        with open(a_path, 'w') as f:
            f.write('theory SWR_A\n  imports Main\nbegin\n\n'
                    'definition swr_val where "swr_val = (42::nat)"\n\n'
                    'end\n')

        resp = check(c_path, self.repl, always_stepwise=True)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "error")
        self.assertIn("42 + 1 = 2", resp["target"]["error"])

    def test_dry_run_prints_plans_without_executing(self):
        """--dry-run prints the plan table without modifying I/R state."""
        dep_dir = fixture_dir("stepwise_recheck")
        a_path = os.path.join(dep_dir, "SWR_A.thy")
        c_path = os.path.join(dep_dir, "SWR_C.thy")

        resp = check(c_path, self.repl)
        self.assertEqual(resp["target"]["status"], "ok")

        with open(a_path, 'w') as f:
            f.write('theory SWR_A\n  imports Main\nbegin\n\n'
                    'definition swr_val where "swr_val = (42::nat)"\n\n'
                    'end\n')

        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            resp = check(c_path, self.repl, dry_run=True)
        output = buf.getvalue()

        self.assertIn("theory", output)
        self.assertIn("SWR_A", output)
        self.assertIn("SWR_C", output)
        self.assertIn("CheckPlan", output)
        self.assertEqual(resp["status"], "ok")
        self.assertTrue(resp.get("dry_run"))

        from ic_check import read_all_markers, serialize_marker
        markers_before = read_all_markers(self.repl)
        # Re-run dry_run and verify markers didn't change
        buf2 = io.StringIO()
        with contextlib.redirect_stdout(buf2):
            check(c_path, self.repl, dry_run=True)
        markers_after = read_all_markers(self.repl)
        for key in markers_before:
            self.assertEqual(
                serialize_marker(markers_before[key]),
                serialize_marker(markers_after[key]),
                msg=f"dry-run modified marker for {key}")

    def test_always_stepwise_rejects_keywords_dep(self):
        """--always-stepwise must error when a dep declares custom keywords.

        Theories with custom keywords cannot be stepped via REPL (the
        keyword parsing is unavailable). With always_stepwise, there is
        no Ir.load_theory fallback, so the dep should fail with a clear
        error about keywords and the target should be stale.
        """
        resp = check(
            fixture_file("stepwise_keywords", "SKW_User"),
            self.repl, always_stepwise=True)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        skw_def = find_dep(resp, "SKW_Def")
        self.assertIsNotNone(skw_def)
        self.assertEqual(skw_def["status"], "error")
        self.assertEqual(
            skw_def["error"],
            "Theory 'stepwise_keywords.SKW_Def' declares custom keywords "
            "and cannot be checked via REPL; remove --always-stepwise or "
            "ensure it is in the heap")
        self.assertEqual(resp["target"]["status"], "stale")

    def test_dep_chain_a_broken(self):
        """When DCA_A is broken, Ir.load_theory fails and DCA_B is stale."""
        resp = check(
            fixture_file("dep_chain_a_broken", "DCA_B"),
            self.repl)
        a_dep = find_dep(resp, "DCA_A")
        self.assertEqual(a_dep["status"], "error")
        self.assertEqual(resp["target"]["status"], "stale")
        self.assertEqual(resp["target"]["reason"], "depends on failed DCA_A")

    def test_dep_chain_b_broken(self):
        """When DCB_B is broken, DCB_A loads fine but DCB_B has the proof error."""
        resp = check(
            fixture_file("dep_chain_b_broken", "DCB_B"),
            self.repl)
        t = resp["target"]
        self.assertEqual(t["status"], "error")
        self.assertEqual(t["error"],
                         'Failed to apply initial proof method:\n'
                         'goal (1 subgoal):\n'
                         ' 1. 3 = 4\n'
                         'At command "by"')
        self.assertEqual(t["line"], 5)
        self.assertEqual(t["steps_taken"], 2)

    def test_recheck_incremental(self):
        """Changing DC_B and re-checking only re-steps the changed tail."""
        b_path = fixture_file("dep_chain", "DC_B")

        resp = check(b_path, self.repl)
        self.assertEqual(resp["target"]["status"], "ok")

        # Edit in-place (install_templates restores before next test)
        with open(b_path) as f:
            lines = f.readlines()
        insert_at = next(i for i, l in enumerate(lines)
                         if "b_val" in l) + 1
        lines.insert(insert_at,
                      'definition b_val2 where "b_val2 = a_val + 2"\n')
        with open(b_path, "w") as f:
            f.writelines(lines)

        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok")
        self.assertEqual(resp["target"]["status"], "ok")
        # New def inserted after b_val def; re-steps: b_val2 + lemma + unfolding + by eval = 4
        self.assertEqual(resp["target"]["steps_taken"], 4)

    def test_dep_reload_after_change(self):
        """Changing a dependency invalidates the target on re-check."""
        dep_dir = fixture_dir("dep_reload")
        a_path = os.path.join(dep_dir, "DR_A.thy")
        b_path = os.path.join(dep_dir, "DR_B.thy")

        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")

        with open(a_path, 'w') as f:
            f.write('theory DR_A\n  imports Main\nbegin\n\n'
                    'definition val_a where "val_a = (42::nat)"\n\n'
                    'end\n')

        resp = check(b_path, self.repl)
        self.assertEqual(resp["target"]["status"], "error")
        self.assertEqual(resp["target"]["error"],
                         'Failed to apply initial proof method:\n'
                         'goal (1 subgoal):\n'
                         ' 1. 42 = 1\n'
                         'At command "by"')
        self.assertEqual(resp["target"]["line"], 6)

    def test_orphan_marker_after_dep_failure(self):
        """Marker must not survive pre-execution REPL removal when a dep fails.

        remove_stale_repls (in execute_plans) destroys the target's REPL
        up front based on its plan. If a dep then fails, run_dep_job
        short-circuits before the target's plan runs, so the plan body
        that would have written a fresh marker never executes. The
        invariant "SteppedMarker exists ⇔ matching ic.* REPL exists"
        must therefore be preserved by remove_stale_repls itself, by
        deleting the paired marker alongside the REPL.

        Without that, on the next check() the classify worker reads the
        orphan SteppedMarker, finds repl_info=None so body_step_count=0
        < cmd_count, falls into the cached-error branch, and calls
        Ir.step on the missing REPL — RuntimeError, check() crashes.

        Sequence:
        1. check(OM_B) — OM_A loads, OM_B steps OK.
        2. Edit OM_A so its proof breaks.
        3. check(OM_B) — OM_A fails to load; B's CheckPlan(INIT) drives
           remove_stale_repls to drop ic.orphan_marker.OM_B, then
           run_dep_job sees A's failure and returns stale without
           writing any new marker for B. The OM_B marker must also be
           cleared, otherwise the next check crashes.
        4. check(OM_B) — must not crash; target reports stale because
           OM_A still fails to load.
        """
        dep_dir = fixture_dir("orphan_marker")
        a_path = os.path.join(dep_dir, "OM_A.thy")
        b_path = os.path.join(dep_dir, "OM_B.thy")

        # Step 1: both files OK.
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")

        # Step 2: break OM_A so Ir.load_theory will fail on it.
        with open(a_path, 'w') as f:
            f.write('theory OM_A\n  imports Main\nbegin\n\n'
                    'lemma broken: "(0::nat) = 1" by (rule TrueI)\n\n'
                    'end\n')

        # Step 3: OM_A fails to load -> OM_B comes back stale, B's
        # REPL is removed, and B's SteppedMarker should be cleared.
        resp = check(b_path, self.repl)
        self.assertEqual(resp["target"]["status"], "stale",
                         msg=f"Expected stale target, got {resp['target']}")
        a_dep = find_dep(resp, "OM_A")
        self.assertIsNotNone(a_dep)
        self.assertEqual(a_dep["status"], "error")

        # Invariant check: REPL is gone AND its marker is gone.
        from ic_check import read_all_markers, parse_repls_output, ml_expect
        markers = read_all_markers(self.repl)
        repls_raw = ml_expect(self.repl.send('Ir.repls ()'))
        active, _ = parse_repls_output(repls_raw)
        self.assertNotIn("ic.orphan_marker.OM_B", active,
                         msg="REPL should have been destroyed by "
                             "remove_stale_repls")
        self.assertNotIn("orphan_marker.OM_B", markers,
                         msg="SteppedMarker must be cleared alongside "
                             "the REPL it pointed at")

        # Step 4: re-checking must not crash on an orphan marker.
        resp = check(b_path, self.repl)
        self.assertEqual(resp["target"]["status"], "stale",
                         msg=f"Expected stale target on recheck, "
                             f"got {resp['target']}")

    def test_dep_reload_broken_not_stale(self):
        """Breaking a dep should not silently use stale loaded version.

        Check DRB_B (loads DRB_A ok). Then break DRB_A with a proof error.
        Recheck DRB_B — should detect the broken dep, not silently succeed
        with the stale loaded version.
        """
        dep_dir = fixture_dir("dep_reload_broken")
        a_path = os.path.join(dep_dir, "DRB_A.thy")
        b_path = os.path.join(dep_dir, "DRB_B.thy")

        # First check: succeeds
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")

        # Break DRB_A: introduce a proof error
        with open(a_path, 'w') as f:
            f.write('theory DRB_A\n  imports Main\nbegin\n\n'
                    'definition val_a where "val_a = (1::nat)"\n'
                    'lemma "False" by simp\n\n'
                    'end\n')

        # Recheck DRB_B — should NOT silently succeed
        resp = check(b_path, self.repl)
        self.assertNotEqual(resp["target"]["status"], "ok",
                            msg="Target should not be ok when dep is broken")

    def test_dep_fix_after_load_failure(self):
        """Fixing a dep after it failed to load must let target recover.

        LoadedMarker persists after Ir.load_theory fails and removes
        the theory from Isabelle's theory database. On the next check,
        classify_loaded_repl sees matching hashes → FileLoaded →
        SkipPlan, but the theory is actually gone. Ir.init then fails
        with "undefined entry for theory".

        Sequence:
        1. check(B) — A loaded via Ir.load_theory, B checked OK.
        2. Break A (proof error).
        3. check(B) — A fails to load (theory removed from database),
           B reported stale.
        4. Fix A (restore original content).
        5. check(B) — must not crash; should reload A and check B OK.
        """
        dep_dir = fixture_dir("stale_loaded_marker")
        a_path = os.path.join(dep_dir, "SLM_A.thy")
        b_path = os.path.join(dep_dir, "SLM_B.thy")

        # Step 1: check B — A loaded, B OK
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")

        # Step 2: break A
        with open(a_path, 'w') as f:
            f.write('theory SLM_A\n  imports Main\nbegin\n\n'
                    'lemma "False" by simp\n\n'
                    'definition slm_a where "slm_a = (1::nat)"\n\n'
                    'end\n')

        # Step 3: check B — A fails, B stale
        resp = check(b_path, self.repl)
        self.assertNotEqual(resp["target"]["status"], "ok")

        # Step 4: fix A (restore)
        with open(a_path, 'w') as f:
            f.write('theory SLM_A\n  imports Main\nbegin\n\n'
                    'definition slm_a where "slm_a = (1::nat)"\n\n'
                    'end\n')

        # Step 5: check B — must not crash, must succeed
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok",
                         msg=f"Expected ok after fixing dep, got: "
                             f"{resp.get('error')}")
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=f"Expected target ok: {resp.get('target')}")

    def test_load_theory_leak(self):
        """Ir.load_theory error from one theory should not leak into another.

        Same session: B imports A, D imports C (independent chains).
        Check D (loads C, D). Break C. Recheck D (stale — correct).
        Now check B — should load A fine, but Ir.load_theory sees
        the broken C and raises, even though A doesn't depend on C.
        """
        dep_dir = fixture_dir("load_theory_leak")
        b_path = os.path.join(dep_dir, "LTL_B.thy")
        c_path = os.path.join(dep_dir, "LTL_C.thy")
        d_path = os.path.join(dep_dir, "LTL_D.thy")

        # Step 1: check D — loads C and D
        resp = check(d_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")

        # Step 2: break C
        with open(c_path, 'w') as f:
            f.write('theory LTL_C imports Main begin\n'
                    'lemma "False" by simp\n'
                    'end\n')

        # Step 3: recheck D — should detect broken C
        resp = check(d_path, self.repl)
        self.assertNotEqual(resp["target"]["status"], "ok")

        # Step 4: check B — A is fine, should succeed
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=f"B should succeed (A is fine): {resp['target']}")

    def test_chain_rebuild_intermediate_then_check_downstream(self):
        """Rebuilding intermediate dep via check must not crash downstream.

        A → B → C chain. check(C) loads A and B via Ir.load_theory,
        C gets REPL. Then change A and check(B) — B is rebuilt as
        target (new REPL). Now check(C): C's SteppedMarker dep_hash
        for B has changed → NoRepl → CheckPlan(REBASE or INIT).

        Bug: Ir.rebase/Ir.init for C references B's old theory
        identity (from Ir.load_theory in step 1), but that entry was
        destroyed when Ir.load_theory rebuilt B in step 3. The REBASE
        crashes with "undefined entry for theory".

        Sequence:
        1. check(C) — A, B loaded from file; C stepped in REPL.
        2. Change A (cir_a = 1 → 99).
        3. check(B) — A reloaded, B checked OK as target (REPL).
        4. check(C) — must not crash; C's proof should fail
           (cir_b = 99+1 = 100, not 2).
        """
        dep_dir = fixture_dir("chain_intermediate_rebuild")
        a_path = os.path.join(dep_dir, "CIR_A.thy")
        b_path = os.path.join(dep_dir, "CIR_B.thy")
        c_path = os.path.join(dep_dir, "CIR_C.thy")

        # Step 1: check C
        resp = check(c_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Step 2: change A
        with open(a_path, 'w') as f:
            f.write('theory CIR_A\n  imports Main\nbegin\n\n'
                    'definition cir_a where "cir_a = (99::nat)"\n\n'
                    'end\n')

        # Step 3: check B (as target, not C)
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Step 4: check C — must not crash
        resp = check(c_path, self.repl)
        self.assertEqual(resp["status"], "ok",
                         msg=f"check(C) crashed: {resp.get('error')}")
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"Expected proof failure (cir_b=100≠2): "
                             f"{resp.get('target')}")

    def test_dep_reload_transitive_change(self):
        """Changing a transitive dependency invalidates the target on re-check.

        DRT_C imports DRT_B imports DRT_A. After changing DRT_A so val_a = 42,
        re-checking DRT_C should fail because val_b = val_a + 1 = 43, not 2.
        """
        dep_dir = fixture_dir("dep_reload_transitive")
        a_path = os.path.join(dep_dir, "DRT_A.thy")
        c_path = os.path.join(dep_dir, "DRT_C.thy")

        # First check: DRT_C passes (val_a=1, val_b=2, lemma holds)
        resp = check(c_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")

        # Modify DRT_A: change val_a from 1 to 42
        with open(a_path, 'w') as f:
            f.write('theory DRT_A\n  imports Main\nbegin\n\n'
                    'definition val_a where "val_a = (42::nat)"\n\n'
                    'end\n')

        # Re-check DRT_C: should fail because val_b = 43, not 2
        resp = check(c_path, self.repl)
        self.assertEqual(resp["target"]["status"], "error")
        self.assertEqual(resp["target"]["error"],
                         'Failed to apply initial proof method:\n'
                         'goal (1 subgoal):\n'
                         ' 1. 42 + 1 = 2\n'
                         'At command "by"')
        self.assertEqual(resp["target"]["line"], 6)

    def test_inner_locale(self):
        """Theory with an inner locale block should check successfully."""
        resp = check(
            fixture_file("inner_locale", "Inner_Test"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        t = resp["target"]
        self.assertEqual(t["status"], "ok",
                         msg=f"error at line {t.get('line')}: {t.get('error')}")

    @unittest.skipIf(_is_remote, "requires Ir.load_theory for keywords dep")
    def test_header_keywords(self):
        """Keywords theory can't be checked directly, but importing it works."""
        resp = check(
            fixture_file("header_keywords", "KW_Test"),
            self.repl)
        self.assertEqual(resp["status"], "error")
        self.assertIn("keywords", resp["error"])

        # KW_User imports KW_Test and uses dummy_kw — works because
        # the dep is loaded via Ir.load_theory, not stepped via REPL.
        resp = check(
            fixture_file("header_keywords", "KW_User"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        t = resp["target"]
        self.assertEqual(t["status"], "ok",
                         msg=f"error at line {t.get('line')}: {t.get('error')}")

    def test_qualified_command(self):
        """Theory with qualified datatype_record in context block."""
        resp = check(
            fixture_file("qualified_command", "QC_Test"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        t = resp["target"]
        self.assertEqual(t["status"], "ok",
                         msg=f"error at line {t.get('line')}: {t.get('error')}")

    def test_external_imports_with_hidden_dep_order(self):
        """Two ExternalImports with a hidden dep relationship don't crash.

        EDO_Target imports HOL-Library.AList_Mapping AND HOL-Library.Mapping
        directly. AList_Mapping itself imports Mapping, but I/C can't see
        external imports' dependency graph — both are classified as
        ExternalImport with no edges between them.

        Topological sort orders ExternalImports alphabetically, so
        AList_Mapping is loaded first and Ir.load_theory pulls Mapping
        transitively into the heap. When the executor then runs Mapping's
        LoadFilePlan, Ir.load_theory returns (success=True, rebuilt=False).
        execute_load_file_plan must accept this for ExternalImports rather
        than tripping its `assert rebuilt` (which still guards FileImports).
        """
        resp = check(
            fixture_file("external_dep_order", "EDO_Target"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        t = resp["target"]
        self.assertEqual(t["status"], "ok",
                         msg=f"error at line {t.get('line')}: {t.get('error')}")

    def test_ml_comment_in_imports(self):
        """Theory with (* ... *) comment in imports should check successfully."""
        resp = check(
            fixture_file("ml_comment_in_imports", "CH_Main"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        t = resp["target"]
        self.assertEqual(t["status"], "ok",
                         msg=f"error at line {t.get('line')}: {t.get('error')}")

    def test_cross_session(self):
        """Check B in SessionB; A loaded via Ir.load_theory from SessionA."""
        sessions_dir = fixture_dir("sessions")
        b_path = os.path.join(sessions_dir, "session_b", "B.thy")
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 1)

    def test_cross_session_separate_dirs(self):
        """Cross-session check with two separate -d directories (no ROOTS file)."""
        sessions_dir = fixture_dir("sessions")
        b_path = os.path.join(sessions_dir, "session_b", "B.thy")
        resp = check(
            b_path, self.repl)
        self.assertEqual(resp["status"], "ok")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 1)

    def test_cross_session_base(self):
        """Cross-session check where SessionB = SessionA + (base session dep)."""
        base_dir = fixture_dir("sessions_base")
        b_path = os.path.join(base_dir, "session_b", "B.thy")
        resp = check(
            b_path, self.repl)
        self.assertEqual(resp["status"], "ok")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 1)

    def test_comments_and_markup(self):
        """Theory with text, section, subsection, (* *) and \\<comment> should check."""
        resp = check(
            fixture_file("comments_and_markup", "Markup_Test"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        t = resp["target"]
        self.assertEqual(t["status"], "ok",
                         msg=f"error at line {t.get('line')}: {t.get('error')}")

    def test_keywords_inside_header_comment_not_rejected(self):
        """A theory whose header contains the literal word `keywords` only
        inside a comment must still be checked normally — `has_keywords`
        detection must run after comment-stripping, not against the raw
        header text.
        """
        resp = check(
            fixture_file("keywords_in_comment", "KIC_File"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        t = resp["target"]
        self.assertEqual(t["status"], "ok",
                         msg=f"error at line {t.get('line')}: {t.get('error')}")
        self.assertEqual(t["steps_taken"], 1,
                         "theory has a single body command")

    def test_missing_terminating_end_not_silently_accepted(self):
        """A theory file without a terminating `end` on its own line must
        not be reported as ok — the parser has to surface the malformation
        either at the top level or on the target dep, so users relying on
        I/C as a pre-flight check don't see a green status on a file that
        `isabelle build` would reject.
        """
        resp = check(
            fixture_file("missing_end", "ME_File"),
            self.repl)
        if resp.get("status") == "error":
            return
        t = resp.get("target", {})
        self.assertNotEqual(
            t.get("status"), "ok",
            "I/C reported OK on a theory file with no terminating `end`; "
            "expected an error that surfaces the malformation to the user")

    def test_comment_in_imports(self):
        """Theory with \\<comment> block in imports header should check."""
        resp = check(
            fixture_file("comment_in_imports", "CII_B"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

    def test_unlisted_import(self):
        """Theory importing an unlisted-in-ROOT theory from the same session."""
        # Check the unlisted file directly
        resp = check(
            fixture_file("unlisted_import", "Unlisted_A"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Check a listed file that imports the unlisted one
        resp = check(
            fixture_file("unlisted_import", "Listed_B"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

    def test_root_directories_cross_session(self):
        """Cross-session import of a theory in a ROOT directories subdirectory."""
        resp = check(
            fixture_file("root_directories_cross", "Cross_C"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

    def test_loaded_theory_shadows_file_dep(self):
        """Loaded theory in loaded_theories should not shadow file dependency.

        After checking Shadow_Target (which loads Shadow_Dep via
        Ir.load_theory), ShadowA.Shadow_Dep appears in Ir.theories().
        On the next check, resolve_import sees it in loaded_theories and
        returns 'heap' instead of recognizing it as a file dep. If
        Shadow_Dep is then modified, the change goes undetected.
        """
        dep_dir = fixture_dir("loaded_shadows_file")
        target = os.path.join(dep_dir, "session_b", "Shadow_Target.thy")
        dep_file = os.path.join(dep_dir, "session_a", "Shadow_Dep.thy")

        # First check — loads Shadow_Dep, checks Shadow_Target
        resp = check(target, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Modify Shadow_Dep: shadow_val = 1 → 42
        with open(dep_file, 'w') as f:
            f.write('theory Shadow_Dep\n  imports Main\nbegin\n\n'
                    'definition shadow_val where "shadow_val = (42::nat)"\n\n'
                    'end\n')

        # Re-check — should detect changed dep and fail
        resp = check(target, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"Expected proof failure, got: {resp['target']}")

    def test_loaded_dep_checked_with_new_content(self):
        """Dep loaded via Ir.load_theory, then checked with different content.

        After check(B) loads A and creates B's REPL, editing A and
        checking A directly creates a REPL for A with new content.
        Re-checking B must see the NEW A content (lrs_a=42), not the
        stale loaded version (lrs_a=1).

        Bug: B's REPL is re-created with the Ir.load_theory name as
        parent instead of the REPL. The loaded theory still has
        lrs_a=1, so B's proof "lrs_b = 2" silently passes when it
        should fail (42+1≠2).

        Sequence:
        1. check(B) — A loaded via Ir.load_theory (lrs_a=1), B OK.
        2. Edit A (lrs_a = 1 → 42).
        3. check(A) — creates REPL for A with lrs_a=42.
        4. check(B) — must see lrs_a=42; proof "lrs_b = 2" must fail.
        """
        dep_dir = fixture_dir("loaded_to_repl_stale")
        a_path = os.path.join(dep_dir, "LRS_A.thy")
        b_path = os.path.join(dep_dir, "LRS_B.thy")

        # Step 1: check B — A loaded from file, B checked OK
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")

        # Step 2: edit A
        with open(a_path, 'w') as f:
            f.write('theory LRS_A\n  imports Main\nbegin\n\n'
                    'definition lrs_a where "lrs_a = (42::nat)"\n\n'
                    'end\n')

        # Step 3: check A directly — creates REPL with lrs_a=42
        resp = check(a_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")

        # Step 4: check B — must detect A's new content
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"B should fail (lrs_a=42, 42+1≠2): "
                             f"{resp.get('target')}")

    def test_same_name_theories(self):
        """Two sessions with theories named Common, disambiguated by session prefix.

        SameNameA and SameNameB both have Common.thy (different content).
        UserA imports SameNameA.Common, UserB imports SameNameB.Common.
        I/C must use the session prefix to pick the right Common.
        """
        resp = check(
            fixture_file("same_name_theories/session_c", "UserA"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        resp = check(
            fixture_file("same_name_theories/session_c", "UserB"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

    def test_rebase_chain_leaf_check(self):
        """A→B→C chain, all REPLs. Change A, check C: must not crash.

        After all three theories are checked individually (creating
        REPLs with pin chains C→B→A), editing A and checking C should
        propagate the staleness through B to C and rebuild both.

        Bug: build_plans assigns LoadFilePlan to B (NoRepl dep without
        always_stepwise) even though B is rebase-compatible. C gets
        CheckPlan(REBASE) (target path uses rebase_set). B's LoadFilePlan
        requires removing B's REPL. expand_with_pin_dependents then
        marks C for removal too (C pins B). But C is in to_keep
        (REBASE). Assertion: REBASE/INIT conflict.

        Expected: B should be rebuilt via REPL (CheckPlan REBASE or
        INIT), not LoadFilePlan. The check should succeed and detect
        the value change (rcc_b = 42+1 = 43, not 2).
        """
        dep_dir = fixture_dir("rebase_chain_conflict")
        a_path = os.path.join(dep_dir, "RCC_A.thy")
        b_path = os.path.join(dep_dir, "RCC_B.thy")
        c_path = os.path.join(dep_dir, "RCC_C.thy")

        # Step 1: check A, B, C — creates REPL chain
        for path in (a_path, b_path, c_path):
            resp = check(path, self.repl)
            self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
            self.assertEqual(resp["target"]["status"], "ok",
                             msg=resp["target"].get("error"))

        # Step 2: change A
        with open(a_path, 'w') as f:
            f.write('theory RCC_A\n  imports Main\nbegin\n\n'
                    'definition rcc_a where "rcc_a = (42::nat)"\n\n'
                    'end\n')

        # Step 3: check C — must not crash; should detect change
        resp = check(c_path, self.repl)
        self.assertEqual(resp["status"], "ok",
                         msg=f"check(C) crashed: {resp.get('error')}")
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"Expected proof failure (rcc_b=43≠2): "
                             f"{resp.get('target')}")

    def test_interleaved_check_stale_dep(self):
        """Dep change must propagate to ALL targets sharing that dep.

        T1 and T2 both import Dep. After checking both (Dep gets a
        LoadedMarker), modifying Dep, and checking T1 (which reloads
        Dep), T2 must ALSO detect the change on its next check.

        BUG: After T1's check reloads Dep, T2's REPL still holds the
        old theory identity. has_persistent_repl sees the bare theory
        name in T2's origin matches current_import_spec (Dep has no
        stepped REPL, just a LoadedMarker) → rebase-compatible. But
        Ir.rebase doesn't re-resolve bare names, so T2 keeps the stale
        context.
        """
        dep_dir = fixture_dir("interleaved_dep_stale")
        dep_path = os.path.join(dep_dir, "IDS_Dep.thy")
        t1_path = os.path.join(dep_dir, "IDS_T1.thy")
        t2_path = os.path.join(dep_dir, "IDS_T2.thy")

        # Step 1: check both targets (Dep loaded for each)
        resp = check(t1_path, self.repl)
        self.assertEqual(resp["target"]["status"], "ok")
        resp = check(t2_path, self.repl)
        self.assertEqual(resp["target"]["status"], "ok")

        # Step 2: modify Dep
        with open(dep_path, 'w') as f:
            f.write('theory IDS_Dep\n  imports Main\nbegin\n\n'
                    'definition ids_val where "ids_val = (99::nat)"\n\n'
                    'end\n')

        # Step 3: check T1 — should detect change and fail
        resp = check(t1_path, self.repl)
        self.assertEqual(resp["target"]["status"], "error",
                         msg="T1 should fail (ids_val=99≠1)")

        # Step 4: check T2 — MUST also detect change and fail
        resp = check(t2_path, self.repl)
        self.assertNotEqual(
            resp["target"]["status"], "ok",
            msg="T2 must detect dep change after T1's check reloaded "
                "it. T2's REPL was built against ids_val=1, but Dep "
                f"now has ids_val=99. Got: {resp['target']}")

    def test_unlisted_cross_session_import(self):
        """Cross-session import of a theory not listed in the source session's ROOT."""
        # Check the unlisted file directly
        resp = check(
            fixture_file("unlisted_cross_session/session_a", "Unlisted_Y"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Check a file that imports the unlisted one cross-session
        resp = check(
            fixture_file("unlisted_cross_session/session_b", "Cross_B"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

    def test_root_subdir_theories(self):
        """Theories in ROOT subdirectories: direct check, same-session, cross-session."""
        # Check the subdirectory theory directly
        resp = check(
            os.path.join(fixture_dir("root_subdir"), "sub", "SD_Sub.thy"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

        # Check same-session import via relative path
        resp = check(
            fixture_file("root_subdir", "SD_Top"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Check cross-session import via qualified name
        resp = check(
            fixture_file("root_subdir_cross", "SD_Cross"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

    @unittest.skipIf(_is_remote, "requires Ir.load_theory")
    def test_diamond_reload_strategy(self):
        """Diamond resolved via reload: A is loaded from source."""
        d = fixture_dir("dep_diamond_reload")
        resp1 = check(
            os.path.join(d, "DiaR_A.thy"), self.repl)
        self.assertEqual(resp1["status"], "ok")
        resp2 = check(
            os.path.join(d, "DiaR_C.thy"), self.repl,
            diamond_strategy=DiamondStrategy.RELOAD)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok",
                         msg=resp2["target"].get("error"))
        a_dep = find_dep(resp2, "DiaR_A")
        self.assertIsNotNone(a_dep)
        self.assertEqual(a_dep["resolution"], "from_file")
        b_dep = find_dep(resp2, "DiaR_B")
        self.assertIsNotNone(b_dep)
        self.assertEqual(b_dep["resolution"], "from_file")

    def test_diamond_repl_strategy(self):
        """Diamond resolved via repl: B is stepped instead of Ir.load_theory."""
        d = fixture_dir("dep_diamond_repl")
        resp1 = check(
            os.path.join(d, "DiaP_A.thy"), self.repl)
        self.assertEqual(resp1["status"], "ok")
        resp2 = check(
            os.path.join(d, "DiaP_C.thy"), self.repl,
            diamond_strategy=DiamondStrategy.REPL)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok",
                         msg=resp2["target"].get("error"))
        b_dep = find_dep(resp2, "DiaP_B")
        self.assertIsNotNone(b_dep)
        self.assertEqual(b_dep["resolution"], "repl")
        self.assertEqual(b_dep["status"], "ok")

    @unittest.skipIf(_is_remote, "requires Ir.load_theory")
    def test_diamond_heuristic_picks_reload(self):
        """Heuristic picks reload when A is small and B is large."""
        d = fixture_dir("dep_diamond_heur_reload")
        resp1 = check(
            os.path.join(d, "SmA_A.thy"), self.repl)
        self.assertEqual(resp1["status"], "ok")
        resp2 = check(
            os.path.join(d, "SmA_C.thy"), self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok",
                         msg=resp2["target"].get("error"))
        a_dep = find_dep(resp2, "SmA_A")
        self.assertIsNotNone(a_dep)
        self.assertEqual(a_dep["resolution"], "from_file")
        b_dep = find_dep(resp2, "SmA_B")
        self.assertIsNotNone(b_dep)
        self.assertEqual(b_dep["resolution"], "from_file")

    def test_diamond_heuristic_picks_repl(self):
        """Heuristic picks repl when A is large and B is small."""
        d = fixture_dir("dep_diamond_heur_repl")
        resp1 = check(
            os.path.join(d, "LgA_A.thy"), self.repl)
        self.assertEqual(resp1["status"], "ok")
        resp2 = check(
            os.path.join(d, "LgA_C.thy"), self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok",
                         msg=resp2["target"].get("error"))
        b_dep = find_dep(resp2, "LgA_B")
        self.assertIsNotNone(b_dep)
        self.assertEqual(b_dep["resolution"], "repl")
        self.assertEqual(b_dep["status"], "ok")

    @unittest.skipIf(_is_remote, "requires Ir.load_theory")
    def test_diamond_heuristic_global_resolution(self):
        """Global diamond resolution: both B and C use RELOAD.

        With B(1 def) < A(5 defs) < C(10 defs), check A then check D:
        Global: RELOAD cost = 5 (A), REPL cost = 1+10 = 11 (B+C).
        5 ≤ 11 → RELOAD. Both B and C loaded from file.
        """
        d = fixture_dir("dep_diamond_suboptimal")

        # Check A → REPL created
        resp1 = check(os.path.join(d, "Sub_A.thy"), self.repl)
        self.assertEqual(resp1["target"]["status"], "ok",
                         msg=f"error: {resp1['target'].get('error')}")

        # Check D → global resolution picks RELOAD for both B and C
        resp2 = check(os.path.join(d, "Sub_D.thy"), self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok",
                         msg=f"error: {resp2['target'].get('error')}")
        # All deps resolved via file loading
        a_dep = find_dep(resp2, "Sub_A")
        self.assertIsNotNone(a_dep)
        self.assertEqual(a_dep["resolution"], "from_file")
        b_dep = find_dep(resp2, "Sub_B")
        self.assertIsNotNone(b_dep)
        self.assertEqual(b_dep["resolution"], "from_file")
        c_dep = find_dep(resp2, "Sub_C")
        self.assertIsNotNone(c_dep)
        self.assertEqual(c_dep["resolution"], "from_file")

    def test_dep_reuses_repl(self):
        """Checking B after A reuses A's REPL state (no Ir.load_theory)."""
        resp1 = check(
            fixture_file("dep_chain", "DC_A"),
            self.repl)
        self.assertEqual(resp1["status"], "ok")
        self.assertEqual(resp1["target"]["status"], "ok")

        resp2 = check(
            fixture_file("dep_chain", "DC_B"),
            self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok")
        dc_a = find_dep(resp2, "DC_A")
        self.assertIsNotNone(dc_a)
        self.assertEqual(dc_a["resolution"], "repl")

        # Recheck: B should be detected as unchanged (not false-changed
        # due to symbol encoding mismatch between Ir.text() and disk)
        resp3 = check(
            fixture_file("dep_chain", "DC_B"),
            self.repl)
        self.assertEqual(resp3["target"]["status"], "ok")
        self.assertEqual(resp3["target"]["steps_taken"], 0,
                         msg="Recheck after REPL dep should detect no changes")

    def test_dep_reuses_repl_with_symbols(self):
        r"""REPL dep with Isabelle symbols: check A, check B, recheck B.

        DCS_A and DCS_B use \<open>, \<equiv>, \<Rightarrow> throughout.
        B references constants from A. Recheck must not false-detect
        changes due to symbol encoding (Ir.text() returns Unicode,
        disk has \<symbol> notation).
        """
        d = fixture_dir("dep_chain_symbols")
        resp1 = check(os.path.join(d, "DCS_A.thy"), self.repl)
        self.assertEqual(resp1["status"], "ok", msg=resp1.get("error"))
        self.assertEqual(resp1["target"]["status"], "ok",
                         msg=f"error: {resp1['target'].get('error')}")

        resp2 = check(os.path.join(d, "DCS_B.thy"), self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok",
                         msg=f"error: {resp2['target'].get('error')}")
        dcs_a = find_dep(resp2, "DCS_A")
        self.assertIsNotNone(dcs_a)
        self.assertEqual(dcs_a["resolution"], "repl")

        # Recheck B: must detect no changes despite symbol encoding differences
        resp3 = check(os.path.join(d, "DCS_B.thy"), self.repl)
        self.assertEqual(resp3["target"]["status"], "ok")
        self.assertEqual(resp3["target"]["steps_taken"], 0,
                         msg="Recheck should detect no changes (symbol encoding mismatch?)")

    def test_dep_order_conflict(self):
        """Check B (loads A from file), check A (creates REPL), check D.

        D imports B and C. B has a REPL (built on file-loaded A). A has a REPL
        (different theory object). C has NO REPL and imports A — triggering
        diamond resolution. The diamond REPL strategy creates C's REPL with
        parents including B's REPL (file-A ancestry) and A's REPL (REPL-A).
        Without proper handling, Ir.init fails with 'Duplicate theory name'.
        """
        d = fixture_dir("dep_order_conflict")

        # Step 1: Check B — A loaded from file, B REPL created on file-A
        resp1 = check(os.path.join(d, "Ord_B.thy"), self.repl)
        self.assertEqual(resp1["status"], "ok", msg=resp1.get("error"))
        self.assertEqual(resp1["target"]["status"], "ok",
                         msg=f"error: {resp1['target'].get('error')}")

        # Step 2: Check A — creates REPL (new theory object, differs from file-A)
        resp2 = check(os.path.join(d, "Ord_A.thy"), self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok",
                         msg=f"error: {resp2['target'].get('error')}")

        # Step 3: Check D — B and A from REPL, C needs loading (diamond).
        # Force REPL strategy to trigger the conflict (heuristic picks
        # RELOAD for small files which avoids it).
        resp3 = check(os.path.join(d, "Ord_D.thy"), self.repl,
                       diamond_strategy=DiamondStrategy.REPL)
        self.assertEqual(resp3["status"], "ok", msg=resp3.get("error"))
        self.assertEqual(resp3["target"]["status"], "ok",
                         msg=f"error: {resp3['target'].get('error')}")

    def test_check_two_different_files(self):
        """Checking two different files in sequence (no clean in between)."""
        resp1 = check(
            fixture_file("check_all", "Check_All"),
            self.repl)
        self.assertEqual(resp1["status"], "ok")
        self.assertEqual(resp1["target"]["status"], "ok")

        resp2 = check(
            fixture_file("status", "Status_Test"),
            self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok")

    def test_instantiation(self):
        """instantiation works directly (no locale wrapping, no special flag)."""
        resp = check(
            fixture_file("instantiation", "Inst_Test"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        t = resp["target"]
        self.assertEqual(t["status"], "ok",
                         msg=f"error at line {t.get('line')}: {t.get('error')}")

    def test_smt_proof(self):
        """SMT proofs should work (requires Bash.Server for solver access)."""
        resp = check(
            fixture_file("smt_proof", "SMT_Test"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        t = resp["target"]
        self.assertEqual(t["status"], "ok",
                         msg=f"error at line {t.get('line')}: {t.get('error')}")

    def test_recheck_with_isabelle_symbols(self):
        r"""Recheck a file using \<open>, \<close>, \<Rightarrow> etc.

        Isabelle's Ir.text() returns Unicode (e.g. \u2039) while the disk
        file uses \\<open>. The symbol normalization must prevent false
        change detection on recheck.
        """
        path = fixture_file("isabelle_symbols", "Sym_Test")
        resp1 = check(path, self.repl)
        self.assertEqual(resp1["status"], "ok", msg=resp1.get("error"))
        self.assertEqual(resp1["target"]["status"], "ok",
                         msg=f"error: {resp1['target'].get('error')}")
        self.assertGreater(resp1["target"]["steps_taken"], 0)

        resp2 = check(path, self.repl)
        self.assertEqual(resp2["target"]["status"], "ok")
        self.assertEqual(resp2["target"]["steps_taken"], 0,
                         msg="Recheck should detect no changes (symbol encoding mismatch?)")

    def test_over_eager_parents(self):
        """Dep REPL should only see its own imports, not all transitive deps.

        OE_A and OE_B both define 'clash' with different types. OE_C imports
        only OE_A. First check OE_A to create a stepped REPL. Then check
        OE_Target: OE_C has a diamond conflict (imports OE_A which has an
        active REPL) → REPL strategy → CheckPlan. execute_plans passes all
        prior deps (including OE_B) as parents, causing a name clash.
        """
        # Step 1: create a REPL for OE_A
        resp = check(
            fixture_file("over_eager_parents", "OE_A"),
            self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

        # Step 2: check target with REPL strategy — forces CheckPlan for OE_C
        resp = check(
            fixture_file("over_eager_parents", "OE_Target"),
            self.repl,
            diamond_strategy=DiamondStrategy.REPL)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

    def test_parent_order(self):
        """REPL parent order should match theory import order.

        PO_A and PO_B both define 'clash' with different types.
        PO_C imports PO_B then PO_A. ensure_repl sorts parents
        alphabetically, reversing the order.
        """
        resp = check(
            fixture_file("parent_order", "PO_A"), self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

        resp = check(
            fixture_file("parent_order", "PO_Target"),
            self.repl,
            diamond_strategy=DiamondStrategy.REPL)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        po_c = find_dep(resp, "PO_C")
        self.assertIsNotNone(po_c)
        self.assertEqual(po_c.get("status"), "ok",
                         msg=po_c.get("error"))

    def test_stale_repl_dep_detected(self):
        """Changing A should invalidate B's REPL when checking C.

        B has a REPL from checking B earlier. A's file changes (val_a
        from 1 to 42). B's file is unchanged but B's REPL context is
        stale. C's lemma "val_b = 2" should fail (val_b is now 43).
        """
        dep_dir = fixture_dir("dep_stale_repl")
        a_path = os.path.join(dep_dir, "SR_A.thy")
        b_path = os.path.join(dep_dir, "SR_B.thy")
        c_path = os.path.join(dep_dir, "SR_C.thy")

        # Check B — A loaded via Ir.load_theory, B checked via REPL
        resp1 = check(b_path, self.repl)
        self.assertEqual(resp1["status"], "ok", msg=resp1.get("error"))
        self.assertEqual(resp1["target"]["status"], "ok",
                         msg=resp1["target"].get("error"))

        # Edit A: val_a = 42
        with open(a_path, 'w') as f:
            f.write('theory SR_A\n  imports Main\nbegin\n\n'
                    'definition val_a where "val_a = (42::nat)"\n\nend\n')

        # Check C: B's REPL is stale (built on old A).
        # Expected: C should detect the problem — either by invalidating
        # B's REPL and re-checking, or by reporting an error.
        # Current bug: crashes with "Duplicate theory name" because
        # B's REPL has old A identity but load_theory gives new A.
        resp2 = check(c_path, self.repl)
        # Should succeed (with B re-checked) or report a target error,
        # but NOT a top-level Ir.init crash
        self.assertNotIn("Duplicate theory name", resp2.get("error", ""))
        self.assertEqual(resp2["target"]["status"], "error",
                         msg=f"Expected target error, got: {resp2.get('target', resp2)}")

    def test_file_not_in_root_error(self):
        """Error when checking a file outside any session directory."""
        # Create a .thy file outside any session directory
        tmpdir = tempfile.mkdtemp(prefix="ics_test_no_root_")
        orphan = os.path.join(tmpdir, "Orphan.thy")
        with open(orphan, "w") as f:
            f.write('theory Orphan imports Main begin end\n')
        try:
            resp = check(orphan, self.repl)
            self.assertEqual(resp["status"], "error")
            self.assertIn("not in any session", resp["error"])
        finally:
            shutil.rmtree(tmpdir, ignore_errors=True)

    # --- Client output formatting tests ---

    def capture_output(self, response):
        """Pass a response through print_response, capture output."""
        out = io.StringIO()
        err = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            has_errors = print_response(response)
        return out.getvalue(), err.getvalue(), has_errors

    def test_client_ok_hides_deps(self):
        """Successful check: only target shown, deps hidden."""
        resp = check(
            fixture_file("client_dep_ok", "Cli_B"),
            self.repl)
        out, err, has_errors = self.capture_output(resp)
        self.assertFalse(has_errors)
        self.assertEqual(out, "  OK   Cli_B\n")
        self.assertEqual(err, "")

    def test_client_target_error(self):
        """Target fails: error line and message shown."""
        resp = check(
            fixture_file("check_error", "Check_Error"),
            self.repl)
        out, err, has_errors = self.capture_output(resp)
        self.assertTrue(has_errors)
        self.assertEqual(out,
                         '  ERR  Check_Error:6: '
                         'Failed to apply initial proof method:\n'
                         'goal (1 subgoal):\n'
                         ' 1. 0 = 1\n'
                         'At command "by"\n')
        self.assertEqual(err, "")

    @unittest.skipIf(_is_remote, "requires Ir.load_theory")
    def test_client_dep_failure_shows_reason(self):
        """Dep fails to load: dep error and target stale shown."""
        resp = check(
            fixture_file("dep_chain_a_broken", "DCA_B"),
            self.repl)
        out, err, has_errors = self.capture_output(resp)
        self.assertTrue(has_errors)
        dca_a_path = fixture_file("dep_chain_a_broken", "DCA_A")
        self.assertEqual(out,
                         f"  ERR  DCA_A: failed to load theory\n"
                         f"       try: ic_client.py check {dca_a_path}\n"
                         f"  ---  DCA_B  (stale: depends on failed DCA_A)\n")
        self.assertEqual(err, "")

    def test_client_server_error(self):
        """File not in ROOT: top-level error printed to stderr."""
        tmpdir = tempfile.mkdtemp(prefix="ics_test_no_root_")
        orphan = os.path.join(tmpdir, "Orphan.thy")
        with open(orphan, "w") as f:
            f.write('theory Orphan imports Main begin end\n')
        try:
            resp = check(orphan, self.repl)
            out, err, has_errors = self.capture_output(resp)
            self.assertTrue(has_errors)
            self.assertEqual(out, "")
            self.assertIn("Error:", err)
        finally:
            shutil.rmtree(tmpdir, ignore_errors=True)


    def test_empty_body_truncates_repl(self):
        """Emptying a file's body should truncate all REPL steps.

        Check EB_File (2 definitions), then overwrite with empty body,
        recheck. The REPL should have 0 steps — not retain stale steps
        from the previous check.
        """
        eb_path = fixture_file("empty_body", "EB_File")

        # Step 1: check — creates REPL with 2 steps
        resp = check(eb_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 2)

        # Step 2: overwrite with empty body
        with open(eb_path, 'w') as f:
            f.write('theory EB_File\n  imports Main\nbegin\nend\n')

        # Step 3: recheck — should succeed with 0 steps
        resp = check(eb_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Step 4: verify REPL actually has 0 steps
        from ic_check import bootstrap, parse_repls_output, strip_ml_noise, ml_expect
        _, active, _ = bootstrap(self.repl)
        repl_name = "ic.empty_body.EB_File"
        self.assertIn(repl_name, active,
                      msg=f"REPL {repl_name} should exist")
        self.assertEqual(active[repl_name].step_count, 0,
                         msg="REPL should have 0 steps after empty body")


    def test_stale_dep_recheck(self):
        """Checking B after A was rebuilt should restep B.

        Check A (REPL), check B (REPL, uses A). Modify A, check A
        (incremental rebuild). Then check B — B's REPL was built
        against the old A. B should be restepped, not skipped.
        """
        dep_dir = fixture_dir("stale_dep_recheck")
        a_path = os.path.join(dep_dir, "SDR_A.thy")
        b_path = os.path.join(dep_dir, "SDR_B.thy")

        # Step 1: check A
        resp = check(a_path, self.repl)
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Step 2: check B (depends on A via REPL)
        resp = check(b_path, self.repl)
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertGreater(resp["target"]["steps_taken"], 0)

        # Step 3: modify A (sdr_val = 1 → 42), check A
        with open(a_path, 'w') as f:
            f.write('theory SDR_A\n  imports Main\nbegin\n\n'
                    'definition sdr_val where "sdr_val = (42::nat)"\n\n'
                    'end\n')
        resp = check(a_path, self.repl)
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Step 4: check B — should detect stale dep and restep.
        # sdr_sum = sdr_val + 1 = 43, but proof says sdr_sum = 2 → error
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertNotEqual(resp["target"]["status"], "ok",
                            msg="B should not be ok — dep A was rebuilt "
                                "with different content")


    def test_parse_spans_incremental_with_malformed(self):
        """parse_spans via ML snippets works for incremental rebuild.
        Malformed input is parsed into <malformed> transitions, not errors."""
        from ic_check import bootstrap

        ps_dir = fixture_dir("parse_spans_safe")
        ps_file = os.path.join(ps_dir, "PS_File.thy")

        # 1. Initial check — creates REPL with steps
        resp = check(ps_file, self.repl, verbose=0)
        self.assertIn("target", resp, msg=f"Unexpected response: {resp}")
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp.get("target", resp))

        # 2. Append a command, re-check — incremental path via parse_spans
        with open(ps_file, "w") as f:
            f.write('theory PS_File imports Main begin\n'
                    'definition "foo = True"\n'
                    'definition "bar = False"\n'
                    'end\n')
        resp2 = check(ps_file, self.repl, verbose=0)
        self.assertEqual(resp2["target"]["status"], "ok",
                         msg=resp2.get("target", resp2))
        self.assertEqual(resp2["target"]["steps_taken"], 1,
                         "Should only step the appended command")

        # 3. Read back the REPL body to confirm state
        from ic_check import read_repl_body_text
        repl_name = "ic.ParseSpansSafe.PS_File"
        body_before = read_repl_body_text(self.repl, repl_name)

        # 4. Overwrite with unparseable content, re-check — parse_spans
        #    should fail internally but the REPL body must survive
        with open(ps_file, "w") as f:
            f.write('theory PS_File imports Main begin\n'
                    'definition "foo = True"\n'
                    'definition "bar = False"\n'
                    'definition "broken\n'
                    'end\n')
        resp3 = check(ps_file, self.repl, verbose=0)
        self.assertEqual(resp3["target"]["status"], "error")
        self.assertEqual(resp3["target"]["error"],
                         'Outer syntax error: proposition expected,\n'
                         'but bad input "broken was found\n'
                         'At command "<malformed>"')
        self.assertEqual(resp3["target"]["line"], 4)

        # 5. Verify the REPL body is unchanged — parse_spans failure
        #    must not have truncated or corrupted the existing steps
        body_after = read_repl_body_text(self.repl, repl_name)
        self.assertEqual(body_before, body_after,
                         "REPL body must survive a parse_spans failure")


    def test_timeout_set_on_repl(self):
        """Per-step timeout is forwarded to REPLs via Ir.timeout."""
        from ic_check import ml_expect, ml_escape, strip_ml_noise
        path = fixture_file("timeout_check", "TC_File")
        resp = check(path, self.repl, timeout=42)
        self.assertEqual(resp["status"], "ok")

        repl_name = "ic.timeout_check.TC_File"
        raw = strip_ml_noise(ml_expect(
            self.repl.send(f'Ir.show "{ml_escape(repl_name)}"')))
        self.assertIn("timeout=42s", raw)

        # Edit file and re-check with a different timeout
        with open(path, 'w') as f:
            f.write('theory TC_File\n  imports Main\nbegin\n\n'
                    'definition tc_val where "tc_val = (2::nat)"\n\n'
                    'end\n')
        resp2 = check(path, self.repl, timeout=99)
        self.assertEqual(resp2["status"], "ok")
        self.assertGreater(resp2["target"]["steps_taken"], 0)
        raw2 = strip_ml_noise(ml_expect(
            self.repl.send(f'Ir.show "{ml_escape(repl_name)}"')))
        self.assertIn("timeout=99s", raw2)

    @unittest.skipIf(_is_remote, "requires Ir.load_theory")
    def test_diamond_recheck_after_dep_change(self):
        """Diamond via load_theory: D imports B,C; both import A.

        Known bug: deps loaded via Ir.load_theory use LoadedMarker which
        doesn't track dep hashes. When A changes and B is rechecked, C's
        LoadedMarker still matches (C's own file unchanged), so C is
        reused with stale A content.
        """
        dep_dir = fixture_dir("diamond_recheck")
        a_path = os.path.join(dep_dir, "DR_A.thy")
        d_path = os.path.join(dep_dir, "DR_D.thy")
        b_path = os.path.join(dep_dir, "DR_B.thy")

        # Step 1: check D — deps loaded via Ir.load_theory
        resp = check(d_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertGreater(resp["target"]["steps_taken"], 0)

        # Step 2: change A, check B
        with open(a_path, 'w') as f:
            f.write('theory DR_A\n  imports Main\nbegin\n\n'
                    'definition dr_a where "dr_a = (5::nat)"\n\n'
                    'end\n')
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Step 3: check D — should see new A value through both B and C.
        with open(d_path, 'w') as f:
            f.write('theory DR_D\n  imports DR_B DR_C\nbegin\n\n'
                    'definition dr_d where "dr_d = dr_b + dr_c"\n\n'
                    'lemma "dr_d = 120"\n'
                    '  unfolding dr_d_def dr_b_def dr_c_def dr_a_def '
                    'by eval\n\n'
                    'end\n')
        resp = check(d_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=f"Expected ok (dr_d=15+105=120), got: "
                             f"{resp['target']}")

    def test_diamond_reload_stale_repl_identity(self):
        """Stale REPL identity: B's REPL has old A, C's has new A; D crashes.

        Setup: A → B, A → C, B+C → D.

        1. check(A) — creates REPL for A. check(B) — A: ReplClean →
           SkipPlan(import=A.repl_name). B gets REPL built on REPL-A.
        2. Edit A. check(C) — A: ReplChanged. As C's dep, A is rebuilt
           (IncrementalPlan or SegmentInit → new REPL for A). C gets
           REPL built on new REPL-A identity. B's REPL still has old
           REPL-A in ancestry.
        3. check(D):
           - A: ReplClean (matches post-edit marker).
           - B: dep_hash for A mismatches → NoRepl → LoadFilePlan.
           - C: ReplClean → SkipPlan(import=C.repl_name).
           - Diamond: B imports A which has REPL → conflict detected.
           - RELOAD: A → LoadFilePlan → Ir.load_theory (loaded-A identity).
             B → LoadFilePlan → Ir.load_theory (references loaded-A).
           - But C is SkipPlan(C.repl_name). C's REPL has REPL-A-gen2
             in ancestry. This differs from loaded-A.
           - D's Ir.init with parents [B.name, C.repl_name]:
             B.name has loaded-A, C.repl_name has REPL-A-gen2.
             Same theory name, different identity → Ir.init crash.

        Expected: D should check successfully, NOT crash with Ir.init failure.
        """
        d = fixture_dir("diamond_reload_changed")
        a_path = os.path.join(d, "DRC_A.thy")

        # Step 1: check A, then B — B's REPL built on REPL-A identity
        resp = check(os.path.join(d, "DRC_A.thy"), self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        resp = check(os.path.join(d, "DRC_B.thy"), self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Step 2: edit A, check C — A rebuilt with new REPL identity,
        # C's REPL built on new REPL-A
        with open(a_path, 'w') as f:
            f.write('theory DRC_A\n  imports Main\nbegin\n\n'
                    'definition drc_a where "drc_a = (42::nat)"\n\n'
                    'end\n')
        resp = check(os.path.join(d, "DRC_C.thy"), self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Step 3: check D.
        # Bug: B is NoRepl (dep hash stale) → LoadFilePlan → Ir.load_theory.
        # A and C have REPLs. Diamond detected for B (imports A).
        # RELOAD: A → LoadFilePlan (Ir.load_theory), B → LoadFilePlan.
        # But C is SkipPlan with REPL-A ancestry. D's parents include
        # loaded-A (via B) and REPL-A (via C) → Ir.init crash.
        resp = check(os.path.join(d, "DRC_D.thy"), self.repl)
        self.assertNotIn("Duplicate theory", resp.get("error", ""),
                         msg="Ir.init failed with duplicate theory — "
                             "RELOAD didn't invalidate sibling REPL C "
                             "which still has old REPL-A identity")
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

    def test_rebase_after_import_change(self):
        """A→B→C chain, all with REPLs. C uses ric_d (from D).

        Initially B imports only A, so C fails (ric_d not visible).
        After adding D to B's imports, check C succeeds.
        """
        d = fixture_dir("rebase_import_change")
        a_path = os.path.join(d, "RIC_A.thy")
        b_path = os.path.join(d, "RIC_B.thy")
        c_path = os.path.join(d, "RIC_C.thy")

        # Check A, D, B — all get REPLs
        resp = check(a_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        d_path = os.path.join(d, "RIC_D.thy")
        resp = check(d_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Check C — fails because ric_d is not visible (B doesn't import D)
        resp = check(c_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "error",
                         msg="C should fail: ric_d not in scope")

        # Add D to B's imports
        with open(b_path, 'w') as f:
            f.write('theory RIC_B\n  imports RIC_A RIC_D\nbegin\n\n'
                    'definition ric_b where "ric_b = ric_a + 10"\n\n'
                    'end\n')

        # Check B — B should be rebuilt with D in its parents.
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        from ic_check import bootstrap
        _, active_after_b, _ = bootstrap(self.repl)
        b_info = active_after_b.get("ic.rebase_import_change.RIC_B")
        self.assertIsNotNone(b_info, "B should have a REPL after check(B)")
        self.assertIn("RIC_D", b_info.origin,
                      f"B's origin should include D: {b_info.origin}")
        self.assertNotIn("ic.rebase_import_change.RIC_C", active_after_b,
                         "C's REPL should have been removed as collateral "
                         "of B's removal (C held pin@B in origin)")

        # Check C — should succeed now (ric_d visible via B)
        resp = check(c_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

    def test_status_shows_stale_no_orphans_repl_chain(self):
        """status() reports a stale marker without orphaning it.

        Plain HOL chain: X, A imports X, B imports A. After all three
        are checked individually and X is then changed, re-checking A
        as target rebases A (REPL kept alive, parent pins re-resolved,
        marker rewritten with the new dep_hashes[X]). B is never
        touched, so its marker still points at A's old hash and B's
        REPL still pins@ic.A.

        status() must:
        - report B in the Stale section (its dep A's marker changed),
        - emit no Orphan section (every stepped marker still has a
          live REPL: X via IncrementalPlan, A via REBASE, B untouched).
        """
        dep_dir = fixture_dir("status_stale_repl")
        x_path = os.path.join(dep_dir, "SSR_X.thy")
        a_path = os.path.join(dep_dir, "SSR_A.thy")
        b_path = os.path.join(dep_dir, "SSR_B.thy")

        # Step 1: check X, A, B — each gets a REPL with the right pin chain.
        for p in (x_path, a_path, b_path):
            resp = check(p, self.repl)
            self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
            self.assertEqual(resp["target"]["status"], "ok",
                             msg=resp["target"].get("error"))

        # Step 2: change X, then check A (target). A is ReplClean →
        # NoRepl by propagate, but rebase-compatible → CheckPlan(REBASE).
        with open(x_path, 'w') as f:
            f.write('theory SSR_X\n  imports Main\nbegin\n\n'
                    'definition ssr_x where "ssr_x = (2::nat)"\n\n'
                    'end\n')
        resp = check(a_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Status: B is stale (dep A's marker changed); no orphans.
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            status(self.repl, verbose=0)
        out = out.getvalue()
        self.assertIn("Stale", out,
                      msg=f"Expected stale section in status:\n{out}")
        self.assertIn("status_stale_repl.SSR_B", out)
        self.assertIn("marker changed", out)
        self.assertNotIn("Orphan", out,
                         msg="No marker should be orphaned when REBASE "
                             f"keeps the dep's REPL alive:\n{out}")


def find_isabelle(isabelle_path=None):
    """Find Isabelle installation. Raises unittest.SkipTest if not found.

    When `isabelle_path` is given, it is validated via
    repl.find_isabelle_installation (which accepts either the binary
    path or the Isabelle home directory). Otherwise falls back to that
    function's platform-specific default search.
    """
    sys.path.insert(0, IR_DIR)
    try:
        from repl import find_isabelle_installation
        return find_isabelle_installation(isabelle_path)
    except (ImportError, RuntimeError) as e:
        raise unittest.SkipTest(f"Isabelle not found: {e}")


def parse_isabelle_remote_opts() -> list[str]:
    """Parse ISABELLE_REMOTE env var into a list of Isabelle -o values."""
    import shlex
    raw = os.environ.get("ISABELLE_REMOTE", "")
    if not raw:
        return []
    tokens = shlex.split(raw)
    opts = []
    i = 0
    while i < len(tokens):
        if tokens[i] == '-o' and i + 1 < len(tokens):
            opts.append(tokens[i + 1])
            i += 2
        else:
            i += 1
    return opts


def build_session(isabelle, directory, session, extra_opts=None):
    """Build an Isabelle session. Raises unittest.SkipTest on failure."""
    cmd = [isabelle, "build", "-d", directory]
    for opt in (extra_opts or []) + parse_isabelle_remote_opts():
        cmd += ["-o", opt]
    cmd += ["-b", session]
    try:
        subprocess.run(cmd, check=True, capture_output=True,
                       text=True, timeout=300)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
        out = getattr(e, 'stdout', '') or ''
        err = getattr(e, 'stderr', '') or ''
        raise unittest.SkipTest(
            f"Failed to build {session}: {e}\n{out}\n{err}")


class TestHeapTheories(unittest.TestCase):
    """Tests requiring pre-built heap sessions (segment init, heap deps, etc).

    All heap sessions are built once and share a single REPL via the
    AllHeapTests parent session.
    """

    repl = None
    repl_proc = None
    isabelle_path = None  # set by main() from --isabelle / $ISABELLE

    @classmethod
    def setUpClass(cls):
        install_templates()  # .thy files must exist before build
        isabelle = find_isabelle(cls.isabelle_path)
        all_dir = fixture_dir("heap_all_tests")
        build_session(isabelle, all_dir, "AllHeapTests")

        # Skip Bash.Server locally (saves ~5s, only needed for sledgehammer).
        # The I/P proxy requires it as its communication bridge, so keep it
        # when ISABELLE_REMOTE is set.
        cls.repl_proc = ReplProcess(
            session="AllHeapTests", dirs=[all_dir],
            no_bash_server=not os.environ.get("ISABELLE_REMOTE"),
            isabelle=cls.isabelle_path)
        cls.repl = cls.repl_proc.start()
        clean(cls.repl)

    @classmethod
    def tearDownClass(cls):
        if cls.repl:
            try:
                clean(cls.repl)
            except Exception:
                pass
        if cls.repl_proc:
            cls.repl_proc.stop()
        remove_templates()

    def setUp(self):
        install_templates()
        clean(self.repl)

    # --- Heap dep tests (from TestHeapSession) ---

    def test_check_with_heap_dep(self):
        """Main_Thy imports TestBase.Base; Base should come from heap, not re-checked."""
        heap_dir = fixture_dir("heap_session")
        main_thy = os.path.join(heap_dir, "main", "Main_Thy.thy")
        resp = check(main_thy, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        base_dep = find_dep(resp, "Base")
        if base_dep:
            self.assertEqual(base_dep["resolution"], "from_heap")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 1)

        # Recheck: cached HeapVerifiedMarker path
        resp2 = check(main_thy, self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["status"], "ok")
        self.assertEqual(resp2["target"]["steps_taken"], 0)

    # --- Segment init tests (from TestSegmentInit) ---

    def test_segment_comment_unchanged(self):
        """Heap theory with (*>*) + \\<comment> should recheck as unchanged.

        (*>*) followed by \\<comment> blocks gets grouped into one span
        by parse_spans, but the heap doesn't record it as a segment.
        is_comment_only doesn't filter the combined text.
        """
        seg_file = fixture_file("segment_session", "Seg_Comment")
        resp = check(seg_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Recheck: cached HeapVerifiedMarker path
        resp2 = check(seg_file, self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["steps_taken"], 0)

    def test_segment_init_unchanged(self):
        """First check of unchanged file uses segment init (0 commands stepped)."""
        seg_file = fixture_file("segment_session", "Seg_File")
        resp = check(seg_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Recheck: cached HeapVerifiedMarker path
        resp2 = check(seg_file, self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["steps_taken"], 0)

    def test_segment_init_recheck(self):
        """Recheck after segment init detects unchanged file."""
        seg_file = fixture_file("segment_session", "Seg_File")
        resp1 = check(seg_file, self.repl)
        self.assertEqual(resp1["target"]["status"], "ok")
        self.assertEqual(resp1["target"]["steps_taken"], 0)
        resp2 = check(seg_file, self.repl)
        self.assertEqual(resp2["target"]["status"], "ok")
        self.assertEqual(resp2["target"]["steps_taken"], 0)

    def test_segment_init_changed_tail(self):
        """Changed file uses partial segment init, steps only tail."""
        seg_file = fixture_file("segment_session", "Seg_File")
        with open(seg_file) as f:
            original = f.read()
        modified = original.replace(
            "\nend",
            '\ndefinition seg_f where "seg_f = (6::nat)"\n\nend')
        with open(seg_file, 'w') as f:
            f.write(modified)
        resp = check(seg_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 1)

    def test_segment_init_changed_middle(self):
        """Edit in the middle of the file: steps only from the change onward."""
        seg_file = fixture_file("segment_session", "Seg_File")
        with open(seg_file) as f:
            original = f.read()
        modified = original.replace(
            'definition seg_c where "seg_c = (3::nat)"',
            'definition seg_c where "seg_c = (33::nat)"')
        with open(seg_file, 'w') as f:
            f.write(modified)
        resp = check(seg_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 3)

    def test_segment_init_plain_unchanged(self):
        """Segment init on a file without (*<*)(*>*) markers."""
        seg_file = fixture_file("segment_session", "Seg_Plain")
        resp = check(seg_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Recheck: cached HeapVerifiedMarker path
        resp2 = check(seg_file, self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["steps_taken"], 0)

    def test_segment_init_plain_changed_middle(self):
        """Edit plain file in the middle: steps only from change onward."""
        seg_file = fixture_file("segment_session", "Seg_Plain")
        with open(seg_file) as f:
            original = f.read()
        modified = original.replace(
            'definition sp_b where "sp_b = (2::nat)"',
            'definition sp_b where "sp_b = (22::nat)"')
        with open(seg_file, 'w') as f:
            f.write(modified)
        resp = check(seg_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 2)

    def test_segment_init_error_middle(self):
        """Introduce an error halfway: segment init, 1 step, error persists on recheck."""
        seg_file = fixture_file("segment_session", "Seg_Error")
        with open(seg_file) as f:
            original = f.read()
        modified = original.replace(
            'definition se_c where "se_c = (3::nat)"',
            'definition se_c where "se_c = (x::nat)"')
        with open(seg_file, 'w') as f:
            f.write(modified)

        resp1 = check(seg_file, self.repl)
        self.assertEqual(resp1["status"], "ok", msg=resp1.get("error"))
        t1 = resp1["target"]
        self.assertEqual(t1["status"], "error")
        self.assertEqual(t1["steps_taken"], 1)
        self.assertEqual(t1["line"], 9)
        self.assertIn("Extra variables on rhs", t1["error"])

        resp2 = check(seg_file, self.repl)
        self.assertEqual(resp2["status"], "ok", msg=repr(resp2))
        t2 = resp2["target"]
        self.assertEqual(t2["status"], "error")
        self.assertEqual(t2["line"], 9)
        self.assertIn("Extra variables on rhs", t2["error"])

    def test_segment_init_error_in_proof(self):
        """Break a proof tactic: segment init from inside the proof context."""
        seg_file = fixture_file("segment_session", "Seg_Proof")
        with open(seg_file) as f:
            original = f.read()
        modified = original.replace(
            'by (simp add: proof_val_def)',
            'by auto')
        with open(seg_file, 'w') as f:
            f.write(modified)
        resp = check(seg_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "error")
        self.assertEqual(resp["target"]["steps_taken"], 1)

    # --- Heap dep change tests (from TestSegmentDepChange) ---

    def test_heap_dep_change_invalidates_dependent(self):
        """Modify SD_A (heap dep), re-check SD_B: should detect stale dep.

        Both SD_A and SD_B are pre-built in the SegDepTest heap.
        After changing SD_A (sd_val = 1 -> 42), SD_B's proof
        "sd_sum = 2" should fail because sd_sum = sd_val + 1 = 43.
        """
        dep_dir = fixture_dir("segment_dep")
        b_path = os.path.join(dep_dir, "SD_B.thy")
        a_path = os.path.join(dep_dir, "SD_A.thy")

        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        # Both in heap, segment init — 0 steps for both
        self.assertEqual(resp["target"]["steps_taken"], 0)

        with open(a_path, 'w') as f:
            f.write('theory SD_A\n  imports Main\nbegin\n\n'
                    'definition sd_val where "sd_val = (42::nat)"\n\n'
                    'end\n')

        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"Expected proof failure, got: {resp['target']}")
        # SD_A: first command differs → init from header, step 1 command
        sd_a = find_dep(resp, "SD_A")
        self.assertIsNotNone(sd_a)
        self.assertEqual(sd_a["steps_taken"], 1)
        # SD_B: fully stepped (skip_segment_init since dep rebuilt)
        self.assertEqual(resp["target"]["steps_taken"], 4)

    def test_heap_stale_both_dep_and_target(self):
        """Change both dep and target on disk, check target.

        Both HSB_A and HSB_B are in the heap. After changing HSB_A
        (hsb_val = 1 → 42) AND HSB_B (proof expects hsb_sum = 43),
        the target should use the rebuilt dep, not the heap segment.

        Regression: propagate_staleness skipped HeapStale entries
        (is_rebuilding=True → continue), so the target stayed HeapStale
        → SegmentInitPlan, which inits from the stale heap segment
        instead of the rebuilt dep's REPL.
        """
        dep_dir = fixture_dir("heap_stale_both")
        a_path = os.path.join(dep_dir, "HSB_A.thy")
        b_path = os.path.join(dep_dir, "HSB_B.thy")

        # Step 1: both unchanged, from heap
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Step 2: change BOTH files
        with open(a_path, 'w') as f:
            f.write('theory HSB_A\n  imports Main\nbegin\n\n'
                    'definition hsb_val where "hsb_val = (42::nat)"\n\n'
                    'end\n')
        with open(b_path, 'w') as f:
            f.write('theory HSB_B\n  imports HSB_A\nbegin\n\n'
                    'definition hsb_sum where "hsb_sum = hsb_val + 1"\n\n'
                    'lemma hsb_sum_is_43: "hsb_sum = 43"\n'
                    '  unfolding hsb_sum_def hsb_val_def by eval\n\n'
                    'end\n')

        # Step 3: check B — should see the NEW A (hsb_val=42),
        # not the heap version (hsb_val=1). The proof hsb_sum=43
        # should succeed.
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=f"Expected ok (hsb_sum=42+1=43), got: "
                             f"{resp['target']}")
        self.assertGreater(resp["target"]["steps_taken"], 0)

    def test_heap_target_must_see_stepped_dep_state(self):
        """B's segment init must use A's stepped REPL state, not heap.

        HSD_A and HSD_B are both heap-built. Workflow:
          1. Edit HSD_A: add a new theorem `new_a_thm` (heap doesn't
             know about it).
          2. Check HSD_A — A's REPL is now stepped through `new_a_thm`.
          3. Edit HSD_B: add `thm new_a_thm`.
          4. Check HSD_B — B should see the stepped A's `new_a_thm`.

        Expected: B passes (the new theorem is in A's REPL state).
        Suspected current behavior: B is classified HeapStale → built
        as SegmentInitPlan, which inits from the heap segment ignoring
        A's stepped REPL. `thm new_a_thm` then fails because the heap
        version of A doesn't have that theorem.
        """
        dep_dir = fixture_dir("heap_stepped_dep")
        a_path = os.path.join(dep_dir, "HSD_A.thy")
        b_path = os.path.join(dep_dir, "HSD_B.thy")

        # Step 1: add a new theorem to A
        with open(a_path, 'w') as f:
            f.write('theory HSD_A\n  imports Main\nbegin\n\n'
                    'definition hsd_val where "hsd_val = (1::nat)"\n\n'
                    'lemma new_a_thm: "hsd_val + 0 = hsd_val" by simp\n\n'
                    'end\n')

        # Step 2: check A — A now has a stepped REPL with new_a_thm
        resp = check(a_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertGreater(resp["target"]["steps_taken"], 0)

        # Step 3: add a reference to new_a_thm in B
        with open(b_path, 'w') as f:
            f.write('theory HSD_B\n  imports HSD_A\nbegin\n\n'
                    'definition hsd_use where "hsd_use = hsd_val + 1"\n\n'
                    'thm new_a_thm\n\n'
                    'end\n')

        # Step 4: check B — must see A's stepped state, not heap
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(
            resp["target"]["status"], "ok",
            msg=f"B must see A's stepped REPL state. Got: {resp['target']}")

    # --- Heap dep change second command (from TestSegmentDep2Change) ---

    def test_heap_dep_change_second_command(self):
        """Modify second command of SD2_A (heap dep), re-check SD2_B.

        SD2_A has two definitions: sd2_fixed (unchanged) and sd2_val
        (changed from 1 to 42). The first command matches the heap,
        so segment init starts from there and only steps the changed tail.
        """
        dep_dir = fixture_dir("segment_dep2")
        b_path = os.path.join(dep_dir, "SD2_B.thy")
        a_path = os.path.join(dep_dir, "SD2_A.thy")

        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 0)

        with open(a_path, 'w') as f:
            f.write('theory SD2_A\n  imports Main\nbegin\n\n'
                    'definition sd2_fixed where "sd2_fixed = (100::nat)"\n'
                    'definition sd2_val where "sd2_val = (42::nat)"\n\n'
                    'end\n')

        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        # SD2_A: first command matches, second differs → step 1 tail command
        sd2_a = find_dep(resp, "SD2_A")
        self.assertIsNotNone(sd2_a)
        self.assertEqual(sd2_a["steps_taken"], 1)
        # SD2_B: fully stepped (skip_segment_init since dep rebuilt)
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"Expected proof failure, got: {resp['target']}")
        self.assertEqual(resp["target"]["steps_taken"], 4)

    # --- Heap dep chain: C → B → A, change A halfway ---

    def test_heap_dep_chain_change_propagates(self):
        """Modify SDC_A halfway, re-check SDC_C: staleness propagates through B.

        SDC_C imports SDC_B imports SDC_A. All pre-built in heap.
        After changing SDC_A (sdc_y = 20 → 99), SDC_C's proof
        "sdc_sum = 30" should fail because sdc_sum = 10 + 99 = 109.
        """
        dep_dir = fixture_dir("segment_dep_chain")
        c_path = os.path.join(dep_dir, "SDC_C.thy")
        a_path = os.path.join(dep_dir, "SDC_A.thy")

        # First check: all in heap, 0 steps
        resp = check(c_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Change SDC_A: sdc_y = 20 → 99 (second command, first unchanged)
        with open(a_path, 'w') as f:
            f.write('theory SDC_A\n  imports Main\nbegin\n\n'
                    'definition sdc_x where "sdc_x = (10::nat)"\n'
                    'definition sdc_y where "sdc_y = (99::nat)"\n\n'
                    'end\n')

        # Re-check C: A is HeapStale, staleness propagates to B and C
        resp = check(c_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        # SDC_A: first command matches, second differs → step 1 tail command
        sdc_a = find_dep(resp, "SDC_A")
        self.assertIsNotNone(sdc_a)
        self.assertEqual(sdc_a["steps_taken"], 1)
        # SDC_C: fully stepped, proof fails (30 != 109)
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"Expected proof failure, got: {resp['target']}")

    def test_segment_qualified_command_unchanged(self):
        """Heap theory with qualified commands should recheck as unchanged.

        parse_spans splits 'qualified' and the command into separate spans,
        but the heap records them as one segment — causing a spurious diff.
        """
        sq_file = os.path.join(fixture_dir("segment_qualified"), "SQ_Test.thy")
        resp = check(sq_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Recheck: cached HeapVerifiedMarker path
        resp2 = check(sq_file, self.repl)
        self.assertEqual(resp2["status"], "ok", msg=resp2.get("error"))
        self.assertEqual(resp2["target"]["steps_taken"], 0)


    def test_empty_body_heap_theory_cached(self):
        """Wrapper theory (empty body) should get HeapVerifiedMarker after check."""
        all_thy = os.path.join(fixture_dir("heap_all_tests"), "All.thy")
        resp = check(all_thy, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        # Verify marker in symtab (no per-theory REPL created)
        from ic_check import read_all_markers
        markers = read_all_markers(self.repl)
        self.assertIn("AllHeapTests.All", markers)

    def test_heap_verified_marker_no_false_diamond(self):
        """HeapVerifiedMarker REPL should not trigger diamond conflicts.

        Seg_Large has a large body. After checking it, a HeapVerifiedMarker
        REPL exists. When checking HVM_Target, detect_diamond sees the marker
        REPL as a conflict, inflating reload_cost. The heuristic picks REPL
        instead of RELOAD, so HVM_B gets CheckPlan instead of LoadFilePlan.
        """
        # Step 1: check Seg_Large — creates HeapVerifiedMarker REPL
        seg_large = fixture_file("segment_session", "Seg_Large")
        resp = check(seg_large, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

        # Step 2: check HVM_Target — HVM_B should be loaded, not stepped
        hvm_target = fixture_file("segment_session", "HVM_Target")
        resp = check(hvm_target, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        hvm_b = find_dep(resp, "HVM_B")
        self.assertIsNotNone(hvm_b)
        self.assertEqual(hvm_b["resolution"], "from_heap")


    # --- Parallel execution tests ---

    def test_parallel_fan_out(self):
        """Parallel execution: 6 independent deps rebuilt concurrently.

        PF_Base → PF_Dep{1..6} → PF_Target, all pre-built in heap.
        After changing PF_Base (pf_base = 1 → 42), re-check PF_Target
        with pool_size=3. All 6 deps are at the same topo level and
        should execute concurrently. Each dep's proof fails because
        it checks a specific value derived from pf_base.
        """
        dep_dir = fixture_dir("parallel_fan_out")
        target_path = os.path.join(dep_dir, "PF_Target.thy")
        base_path = os.path.join(dep_dir, "PF_Base.thy")

        # First check: all in heap, 0 steps
        resp = check(target_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Change PF_Base: pf_base = 1 → 42
        with open(base_path, 'w') as f:
            f.write('theory PF_Base\n  imports Main\nbegin\n\n'
                    'definition pf_base where "pf_base = (42::nat)"\n\n'
                    'end\n')

        # Re-check with pool_size=3: 6 deps execute in parallel
        resp = check(target_path, self.repl, pool_size=3)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

        # PF_Base should be rebuilt (segment init, 1 step)
        pf_base = find_dep(resp, "PF_Base")
        self.assertIsNotNone(pf_base)
        self.assertEqual(pf_base["steps_taken"], 1)

        # All 6 deps should have errors (proofs fail with new base value)
        for i in range(1, 7):
            dep = find_dep(resp, f"PF_Dep{i}")
            self.assertIsNotNone(dep, msg=f"PF_Dep{i} not in response")
            self.assertEqual(dep["status"], "error",
                             msg=f"PF_Dep{i}: expected error, got {dep}")

        # Target should be stale (deps failed)
        self.assertEqual(resp["target"]["status"], "stale",
                         msg=f"Expected target stale, got: {resp['target']}")

        # Restore PF_Base with original value + extra definition.
        # All deps rebuild in parallel and pass this time.
        with open(base_path, 'w') as f:
            f.write('theory PF_Base\n  imports Main\nbegin\n\n'
                    'definition pf_base where "pf_base = (1::nat)"\n'
                    'definition pf_extra where "pf_extra = (99::nat)"\n\n'
                    'end\n')

        resp = check(target_path, self.repl, pool_size=3)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

        # All 6 deps should succeed (proofs still hold, pf_base unchanged)
        for i in range(1, 7):
            dep = find_dep(resp, f"PF_Dep{i}")
            self.assertIsNotNone(dep, msg=f"PF_Dep{i} not in response")
            self.assertEqual(dep["status"], "ok",
                             msg=f"PF_Dep{i}: expected ok, got {dep}")
            self.assertGreater(dep["steps_taken"], 0,
                               msg=f"PF_Dep{i}: expected reprocessing")

        # Target should succeed
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=f"Expected target ok, got: {resp['target']}")
        self.assertGreater(resp["target"]["steps_taken"], 0)


    def test_stale_heap_target_after_dep_recheck(self):
        """Heap target must be re-checked when a dep has been rebuilt via REPL.

        SHT_Dep and SHT_Target are both in the heap. After modifying
        SHT_Dep (sht_val = 1 → 42), check SHT_Dep directly — this
        creates a REPL with the new content. Then check SHT_Target:
        it should detect that its dep has a stepped REPL (content
        differs from heap) and re-check, causing the proof to fail.

        This reproduces the bug where TargetUnchangedPlan is assigned
        because ReplClean deps are not considered "rebuilding" —
        even though the target's heap version was built against the
        old dep content.
        """
        dep_dir = fixture_dir("stale_heap_target")
        dep_path = os.path.join(dep_dir, "SHT_Dep.thy")
        target_path = os.path.join(dep_dir, "SHT_Target.thy")

        # Step 1: both in heap, target unchanged
        resp = check(target_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Step 2: modify dep (sht_val = 1 → 42)
        with open(dep_path, 'w') as f:
            f.write('theory SHT_Dep\n  imports Main\nbegin\n\n'
                    'definition sht_val where "sht_val = (42::nat)"\n\n'
                    'end\n')

        # Step 3: check dep directly — creates REPL with new content
        resp = check(dep_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertGreater(resp["target"]["steps_taken"], 0)

        # Step 4: check target — should detect stale dep and re-check.
        # sht_sum = sht_val + 1 = 43, but proof says sht_sum = 2 → error
        resp = check(target_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertNotEqual(resp["target"]["status"], "ok",
                            msg="Target should not be ok — dep was rebuilt "
                                "with different content")


    def test_segment_double_edit(self):
        """Second edit of a SegmentInit REPL should do incremental on the tail.

        SDE_File has 5 definitions (a-e) in the heap. Edit sde_c (middle)
        → check → SegmentInit steps tail (sde_c, sde_d, sde_e = 3 cmds).
        Edit sde_e (end of tail) → check → should incremental-diff the
        tail and re-step only 1 command (sde_e), not misalign against
        the full body.
        """
        sde_path = os.path.join(fixture_dir("segment_double_edit"),
                                "SDE_File.thy")

        # Step 1: edit sde_c (3rd definition) → check
        with open(sde_path) as f:
            original = f.read()
        edit1 = original.replace(
            'definition sde_c where "sde_c = (3::nat)"',
            'definition sde_c where "sde_c = (33::nat)"')
        with open(sde_path, 'w') as f:
            f.write(edit1)

        resp = check(sde_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        # SegmentInit: first 2 commands match heap, tail = sde_c + sde_d + sde_e = 3
        self.assertEqual(resp["target"]["steps_taken"], 3)

        # Step 2: edit sde_e (last definition, in the tail) → check again
        edit2 = edit1.replace(
            'definition sde_e where "sde_e = (5::nat)"',
            'definition sde_e where "sde_e = (55::nat)"')
        with open(sde_path, 'w') as f:
            f.write(edit2)

        resp = check(sde_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        # Incremental on tail: sde_c and sde_d unchanged, only sde_e re-stepped
        self.assertEqual(resp["target"]["steps_taken"], 1,
                         msg="Should re-step only the changed tail command")


    def test_incremental_marker_update(self):
        """Marker must be updated after incremental rebuild.

        Without marker update, the dep's stale marker causes it to be
        classified as ReplChanged on subsequent rechecks, propagating
        unnecessary staleness to downstream deps.

        IM_Dep (5 defs) → IM_Target (uses im_a + im_e), both in heap.
        1. Check target → all in heap, 0 steps
        2. Edit dep (middle), check dep directly → SegmentInit
        3. Check target → dep has REPL, target rebuilt
        4. Edit dep again (tail), check target → dep incremental, target rebuilt
        5. Check target (no changes) → should be 0 steps
           Without fix: dep's stale marker → ReplChanged → rebuilding →
           target gets HeapStaleDep → full rebuild with steps_taken > 0
        """
        dep_dir = fixture_dir("incremental_marker")
        dep_path = os.path.join(dep_dir, "IM_Dep.thy")
        target_path = os.path.join(dep_dir, "IM_Target.thy")

        # Step 1: all in heap
        resp = check(target_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # Step 2: edit dep middle (im_c = 3 → 33), check dep directly
        with open(dep_path) as f:
            original = f.read()
        edit1 = original.replace(
            'definition im_c where "im_c = (3::nat)"',
            'definition im_c where "im_c = (33::nat)"')
        with open(dep_path, 'w') as f:
            f.write(edit1)
        resp = check(dep_path, self.repl)
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))

        # Step 3: check target → dep rebuilt, target rebuilt
        resp = check(target_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertGreater(resp["target"]["steps_taken"], 0)

        # Step 4: edit dep tail (im_e = 5 → 55), check target
        edit2 = edit1.replace(
            'definition im_e where "im_e = (5::nat)"',
            'definition im_e where "im_e = (55::nat)"')
        with open(dep_path, 'w') as f:
            f.write(edit2)
        resp = check(target_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        # Target's proof: im_sum = im_a + im_e = 1 + 55 = 56 ≠ 6 → error
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"Expected error, got: {resp['target']}")

        # Step 5: check target again (no changes) → should be 0 steps
        resp = check(target_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        dep = find_dep(resp, "IM_Dep")
        self.assertIsNotNone(dep)
        # Key assertion: dep should NOT cause unnecessary target rebuild
        self.assertEqual(resp["target"]["steps_taken"], 1,
                         msg="Target should recover cached error (1 step), "
                             "not full rebuild")


    def test_ml_counter_dep_chain(self):
        """ML counter makes dep fail first, succeed second; chain propagates.

        A → B → C, and D imports both A and C (diamond). All in heap.
        Modify A: insert ML_val counter (fails first invocation) and
        change mlc_a value. Check D twice:
        1. A fails (counter 0→1), B/C/D stale
        2. A recovers (counter 1→2), B/C rebuild with new value, D
           fails because mlc_a changed (42+44≠4)
        """
        dep_dir = fixture_dir("ml_counter")
        a_path = os.path.join(dep_dir, "MLC_A.thy")
        d_path = os.path.join(dep_dir, "MLC_D.thy")

        # Modify A: insert ML_val counter + change mlc_a to 42
        with open(a_path, 'w') as f:
            f.write(
                'theory MLC_A\n'
                '  imports Main\n'
                'begin\n\n'
                'ML \\<open>val mlc_counter = Unsynchronized.ref 0\\<close>\n\n'
                'ML_val \\<open>\n'
                '  mlc_counter := !mlc_counter + 1;\n'
                '  if !mlc_counter < 2 then '
                'error "ic_test: first invocation fails" else ()\n'
                '\\<close>\n\n'
                'definition mlc_a where "mlc_a = (42::nat)"\n\n'
                'end\n')

        # First check: A fails, B/C/D stale
        resp = check(d_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        dep_a = find_dep(resp, "MLC_A")
        self.assertIsNotNone(dep_a)
        self.assertEqual(dep_a["status"], "error")
        self.assertIn("ic_test: first invocation fails", dep_a["error"])
        self.assertEqual(resp["target"]["status"], "stale",
                         msg=f"D should be stale: {resp['target']}")

        # Second check: A recovers, chain rebuilds, D fails (42+44≠4)
        resp = check(d_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        dep_a = find_dep(resp, "MLC_A")
        self.assertIsNotNone(dep_a)
        self.assertEqual(dep_a["status"], "ok",
                         msg=f"A should recover: {dep_a}")
        dep_b = find_dep(resp, "MLC_B")
        self.assertIsNotNone(dep_b)
        self.assertEqual(dep_b["status"], "ok",
                         msg=f"B should rebuild: {dep_b}")
        dep_c = find_dep(resp, "MLC_C")
        self.assertIsNotNone(dep_c)
        self.assertEqual(dep_c["status"], "ok",
                         msg=f"C should rebuild: {dep_c}")
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"D should fail (value changed): {resp['target']}")

    def test_diamond_recheck_after_dep_change_repl(self):
        """Diamond via REPL (heap): D→B→A, D→C→E→A.

        All five theories are in the heap (dr_a=1, dr_d=112).
        1. Change A (dr_a = 1 → 5), check D — all deps rebuilt,
           D's proof expects 112, so it fails.
        2. Change A again (dr_a = 5 → 9), check D with updated proof.
           All deps must see dr_a=9: dr_d = (9+10) + (9+100) = 128.
        """
        dep_dir = fixture_dir("diamond_recheck_repl")
        a_path = os.path.join(dep_dir, "DR_A.thy")
        d_path = os.path.join(dep_dir, "DR_D.thy")

        # Step 1: change A (1 → 5), check D — proof fails (expects 112)
        with open(a_path, 'w') as f:
            f.write('theory DR_A\n  imports Main\nbegin\n\n'
                    'definition dr_a where "dr_a = (5::nat)"\n\n'
                    'end\n')
        resp = check(d_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "error",
                         msg=f"Expected failure (proof says 112): "
                             f"{resp['target']}")

        # Step 2: change A again (5 → 9), add proof to B, check B.
        with open(a_path, 'w') as f:
            f.write('theory DR_A\n  imports Main\nbegin\n\n'
                    'definition dr_a where "dr_a = (9::nat)"\n\n'
                    'end\n')
        b_path = os.path.join(dep_dir, "DR_B.thy")
        with open(b_path, 'w') as f:
            f.write('theory DR_B\n  imports DR_A\nbegin\n\n'
                    'definition dr_b where "dr_b = dr_a + 10"\n\n'
                    'lemma "dr_b = 19"\n'
                    '  unfolding dr_b_def dr_a_def by eval\n\n'
                    'end\n')
        resp = check(b_path, self.repl)
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=f"B should see dr_a=9: {resp['target']}")

        # Step 3: check D with updated proof — all deps must see dr_a=9.
        with open(d_path, 'w') as f:
            f.write('theory DR_D\n  imports DR_B DR_C\nbegin\n\n'
                    'definition dr_d where "dr_d = dr_b + dr_c"\n\n'
                    'lemma "dr_d = 128"\n'
                    '  unfolding dr_d_def dr_b_def dr_c_def dr_e_def '
                    'dr_a_def by eval\n\n'
                    'end\n')
        resp = check(d_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=f"Expected ok (dr_d=19+109=128), got: "
                             f"{resp['target']}")


    def test_diamond_identity_stale_via_transitive_dep(self):
        """Duplicate theory error when B's REPL has stale theory identity.

        All five theories (X, A, B, C, D) are in the heap.
        X is the root, A imports X, B and C import A, D imports B and C.

        Heap values: dis_x=1, dis_a=11, dis_b=12, dis_c=111, dis_d=123.

        The bug requires both B and C to reference the same REPL name
        for A, but different generations of its theory identity:

        1. Edit X (append comment), check(B) — X gets HeapStale → REPL.
           A gets HeapStaleDep → CheckPlan → REPL (gen 1).
           B gets REPL built on gen-1 A.
        2. Edit X again (append more), check(C) — X gets ReplChanged →
           IncrementalPlan. A's dep_hash for X mismatches → NoRepl →
           HeapStaleDep → CheckPlan(REBASE): A's REPL is kept alive
           but its base is re-resolved and steps re-run, producing
           gen-2 theory identity. C gets REPL built on gen-2 A.
        3. check(D) — B's dep_hash for A matches (A's file never changed),
           so B is classified ReplClean. But B's REPL has gen-1 A in its
           ancestry, C's REPL has gen-2 A. Same REPL name, different
           theory identity objects → Ir.init fails with Duplicate theory.

        This tests that dep_hashes (which only track file content hashes)
        correctly detect staleness caused by transitive dep rebuilds that
        don't change the direct dep's file.
        """
        dep_dir = fixture_dir("diamond_identity_stale")
        x_path = os.path.join(dep_dir, "DIS_X.thy")
        b_path = os.path.join(dep_dir, "DIS_B.thy")
        c_path = os.path.join(dep_dir, "DIS_C.thy")
        d_path = os.path.join(dep_dir, "DIS_D.thy")

        # Step 1: Change X's definition (dis_x = 1 → 2), check B.
        # X: HeapStale → SegmentInitPlan → REPL (new content)
        # A: HeapStaleDep → CheckPlan → REPL (gen 1, built on REPL-X)
        # B: HeapStaleDep → CheckPlan → REPL (built on gen-1 A)
        with open(x_path, 'w') as f:
            f.write('theory DIS_X\n  imports Main\nbegin\n\n'
                    'definition dis_x where "dis_x = (2::nat)"\n\n'
                    'end\n')
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=f"B check failed: {resp['target']}")

        # Step 2: Change X again (dis_x = 2 → 3), check C.
        # X: ReplChanged → IncrementalPlan (marker hash mismatch)
        # A: dep_hash for X mismatches → NoRepl → HeapStaleDep →
        #    CheckPlan → old REPL removed, new REPL created (gen 2)
        # C: HeapStaleDep → CheckPlan → REPL (built on gen-2 A)
        #
        # B is NOT in C's dep tree so it is not touched.
        with open(x_path, 'w') as f:
            f.write('theory DIS_X\n  imports Main\nbegin\n\n'
                    'definition dis_x where "dis_x = (3::nat)"\n\n'
                    'end\n')
        resp = check(c_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=f"C check failed: {resp['target']}")

        # Step 3: check D.
        # B's SteppedMarker dep_hash for A matches (A's file unchanged).
        # B classified ReplClean — but B's REPL has gen-1 A in ancestry.
        # C's REPL has gen-2 A in ancestry.
        # Same REPL name (ic...DIS_A), different theory identity objects.
        # D's Ir.init sees both → "Duplicate theory name".
        #
        # Expected: D should check successfully (B's REPL detected as
        # stale and rebuilt), NOT crash with Ir.init failure.
        resp = check(d_path, self.repl)
        self.assertNotIn("Duplicate theory", resp.get("error", ""),
                         msg="Ir.init failed with duplicate theory — "
                             "B's stale REPL identity was not detected")
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

    # --- Status command tests ---

    def capture_status(self, verbose=0):
        """Capture stdout from status()."""
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            status(self.repl, verbose=verbose)
        return out.getvalue()

    def test_status_empty(self):
        """Status after clean: no REPLs, no markers."""
        out = self.capture_status()
        self.assertIn("0 REPLs", out)
        self.assertIn("0 markers", out)
        self.assertIn("no I/C state", out)

    def test_status_shows_done_repls(self):
        """Status shows done REPLs after checking a heap file."""
        dep_dir = fixture_dir("status_done")
        a_path = os.path.join(dep_dir, "STD_A.thy")
        b_path = os.path.join(dep_dir, "STD_B.thy")

        # Change A to force stepping
        with open(a_path, 'w') as f:
            f.write('theory STD_A\n  imports Main\nbegin\n\n'
                    'definition std_a where "std_a = (42::nat)"\n\n'
                    'end\n')
        resp = check(b_path, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

        # verbose=0: done REPLs are just a count
        out = self.capture_status(verbose=0)
        self.assertIn("REPLs done", out)
        self.assertNotIn("StatusDone.STD_A", out)

        # verbose=1: done REPLs are listed with progress bars
        out = self.capture_status(verbose=1)
        self.assertIn("Done", out)
        self.assertIn("StatusDone.STD_A", out)
        self.assertIn("StatusDone.STD_B", out)
        # Progress bars show full
        self.assertRegex(out, r"\[=+\]")

    def test_status_shows_stale(self):
        """Status detects stale dep hashes after a dep is rebuilt."""
        dep_dir = fixture_dir("status_stale")
        x_path = os.path.join(dep_dir, "STS_X.thy")
        b_path = os.path.join(dep_dir, "STS_B.thy")
        c_path = os.path.join(dep_dir, "STS_C.thy")

        # Step 1: check B (creates REPLs for X, A, B)
        with open(x_path, 'w') as f:
            f.write('theory STS_X\n  imports Main\nbegin\n\n'
                    'definition sts_x where "sts_x = (2::nat)"\n\n'
                    'end\n')
        check(b_path, self.repl)

        # Step 2: change X, check C (rebuilds X and A, but B is untouched)
        with open(x_path, 'w') as f:
            f.write('theory STS_X\n  imports Main\nbegin\n\n'
                    'definition sts_x where "sts_x = (3::nat)"\n\n'
                    'end\n')
        check(c_path, self.repl)

        # Status should show B as stale (dep A's marker changed)
        out = self.capture_status()
        self.assertIn("Stale", out)
        self.assertIn("StatusStale.STS_B", out)
        self.assertIn("marker changed", out)
        # A is rebased instead of re-init'd, so A's REPL persists and
        # B's pin@ic.A reference stays valid — no orphan expected.
        self.assertNotIn("Orphan markers", out,
                         msg="A's REPL should be rebased, keeping "
                             f"B's pin@A alive:\n{out}")

    def test_status_shows_heap_verified(self):
        """Status shows heap verified markers at verbose>=1."""
        # Check an unchanged heap file — creates HeapVerifiedMarker
        sth_file = fixture_file("status_heap", "STH_File")
        resp = check(sth_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["steps_taken"], 0)

        # verbose=0: heap verified as count
        out = self.capture_status(verbose=0)
        self.assertIn("heap verified", out)

        # verbose=1: listed individually
        out = self.capture_status(verbose=1)
        self.assertIn("Heap verified", out)
        self.assertIn("StatusHeap.STH_File", out)

    def test_status_sorted_alphabetically(self):
        """Status entries are sorted alphabetically by qualified name."""
        dep_dir = fixture_dir("status_sorted")
        x_path = os.path.join(dep_dir, "SSO_X.thy")
        b_path = os.path.join(dep_dir, "SSO_B.thy")

        with open(x_path, 'w') as f:
            f.write('theory SSO_X\n  imports Main\nbegin\n\n'
                    'definition sso_x where "sso_x = (2::nat)"\n\n'
                    'end\n')
        check(b_path, self.repl)

        out = self.capture_status(verbose=1)
        # Find positions of qualified names in Done section
        pos_a = out.find("StatusSorted.SSO_A")
        pos_b = out.find("StatusSorted.SSO_B")
        pos_x = out.find("StatusSorted.SSO_X")
        self.assertGreater(pos_a, 0)
        self.assertGreater(pos_b, 0)
        self.assertGreater(pos_x, 0)
        # A < B < X alphabetically
        self.assertLess(pos_a, pos_b)
        self.assertLess(pos_b, pos_x)

    def test_status_progress_bars_aligned(self):
        """Progress bars within a section start at the same column.

        STA_X → STA_Mid → STA_LongName, all in heap. Change STA_X
        to force all three to get REPLs. The qualified names
        StatusAligned.STA_X, StatusAligned.STA_Mid, and
        StatusAligned.STA_LongName have different lengths, so the
        progress bars must be padded to align.
        """
        dep_dir = fixture_dir("status_aligned")
        with open(os.path.join(dep_dir, "STA_X.thy"), 'w') as f:
            f.write('theory STA_X\n  imports Main\nbegin\n\n'
                    'definition sta_x where "sta_x = (42::nat)"\n\n'
                    'end\n')
        check(os.path.join(dep_dir, "STA_LongName.thy"), self.repl)

        out = self.capture_status(verbose=1)
        # Find "Done" section lines with progress bars
        in_done = False
        bar_columns = []
        for line in out.splitlines():
            if "Done" in line and "(" in line:
                in_done = True
                continue
            if in_done and line.strip() and not line.startswith("    "):
                break  # next section
            if in_done and "[" in line:
                bar_columns.append(line.index("["))
        self.assertGreater(len(bar_columns), 1,
                           msg=f"Expected multiple bars, got: {bar_columns}")
        self.assertEqual(len(set(bar_columns)), 1,
                         msg=f"Progress bars not aligned: columns {bar_columns}")

    def test_status_shows_stepping_for_partial_repl(self):
        """Status shows partially-stepped REPLs under 'Stepping'.

        STP_File has 5 definitions (a-e) in the heap. Change stp_b to
        a different valid value AND break stp_d. Segment init finds the
        first diff at stp_b, so the tail is [stp_b', stp_c, stp_d_broken,
        stp_e] = 4 commands. stp_b' and stp_c succeed (2 steps), then
        stp_d errors. The REPL ends up with step_count=2, cmd_count=4.
        Status should show this under 'Stepping' with a partially-filled
        progress bar, and NOT under 'Done'.
        """
        stp_file = fixture_file("status_partial", "STP_File")
        with open(stp_file) as f:
            original = f.read()
        modified = original.replace(
            'definition stp_b where "stp_b = (2::nat)"',
            'definition stp_b where "stp_b = (22::nat)"')
        modified = modified.replace(
            'definition stp_d where "stp_d = (4::nat)"',
            'definition stp_d where "stp_d = (x::nat)"')
        with open(stp_file, 'w') as f:
            f.write(modified)

        resp = check(stp_file, self.repl)
        self.assertEqual(resp["target"]["status"], "error")
        # 2 successful steps (stp_b', stp_c), then stp_d errors
        self.assertEqual(resp["target"]["steps_taken"], 3)

        # verbose=0: partial REPL shown under Stepping
        out = self.capture_status(verbose=0)
        self.assertIn("Stepping", out)
        self.assertIn("StatusPartial.STP_File", out)
        # Progress bar must be partially filled: some = followed by spaces
        self.assertRegex(out, r"\[=+ +\] \d+/\d+")
        # Should NOT appear in done count
        self.assertNotIn("REPLs done", out.split("Stepping")[0])

        # verbose=1: still under Stepping, not under Done
        out = self.capture_status(verbose=1)
        stepping_idx = out.find("Stepping")
        done_idx = out.find("Done")
        stp_idx = out.find("StatusPartial.STP_File")
        self.assertGreater(stepping_idx, -1,
                           msg="Stepping section should exist")
        self.assertGreater(stp_idx, stepping_idx,
                           msg="STP_File should appear after Stepping header")
        if done_idx > -1:
            self.assertLess(stp_idx, done_idx,
                            msg="STP_File should appear before Done section")


    def test_pin_dep_transitive_heap_removal(self):
        """expand_with_pin_dependents misses transitive pin deps.

        A→Z→C heap chain. check(C) creates pinned REPLs: A(segment),
        Z(pin@A), C(pin@Z). Edit A at tail, then edit A at head and
        check D(imports A). A needs SegmentInitPlan (removal). Z is
        external with pin@A (found). C is external with pin@Z (missed
        because C sorts before Z alphabetically → single-pass expansion
        visits C before Z is added). Z's removal fails.
        """
        dep_dir = fixture_dir("pin_transitive_heap")
        a_path = os.path.join(dep_dir, "PTH_A.thy")

        # Step 1: edit A's last command → segment init steps the tail
        with open(a_path, 'w') as f:
            f.write('theory PTH_A\n  imports Main\nbegin\n\n'
                    'definition pth_a :: nat where "pth_a = 1"\n'
                    'definition pth_a2 :: nat where "pth_a2 = pth_a + 1"\n'
                    'definition pth_a3 :: nat where "pth_a3 = pth_a2 + 1"\n'
                    'definition pth_a4 :: nat where "pth_a4 = pth_a3 + 1"\n\n'
                    'lemma "pth_a4 = 4" unfolding pth_a4_def '
                    'pth_a3_def pth_a2_def pth_a_def by eval\n\n'
                    'end\n')
        resp = check(os.path.join(dep_dir, "PTH_C.thy"), self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

        # Step 2: edit A's first command → segment point shifts →
        # fresh SegmentInitPlan (removes_repl=True)
        with open(a_path, 'w') as f:
            f.write('theory PTH_A\n  imports Main\nbegin\n\n'
                    'definition pth_a :: nat where "pth_a = 5"\n'
                    'definition pth_a2 :: nat where "pth_a2 = pth_a + 1"\n'
                    'definition pth_a3 :: nat where "pth_a3 = pth_a2 + 1"\n'
                    'definition pth_a4 :: nat where "pth_a4 = pth_a3 + 1"\n\n'
                    'lemma "pth_a4 = 8" unfolding pth_a4_def '
                    'pth_a3_def pth_a2_def pth_a_def by simp\n\n'
                    'end\n')
        resp = check(os.path.join(dep_dir, "PTH_D.thy"), self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))

    def test_heapdiff_reports_match_and_diff(self):
        """heapdiff reports match on unchanged file, diff after modification."""
        hd_file = fixture_file("heapdiff_test", "HD_File")

        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            print_heapdiff(self.repl, hd_file)
        out = buf.getvalue()
        self.assertIn("HD_File", out)
        self.assertIn("heap matches file", out)
        self.assertNotIn("DIFF", out)

        with open(hd_file) as f:
            original = f.read()
        modified = original.replace(
            'definition hd_b where "hd_b = (2::nat)"',
            'definition hd_b where "hd_b = (22::nat)"')
        with open(hd_file, 'w') as f:
            f.write(modified)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            print_heapdiff(self.repl, hd_file)
        out = buf.getvalue()
        self.assertIn("DIFF", out)
        self.assertIn("(2::nat)", out)
        self.assertIn("(22::nat)", out)
        self.assertIn("2 commands would be re-stepped", out)


    def test_segment_shrink_below_heap_size(self):
        """Shrinking a segment-init REPL's file below heap command count.

        SS_File has 5 definitions in the heap. After a segment-init
        edit (changing ss_c), the REPL has segment_spec pointing at
        the heap. Then shrinking the file to 3 definitions (fewer than
        the heap's 5) should not crash.
        """
        seg_file = fixture_file("segment_shrink", "SS_File")
        with open(seg_file) as f:
            original = f.read()

        # Step 1: edit ss_c → segment init
        modified = original.replace(
            'definition ss_c where "ss_c = (3::nat)"',
            'definition ss_c where "ss_c = (33::nat)"')
        with open(seg_file, 'w') as f:
            f.write(modified)

        resp = check(seg_file, self.repl)
        self.assertEqual(resp["status"], "ok", msg=resp.get("error"))
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))
        self.assertGreater(resp["target"]["steps_taken"], 0)

        # Step 2: shrink file (remove ss_d and ss_e)
        with open(seg_file, 'w') as f:
            f.write('(*<*)\ntheory SS_File\n  imports Main\nbegin\n(*>*)\n\n'
                    'definition ss_a where "ss_a = (1::nat)"\n'
                    'definition ss_b where "ss_b = (2::nat)"\n'
                    'definition ss_c where "ss_c = (33::nat)"\n\n'
                    'end\n')

        resp = check(seg_file, self.repl)
        self.assertEqual(resp["status"], "ok",
                         msg=f"Shrink below heap size crashed: "
                             f"{resp.get('error')}")
        self.assertEqual(resp["target"]["status"], "ok",
                         msg=resp["target"].get("error"))


class TestHeapNoRecord(unittest.TestCase):
    """Target lives in a heap built without record_theories=true.

    Without recorded segments, I/C cannot diff the heap copy against
    the source on disk, so it must surface an actionable error
    instead of silently reporting OK and ignoring edits.
    """

    repl = None
    repl_proc = None
    isabelle_path = None  # set by main() from --isabelle / $ISABELLE

    @classmethod
    def setUpClass(cls):
        install_templates()
        isabelle = find_isabelle(cls.isabelle_path)
        d = fixture_dir("heap_no_record")
        # HeapNoRecord must be built (heap-only target). HeapNoRecordClient
        # stays unbuilt so its theories are checked from source.
        build_session(isabelle, d, "HeapNoRecord")

        cls.repl_proc = ReplProcess(
            session="HeapNoRecord", dirs=[d], no_bash_server=True,
            isabelle=cls.isabelle_path)
        cls.repl = cls.repl_proc.start()
        clean(cls.repl)

    @classmethod
    def tearDownClass(cls):
        if cls.repl:
            try:
                clean(cls.repl)
            except Exception:
                pass
        if cls.repl_proc:
            cls.repl_proc.stop()
        remove_templates()

    def setUp(self):
        install_templates()
        clean(self.repl)

    def test_target_in_heap_without_segments_errors(self):
        """check() on a target in a no-record_theories heap must error
        with an actionable message instead of silently reporting OK.

        Also: editing the source must keep producing the same error,
        not a stale OK from cached state.
        """
        path = os.path.join(fixture_dir("heap_no_record"), "heap", "HNR_A.thy")

        def assert_freshness_error(resp):
            self.assertEqual(resp["status"], "error",
                             msg=f"Expected error, got: {resp}")
            err = resp.get("error", "")
            self.assertIn("Cannot determine freshness", err)
            self.assertIn("HeapNoRecord.HNR_A", err)
            self.assertIn("record_theories=true", err)

        assert_freshness_error(check(path, self.repl))

        # Edit the file: the same error must fire again — no cached OK,
        # no silent acceptance of the edited body.
        with open(path, 'w') as f:
            f.write('theory HNR_A\n  imports Main\nbegin\n\n'
                    'definition hnr_a where "hnr_a = (42::nat)"\n\n'
                    'end\n')
        assert_freshness_error(check(path, self.repl))

    def test_dep_in_heap_without_segments_does_not_error(self):
        """Only the target gates on NO_SEGMENTS. A non-heap target
        whose *dep* lives in a no-record_theories heap must succeed,
        with the dep reported as resolution=from_heap. A single
        per-check warning must fire on stderr, naming the session
        only (not the qualified theory name).
        """
        use_path = os.path.join(fixture_dir("heap_no_record"),
                                "client", "HNR_Use.thy")
        err_buf = io.StringIO()
        with contextlib.redirect_stderr(err_buf):
            resp = check(use_path, self.repl)
        self.assertEqual(resp["status"], "ok",
                         msg=f"Expected ok, got: {resp}")
        self.assertEqual(resp["target"]["status"], "ok")
        self.assertEqual(resp["target"]["name"], "HNR_Use")
        a_dep = next((d for d in resp.get("dependencies", [])
                      if d["name"] == "HNR_A"), None)
        self.assertIsNotNone(a_dep, msg=f"HNR_A dep missing from {resp}")
        self.assertEqual(a_dep["resolution"], "from_heap",
                         msg=f"Expected HNR_A from_heap, got {a_dep}")
        err = err_buf.getvalue()
        self.assertIn("record_theories=true", err)
        self.assertIn("HeapNoRecord", err)
        # Theory name must NOT appear — only the session name.
        # (Covers qualified form too: "HeapNoRecord.HNR_A" contains "HNR_A".)
        self.assertNotIn("HNR_A", err)


def main():
    p = argparse.ArgumentParser(
        description="I/C Tests",
        usage="%(prog)s [options] [unittest args]")
    p.add_argument("--unit-only", action="store_true",
                   help="Run unit tests only (no Isabelle needed)")
    p.add_argument("--integration-only", action="store_true",
                   help="Run integration tests only")
    p.add_argument("-k", dest="pattern", default=None,
                   help="Run only tests matching PATTERN")
    p.add_argument("--isabelle", default=os.environ.get("ISABELLE"),
                   help="Path to isabelle binary or Isabelle home directory "
                        "(default: $ISABELLE, else auto-detect)")
    args, remaining = p.parse_known_args()

    TestICSIntegration.isabelle_path = args.isabelle
    TestHeapTheories.isabelle_path = args.isabelle
    TestHeapNoRecord.isabelle_path = args.isabelle

    if args.unit_only:
        # Run unit tests from test_ic_core.py
        sys.argv[1:] = remaining
        import test_ic_core
        unittest.main(module=test_ic_core)
        return

    # Build argv for unittest
    argv = [sys.argv[0]]
    if args.pattern:
        argv += ["-k", args.pattern]
    argv += remaining

    if not args.integration_only:
        # Run unit tests first
        print("\033[1mRunning unit tests\033[0m", file=sys.stderr, flush=True)
        unit_result = subprocess.run(
            [sys.executable, "test_ic_core.py", "-v"] + remaining)
        if unit_result.returncode != 0:
            print("\033[31mUnit tests failed\033[0m",
                  file=sys.stderr, flush=True)
            sys.exit(1)
        print("\033[32mUnit tests passed\033[0m\n",
              file=sys.stderr, flush=True)

    print("\033[1mRunning integration tests\033[0m",
          file=sys.stderr, flush=True)
    sys.argv = argv
    unittest.main(module=__name__, verbosity=2)


if __name__ == "__main__":
    main()
