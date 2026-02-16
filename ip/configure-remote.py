#!/usr/bin/env python3
"""Configure Isabelle remote ML prover.

Subcommands:

  setup HOST   Install Isabelle on remote and mirror poly binary and heaps
               with local copies stored under a configurable ML platform name
               specified with --ml-platform.

               By default, expects target ML platform to be unused.
               - Use --copy-from-local when you want to setup a
                 new remote from an existing ML platform.
                 This is useful to 'fork' new remote instances from ML platforms
                 and heaps that have built previously.
               - Use --force-write-local to overwrite the local ML platform
                 with a fresh rebuild installation and build of poly and the
                 Pure + HOL heap.

  run HOST     Print jEdit flags to use for enabling ML proxy.

               Verifies local poly/heaps match the remote before emitting flags.

  list         List all local ML platforms with poly hashes and available heaps.

  remove PLAT  Remove a local ML platform and its associated heaps.

Common options (setup, run):

  HOST                     SSH host in user@host format (positional, required).
  --isabelle-home PATH     ISABELLE_HOME on the remote machine.
                           Default: /home/<user>/{ISABELLE_VERSION} (user from HOST).
  --local-isabelle-home P  Local Isabelle installation root. Default: if
                           ISABELLE_HOME is set and points to the binary
                           directory of an existing Isabelle installation,
                           uses ISABELLE_HOME/../ as the root.
                           Otherwise, this option is required.
  --ml-platform NAME       Force the local ML platform directory name
                           (e.g. arm64-ubuntu). If omitted, a name is
                           derived from the remote base platform and poly hash.
  --64 / --32              Use 64-bit (default) or 32-in-64-bit ML platform.

Setup-only options:

  --force-write-local      Overwrite an existing local ML platform with the
                           remote poly binary and heaps. Mutually exclusive
                           with --copy-from-local.
  --copy-from-local        Push the local poly binary and heaps to the remote
                           instead of pulling from it. Mutually exclusive with
                           --force-write-local.
  --sync-all-heaps         With --copy-from-local: sync the entire local heaps
                           directory, not just Pure and HOL.

Run-only options:

  --sync-all-heaps         Sync all local heaps to the remote before printing
                           jEdit flags.
  --minheap MB             Override Poly/ML --minheap (minimum heap size).
  --maxheap MB             Override Poly/ML --maxheap (maximum heap size).
  --gcthreads N            Override Poly/ML --gcthreads (GC thread count).
  -H MB                    Override Poly/ML -H (initial heap size).
  --gcpercent N            Override Poly/ML --gcpercent (target GC time, 1-99).

List options:

  --local-isabelle-home P  As above.

Remove options:

  PLAT                     ML platform name to remove (positional, required).
  --local-isabelle-home P  As above.
  -y, --yes                Skip the confirmation prompt.

Examples:

  # First-time setup (install Isabelle on remote, sync to local):
  configure-remote.py setup ubuntu@host --ml-platform aarch64-ubuntu

  # Spawn a new remote with an existing ML platform + all heaps:
  configure-remote.py setup ubuntu@host --ml-platform aarch64-ubuntu \
     --copy-from-local --sync-all-heaps

  # Print jEdit flags
  configure-remote.py run ubuntu@host --ml-platform aarch64-ubuntu

  # List local platforms:
  configure-remote.py list

  # Remove a platform:
  configure-remote.py remove aarch64-ubuntu

Shell alias:

  The following alias makes ./configure-remote.py more convenient to use.
  Put it in your .zshrc or equivalent and then invoke pass $ISABELLE_REMOTE
  to invocations of `isabelle jedit`.

``
  # Isabelle remote ML prover
  isabelle-remote() {
    local flags
    flags=$(~/remote_isabelle/configure-remote.py run "$@") || return 1
    ISABELLE_REMOTE="$flags"
    echo "ISABELLE_REMOTE set ✓" >&2
  }
```
"""

import argparse
import hashlib
import os
import shutil
import subprocess
import sys


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
ISABELLE_VERSION = "Isabelle2025-2"
POLYML_CONTRIB = "contrib/polyml-5.9.2-2"
HEAP_PREFIX = "polyml-5.9.2"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def die(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)


def info(msg):
    print(msg, file=sys.stderr)


import time as _time

# ANSI colors and symbols
_RED = "\033[31m"
_GREEN = "\033[32m"
_YELLOW = "\033[33m"
_BOLD = "\033[1m"
_DIM = "\033[2m"
_RESET = "\033[0m"
_CLEAR_LINE = "\r\033[2K"
_SYM_OK = f"{_GREEN}✓{_RESET}"
_SYM_BUSY = f"{_YELLOW}↻{_RESET}"
_SYM_FAIL = f"{_RED}✗{_RESET}"

_step_t0 = None
_step_msg = ""
_step_indent = "  "

def _finish_step():
    """Overwrite busy symbol with checkmark and print elapsed time."""
    global _step_t0
    if _step_t0 is not None:
        elapsed = _time.time() - _step_t0
        print(f"{_CLEAR_LINE}{_step_indent}{_SYM_OK} {_step_msg}"
              f" {_DIM}({elapsed:.1f}s){_RESET}", file=sys.stderr)
        _step_t0 = None

def step(msg, indent=0):
    """Start a new progress step. Shows ↻ until the next step replaces it with ✓."""
    global _step_t0, _step_msg, _step_indent
    _finish_step()
    _step_indent = "  " + "  " * indent
    _step_msg = msg
    print(f"{_step_indent}{_SYM_BUSY} {msg}", end="", file=sys.stderr, flush=True)
    _step_t0 = _time.time()

def step_detail(detail):
    """Append detail to the current step (before timing is printed)."""
    global _step_msg
    _step_msg += f": {detail}"
    print(f": {detail}", end="", file=sys.stderr, flush=True)

def step_done():
    _finish_step()

def step_fail(msg):
    """Mark the current step as failed with ✗ and die."""
    global _step_t0
    if _step_t0 is not None:
        elapsed = _time.time() - _step_t0
        print(f"{_CLEAR_LINE}{_step_indent}{_SYM_FAIL} {_step_msg}"
              f" {_DIM}({elapsed:.1f}s){_RESET}", file=sys.stderr)
        _step_t0 = None
    die(msg)


_ssh_control_path = None

def _ssh_mux_flags():
    """SSH multiplexing flags — reuses a single connection for all calls."""
    global _ssh_control_path
    if _ssh_control_path is None:
        _ssh_control_path = f"/tmp/configure-remote-ssh_{os.getpid()}_%h"
    return ["-o", "ControlMaster=auto",
            "-o", f"ControlPath={_ssh_control_path}",
            "-o", "ControlPersist=30s"]

def _ssh_mux_cleanup():
    """Stop the SSH master connection."""
    if _ssh_control_path:
        import glob
        for sock in glob.glob(_ssh_control_path.replace("%h", "*")):
            subprocess.run(["ssh", "-o", f"ControlPath={sock}", "-O", "exit", "dummy"],
                           capture_output=True)

def ssh_check(host, *cmd, timeout=15):
    """Run a command on the remote, return stdout stripped. Returns None on failure."""
    try:
        r = subprocess.run(
            ["ssh"] + _ssh_mux_flags() + ["-o", "ConnectTimeout=5", host] + [" ".join(cmd)],
            capture_output=True, text=True, timeout=timeout)
        return r.stdout.strip() if r.returncode == 0 else None
    except subprocess.TimeoutExpired:
        return None


def rsync(src, dst, **kwargs):
    """Run rsync -az with progress on stderr."""
    kwargs.setdefault("stdout", sys.stderr)
    subprocess.run(["rsync", "-az", "--progress", src, dst], **kwargs)


def sha1_file(path):
    """SHA1 of a local file, or None if it doesn't exist."""
    if not os.path.isfile(path):
        return None
    h = hashlib.sha1()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def remote_sha1(host, path):
    """SHA1 of a remote file via ssh."""
    out = ssh_check(host, "sha1sum", path)
    return out.split()[0] if out else None


def detect_remote(host):
    """Detect remote arch and OS. Returns (arch, os_id)."""
    arch = ssh_check(host, "uname", "-m")
    if not arch:
        die("Failed to detect remote architecture")
    os_id = ssh_check(host, "bash", "-c",
                       "'source /etc/os-release 2>/dev/null && echo $ID'") or "unknown"
    return arch, os_id


def pick_setup_script(arch, os_id):
    """Pick the right setup script for the detected system."""
    if os_id in ("ubuntu", "debian"):
        if arch != "aarch64":
            die(f"Ubuntu setup script only supports aarch64 (got {arch})")
        return os.path.join(SCRIPT_DIR, "setup_aarch64_ubuntu.sh")
    elif os_id in ("amzn",):
        return os.path.join(SCRIPT_DIR, "setup_al2.sh")
    else:
        die(f"Unsupported OS: {os_id} (supported: Ubuntu, Amazon Linux 2)")


def resolve_local_home(explicit):
    """Resolve local Isabelle installation root."""
    if explicit:
        return explicit
    env = os.environ.get("ISABELLE_HOME")
    if env:
        isa = os.path.join(env, "isabelle")
        if os.path.isfile(isa):
            return os.path.dirname(env)
        die(f"ISABELLE_HOME={env} but {isa} not found")
    die("Set ISABELLE_HOME or use --local-isabelle-home")


def query_base_platform(host, remote_home, use_64):
    """Query the base ML platform name from the remote."""
    base = ssh_check(host, remote_home + "/bin/isabelle", "getenv", "-b", "ISABELLE_PLATFORM64")
    if not base:
        die("Failed to query ISABELLE_PLATFORM64")
    if not use_64:
        base = base.replace("arm64-", "arm64_32-", 1)
    return base


def local_platform_dir(local_home, platform):
    return os.path.join(local_home, POLYML_CONTRIB, platform)


def local_heap_dir(platform):
    return os.path.join(os.path.expanduser("~"), ".isabelle", ISABELLE_VERSION,
                        "heaps", f"{HEAP_PREFIX}_{platform}")


def remote_user_heap_dir(host, base_platform):
    """Remote user heap directory: ~/.isabelle/{ISABELLE_VERSION}/heaps/<prefix>_<platform>."""
    remote_home = ssh_check(host, "printenv", "HOME") or ""
    return f"{remote_home}/.isabelle/{ISABELLE_VERSION}/heaps/{HEAP_PREFIX}_{base_platform}"





# ---------------------------------------------------------------------------
# setup subcommand
# ---------------------------------------------------------------------------

def cmd_setup(args):
    host = args.host
    user = host.split("@")[0] if "@" in host else os.environ.get("USER") or die("USER not set")
    remote_home = args.isabelle_home or f"/home/{user}/{ISABELLE_VERSION}"
    local_home = resolve_local_home(args.local_isabelle_home)

    info(f"setup {host}")

    step(f"Checking local Isabelle installation: {local_home}")

    # Verify SSH
    step(f"Connecting to {host}")
    if ssh_check(host, "true", timeout=10) is None:
        step_fail(f"Cannot connect to {host}")

    arch, os_id = detect_remote(host)

    # Early check: if we know the platform name and it exists locally,
    # fail fast before running expensive remote setup.
    if args.ml_platform and not args.force_write_local and not args.copy_from_local:
        early_poly = os.path.join(local_platform_dir(local_home, args.ml_platform), "poly")
        if os.path.isfile(early_poly):
            step_fail(f"ML platform {args.ml_platform} already exists locally at "
                      f"{local_platform_dir(local_home, args.ml_platform)}\n"
                      f"Use --force-write-local to overwrite, or --copy-from-local to push to remote.")

    # Install Isabelle on remote if needed
    if ssh_check(host, "test", "-d", remote_home) is None:
        setup_script = pick_setup_script(arch, os_id)
        step(f"Installing Isabelle on remote ({os.path.basename(setup_script)})")
        print("", file=sys.stderr)
        install_dir = os.path.basename(remote_home)
        setup_args = [setup_script, host, install_dir,
                      "64" if args.use_64 else "32"]
        if args.copy_from_local:
            setup_args.append("skip_build")
        rc = subprocess.call(setup_args)
        if rc != 0:
            step_fail("Remote Isabelle installation failed")
    else:
        step(f"Checking remote Isabelle installation: {remote_home} ({arch} {os_id})")

    step("Identifying ML platform")
    base_platform = query_base_platform(host, remote_home, args.use_64)
    platform = args.ml_platform
    if not platform:
        remote_poly = f"{remote_home}/{POLYML_CONTRIB}/{base_platform}/poly"
        rh = remote_sha1(host, remote_poly)
        if not rh:
            step_fail(f"Failed to hash remote poly: {remote_poly}")
        platform = f"{base_platform}-{rh[:7]}"
    step_detail(platform)

    local_plat_dir = local_platform_dir(local_home, platform)
    local_poly = os.path.join(local_plat_dir, "poly")
    local_hdir = local_heap_dir(platform)
    platform_exists_locally = os.path.isfile(local_poly)

    # Determine sync direction
    if args.force_write_local and args.copy_from_local:
        step_fail("Cannot use both --force-write-local and --copy-from-local")

    if args.copy_from_local:
        _setup_copy_from_local(host, remote_home, local_home,
                               platform, base_platform, local_plat_dir, local_hdir,
                               sync_all=args.sync_all_heaps)
    elif args.force_write_local:
        _setup_write_local(host, remote_home, local_home,
                           platform, base_platform, local_plat_dir, local_hdir,
                           force=True)
    else:
        if platform_exists_locally:
            step_fail(f"ML platform {platform} already exists locally at {local_plat_dir}\n"
                      f"Use --force-write-local to overwrite, or --copy-from-local to push to remote.")
        _setup_write_local(host, remote_home, local_home,
                           platform, base_platform, local_plat_dir, local_hdir,
                           force=False)

    step_done()
    info(f"\n{_SYM_OK} Setup complete.")


def _setup_write_local(host, remote_home, local_home,
                       platform, base_platform, local_plat_dir, local_hdir,
                       force):
    """Copy poly binary and heaps from remote to local."""
    remote_poly = f"{remote_home}/{POLYML_CONTRIB}/{base_platform}/poly"
    local_poly = os.path.join(local_plat_dir, "poly")

    if force and os.path.exists(local_plat_dir):
        step("Removing existing local platform")
        shutil.rmtree(local_plat_dir)
    if force and os.path.exists(local_hdir):
        step("Removing existing local heaps")
        shutil.rmtree(local_hdir)

    # Poly binary
    step("Fetching poly binary from remote")
    os.makedirs(local_plat_dir, exist_ok=True)
    rsync(f"{host}:{remote_poly}", local_poly, check=True)
    os.chmod(local_poly, 0o755)

    # Heaps
    remote_hdir = remote_user_heap_dir(host, base_platform)
    os.makedirs(local_hdir, exist_ok=True)
    for heap in ("Pure", "HOL"):
        remote_path = f"{remote_hdir}/{heap}"
        if ssh_check(host, "test", "-f", remote_path) is None:
            step_fail(f"Heap {heap} not found at {remote_path}")
        local_path = os.path.join(local_hdir, heap)
        step(f"Fetching {heap} heap from remote", indent=1)
        rsync(f"{host}:{remote_path}", local_path, check=True)

    # Log
    remote_log = f"{remote_hdir}/log"
    local_log = os.path.join(local_hdir, "log")
    if ssh_check(host, "test", "-d", remote_log) is not None:
        step("Fetching build log from remote", indent=1)
        os.makedirs(local_log, exist_ok=True)
        rsync(f"{host}:{remote_log}/", local_log + "/", check=True)


def _setup_copy_from_local(host, remote_home, local_home,
                           platform, base_platform, local_plat_dir, local_hdir,
                           sync_all=False):
    """Copy poly binary and heaps from local to remote.

    All heaps (including Pure/HOL) are synced to the remote user heap directory.
    """
    local_poly = os.path.join(local_plat_dir, "poly")
    if not os.path.isfile(local_poly):
        step_fail(f"Local poly not found: {local_poly}")

    remote_poly_dir = f"{remote_home}/{POLYML_CONTRIB}/{base_platform}"
    remote_poly = f"{remote_poly_dir}/poly"

    step("Pushing poly binary to remote")
    rsync(local_poly, f"{host}:{remote_poly}", check=True)

    # All heaps go to user heap dir
    remote_hdir = remote_user_heap_dir(host, base_platform)

    if sync_all:
        heaps = [f for f in os.listdir(local_hdir)
                 if os.path.isfile(os.path.join(local_hdir, f))]
    else:
        heaps = ["Pure", "HOL"]

    for heap in heaps:
        local_path = os.path.join(local_hdir, heap)
        if not os.path.isfile(local_path):
            step_fail(f"Local heap not found: {local_path}")
        sz = os.path.getsize(local_path)
        step(f"Pushing {heap} ({sz // (1024*1024)}MB) to remote", indent=1)
        ssh_check(host, "mkdir", "-p", remote_hdir)
        remote_path = f"{remote_hdir}/{heap}"
        rsync(local_path, f"{host}:{remote_path}", check=True)

    # Log
    local_log = os.path.join(local_hdir, "log")
    if os.path.isdir(local_log):
        step("Pushing build log to remote", indent=1)
        ssh_check(host, "mkdir", "-p", f"{remote_hdir}/log")
        rsync(local_log + "/", f"{host}:{remote_hdir}/log/", check=True)


# ---------------------------------------------------------------------------
# run subcommand
# ---------------------------------------------------------------------------

def cmd_run(args):
    host = args.host
    user = host.split("@")[0] if "@" in host else os.environ.get("USER") or die("USER not set")
    remote_home = args.isabelle_home or f"/home/{user}/{ISABELLE_VERSION}"
    local_home = resolve_local_home(args.local_isabelle_home)
    proxy = os.path.join(SCRIPT_DIR, "ml_proxy.py")

    info(f"run {host}")

    step(f"Checking local Isabelle installation: {local_home}")

    # Verify SSH
    step(f"Establishing SSH connection to {host}")
    if ssh_check(host, "true", timeout=10) is None:
        step_fail(f"Cannot connect to {host}")

    arch, os_id = detect_remote(host)

    step(f"Checking remote Isabelle installation: {remote_home} ({arch} {os_id})")
    if ssh_check(host, "test", "-d", remote_home) is None:
        step_fail(f"Isabelle not found at {remote_home} (run 'setup' first)")

    base_platform = query_base_platform(host, remote_home, args.use_64)

    # Determine local platform
    if args.ml_platform:
        platform = args.ml_platform
        step(f"Using ML platform: {platform}")
        step_done()
    else:
        step("Identifying ML platform")
        remote_poly = f"{remote_home}/{POLYML_CONTRIB}/{base_platform}/poly"
        remote_hash = remote_sha1(host, remote_poly)
        if not remote_hash:
            step_fail(f"Failed to hash remote poly: {remote_poly}")

        polyml_dir = os.path.join(local_home, POLYML_CONTRIB)
        platform = None
        if os.path.isdir(polyml_dir):
            for entry in os.listdir(polyml_dir):
                lp = os.path.join(polyml_dir, entry, "poly")
                if os.path.isfile(lp) and sha1_file(lp) == remote_hash:
                    platform = entry
                    step_detail(platform)
                    break
        if not platform:
            step_fail("No local poly binary matches remote. Run 'setup' first.")

    # Verify poly and heap hashes match between local and remote
    remote_poly = f"{remote_home}/{POLYML_CONTRIB}/{base_platform}/poly"
    local_poly = os.path.join(local_home, POLYML_CONTRIB, platform, "poly")

    step("Checking poly hash", indent=1)
    lh = sha1_file(local_poly)
    if not lh:
        step_fail(f"Local poly not found: {local_poly}")
    rh = remote_sha1(host, remote_poly)
    if rh and lh != rh:
        step_fail(f"Poly binary SHA1 MISMATCH for {platform}\n"
                  f"  local:  {lh} ({local_poly[:7]})\n"
                  f"  remote: {rh} ({remote_poly[:7]})")

    lhdir = local_heap_dir(platform)
    remote_hdir = remote_user_heap_dir(host, base_platform)
    for heap in ("Pure", "HOL"):
        step(f"Checking {heap} heap", indent=1)
        local_path = os.path.join(lhdir, heap)
        lh = sha1_file(local_path)
        if not lh:
            step_fail(f"Local heap missing: {local_path}\nRun 'setup' first.")
        lh = sha1_file(local_path)
        rh = remote_sha1(host, f"{remote_hdir}/{heap}")
        if rh and lh != rh:
            step_fail(f"{heap} heap SHA1 mismatch for {platform}\n"
                      f"  local:  {lh[:7]}\n"
                      f"  remote: {rh[:7]}")

    # Sync local heaps to remote
    extra_heaps = sorted(f for f in os.listdir(lhdir)
                         if os.path.isfile(os.path.join(lhdir, f))
                         and f not in ("Pure", "HOL"))
    sync = args.sync_heaps
    if extra_heaps and sync is None:
        step_done()
        die(f"Additional local heaps: {_BOLD}{', '.join(extra_heaps)}{_RESET}\n"
            f"Use {_GREEN}--sync-heaps{_RESET} to sync all heaps to remote, "
            f"or {_YELLOW}--no-sync-heaps{_RESET} to skip.")

    if sync:
        step("Syncing heaps to remote")
        step_done()
        remote_hdir = remote_user_heap_dir(host, base_platform)
        heaps = [f for f in os.listdir(lhdir)
                 if os.path.isfile(os.path.join(lhdir, f))]
        for heap in heaps:
            sz = os.path.getsize(os.path.join(lhdir, heap))
            step(f"{heap} ({sz // (1024*1024)}MB)", indent=1)
            local_path = os.path.join(lhdir, heap)
            ssh_check(host, "mkdir", "-p", remote_hdir)
            remote_path = f"{remote_hdir}/{heap}"
            rsync(local_path, f"{host}:{remote_path}", check=True)
        local_log = os.path.join(lhdir, "log")
        if os.path.isdir(local_log):
            step("log", indent=1)
            ssh_check(host, "mkdir", "-p", f"{remote_hdir}/log")
            rsync(local_log + "/", f"{host}:{remote_hdir}/log/",
                  check=True)

    step("Setting thread count")
    if args.threads:
        threads = str(args.threads)
        step_detail(f"{threads} (forced)")
    else:
        remote_nproc = int(ssh_check(host, "nproc") or "8")
        threads = str(min(remote_nproc, args.maxthreads))
        step_detail(f"{threads} (remote has {remote_nproc} cores, max {args.maxthreads})")

    step(f"Generating jEdit flags (threads={threads}, platform={platform})")
    step_done()

    poly_overrides = ""
    for opt, val in [("--minheap", args.minheap),
                     ("--maxheap", args.maxheap),
                     ("--gcthreads", args.gcthreads),
                     ("-H", args.initial_heap),
                     ("--gcpercent", args.gcpercent)]:
        if val is not None:
            poly_overrides += f" {opt} {val}"

    flags = (
        f"-o ML_platform={platform}"
        f" -o threads={threads}"
        f" -o jedit_auto_resolve=true"
        f" -o 'process_policy={proxy}"
        f" -v --log /tmp/ml_proxy.log"
        f" --host {host}"
        f" --target-isabelle-home {remote_home}"
        f" --target-ml-platform {base_platform}"
        f"{poly_overrides} --'"
    )

    if sys.stdout.isatty():
        info(f"\nUse the following flags when starting Isabelle/jEdit:\n"
             f"{'─' * 60}")

    print(flags)


# ---------------------------------------------------------------------------
# list subcommand
# ---------------------------------------------------------------------------

def cmd_list(args):
    local_home = resolve_local_home(args.local_isabelle_home)
    polyml_dir = os.path.join(local_home, POLYML_CONTRIB)
    heap_base = os.path.join(os.path.expanduser("~"), ".isabelle", ISABELLE_VERSION, "heaps")

    if not os.path.isdir(polyml_dir):
        die(f"No polyml contrib dir: {polyml_dir}")

    entries = []
    for entry in sorted(os.listdir(polyml_dir)):
        poly = os.path.join(polyml_dir, entry, "poly")
        if not os.path.isfile(poly):
            continue
        hdir = os.path.join(heap_base, f"{HEAP_PREFIX}_{entry}")
        heaps = []
        if os.path.isdir(hdir):
            heaps = sorted(f for f in os.listdir(hdir) if os.path.isfile(os.path.join(hdir, f)))
        h = sha1_file(poly)[:7]
        entries.append((entry, h, heaps))

    if not entries:
        info("No ML platforms found.")
        return

    name_w = max(len(e[0]) for e in entries)
    info(f"\n{'ML Platform':<{name_w}}  {'Poly Hash':<9}  Heaps")
    info(f"{'─' * name_w}  {'─' * 9}  {'─' * 40}")
    for name, h, heaps in entries:
        heap_str = f"{_DIM}none{_RESET}" if not heaps else ", ".join(heaps)
        print(f"{_BOLD}{name:<{name_w}}{_RESET}  {_DIM}{h}{_RESET}       {heap_str}",
              file=sys.stderr)
    info("")


# ---------------------------------------------------------------------------
# remove subcommand
# ---------------------------------------------------------------------------

def cmd_remove(args):
    local_home = resolve_local_home(args.local_isabelle_home)
    platform = args.platform
    plat_dir = local_platform_dir(local_home, platform)
    hdir = local_heap_dir(platform)

    to_remove = []
    if os.path.exists(plat_dir):
        to_remove.append(("Poly binary dir", plat_dir))
    if os.path.exists(hdir):
        to_remove.append(("Heap dir", hdir))

    if not to_remove:
        die(f"Nothing to remove for platform {platform}")

    print(f"Will remove platform '{platform}':", file=sys.stderr)
    for label, path in to_remove:
        print(f"  {label}: {path}", file=sys.stderr)
        if label == "Heap dir":
            for f in sorted(os.listdir(path)):
                fp = os.path.join(path, f)
                if os.path.isfile(fp):
                    print(f"    {f} ({os.path.getsize(fp)} bytes)", file=sys.stderr)
                elif os.path.isdir(fp):
                    print(f"    {f}/", file=sys.stderr)

    if not args.yes:
        answer = input("Proceed? [y/N] ").strip().lower()
        if answer != "y":
            die("Aborted.")

    for _, path in to_remove:
        shutil.rmtree(path)
        info(f"Removed {path}")
    info("Done.")


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Configure Isabelle remote ML prover.")
    sub = parser.add_subparsers(dest="command", required=True)

    # Common arguments
    def add_common(p):
        p.add_argument("host", help="SSH host (user@host)")
        p.add_argument("--isabelle-home",
                        help="ISABELLE_HOME on remote (default: /home/<user>/{ISABELLE_VERSION})")
        p.add_argument("--local-isabelle-home",
                        help="Local ISABELLE_HOME (default: auto-detect)")
        bits = p.add_mutually_exclusive_group()
        bits.add_argument("--64", dest="use_64", action="store_true", default=True,
                          help="Use 64-bit ML (default)")
        bits.add_argument("--32", dest="use_64", action="store_false",
                          help="Use 32-in-64-bit ML")
        p.add_argument("--ml-platform",
                        help="Force local ML platform name (e.g. aarch64-ubuntu)")

    # setup
    p_setup = sub.add_parser("setup",
        help="Install Isabelle on remote, sync poly/heaps")
    add_common(p_setup)
    sync = p_setup.add_mutually_exclusive_group()
    sync.add_argument("--force-write-local", action="store_true",
                      help="Overwrite local ML platform with remote poly/heaps")
    sync.add_argument("--copy-from-local", action="store_true",
                      help="Copy local poly/heaps to remote")
    p_setup.add_argument("--sync-all-heaps", action="store_true",
                         help="With --copy-from-local: sync entire heaps dir, not just Pure/HOL")
    p_setup.set_defaults(func=cmd_setup)

    # run
    p_run = sub.add_parser("run",
        help="Print jEdit flags for remote ML prover")
    add_common(p_run)
    p_run.add_argument("--sync-heaps", dest="sync_heaps",
                       action="store_true", default=None,
                       help="Sync all local heaps to remote before printing flags")
    p_run.add_argument("--no-sync-heaps", dest="sync_heaps",
                       action="store_false",
                       help="Do not sync heaps to remote")
    p_run.add_argument("--threads", type=int, default=None,
                       help="Force exact thread count (overrides --maxthreads)")
    p_run.add_argument("--maxthreads", type=int, default=16,
                       help="Maximum thread count (default: 16, capped to remote nproc)")
    p_run.add_argument("--minheap", default=None, help="Override poly --minheap (MB)")
    p_run.add_argument("--maxheap", default=None, help="Override poly --maxheap (MB)")
    p_run.add_argument("--gcthreads", default=None, help="Override poly --gcthreads")
    p_run.add_argument("-H", dest="initial_heap", default=None,
                       help="Override poly -H initial heap size (MB)")
    p_run.add_argument("--gcpercent", default=5,
                       help="Override poly --gcpercent (1-99)")
    p_run.set_defaults(func=cmd_run)

    # list
    p_list = sub.add_parser("list",
        help="List local ML platforms")
    p_list.add_argument("--local-isabelle-home",
                        help="Local ISABELLE_HOME (default: auto-detect)")
    p_list.set_defaults(func=cmd_list)

    # remove
    p_remove = sub.add_parser("remove",
        help="Remove a local ML platform and its heaps")
    p_remove.add_argument("platform", help="ML platform name to remove")
    p_remove.add_argument("--local-isabelle-home",
                          help="Local ISABELLE_HOME (default: auto-detect)")
    p_remove.add_argument("-y", "--yes", action="store_true",
                          help="Skip confirmation prompt")
    p_remove.set_defaults(func=cmd_remove)

    args = parser.parse_args()
    try:
        args.func(args)
    finally:
        _ssh_mux_cleanup()


if __name__ == "__main__":
    main()
