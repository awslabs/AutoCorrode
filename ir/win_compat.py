
"""Windows compatibility helpers for the I/R Python daemon.

The `isabelle` launcher is a Cygwin *bash script*, not a native Windows
executable, so `subprocess` cannot run it directly on Windows -- CreateProcess
raises ``WinError 193: %1 is not a valid Win32 application``.  On Windows we
therefore run it as  ``bash <isabelle-script> <args...>``  using the Cygwin
bash that ships with Isabelle, converting absolute Windows path arguments to
``/cygdrive/`` form so Cygwin can open them.

On POSIX every function here is a thin pass-through, so behaviour on
Linux/macOS is unchanged.
"""

import getpass
import os
import re
import shutil
import subprocess
import sys

IS_WINDOWS = (os.name == "nt")

# Matches an absolute Windows path such as  C:\x  or  C:/x .  Used to decide
# which argv elements are filesystem paths that need /cygdrive/ conversion;
# ML expressions, option strings and session names never match.
_WIN_ABS = re.compile(r'^[A-Za-z]:[\\/]')


def to_cygwin_path(p):
    r"""Convert  C:\Users\me\x  ->  /cygdrive/c/Users/me/x .

    Non-(absolute-Windows) strings are returned unchanged, so this is safe to
    apply to every argument.
    """
    if not isinstance(p, str) or not _WIN_ABS.match(p):
        return p
    drive = p[0].lower()
    rest = p[2:].replace("\\", "/")
    if not rest.startswith("/"):
        rest = "/" + rest
    return "/cygdrive/" + drive + rest


_CYGDRIVE = re.compile(r'^/cygdrive/([A-Za-z])(/.*)?$')


def from_cygwin_path(p):
    r"""Convert  /cygdrive/c/Users/me/x  ->  C:\Users\me\x  (Windows only).

    Values that Isabelle returns (e.g. ``isabelle getenv ISABELLE_HOME``) are
    Cygwin POSIX paths; native Windows Python's ``open``/``os.path`` cannot use
    them.  Non-cygdrive strings and all POSIX platforms are passed through
    unchanged, so this is safe to apply to any getenv result.
    """
    if not IS_WINDOWS or not isinstance(p, str):
        return p
    m = _CYGDRIVE.match(p)
    if not m:
        return p
    drive = m.group(1).upper()
    rest = (m.group(2) or "").replace("/", os.sep)
    return drive + ":" + (rest if rest else os.sep)


def find_cygwin_bash(isabelle_bin):
    """Locate the Cygwin ``bash.exe`` bundled with Isabelle.

    Priority: the ``ISABELLE_CYGWIN_BASH`` override, then well-known locations
    relative to the Isabelle distribution root (derived from the path of the
    ``isabelle`` script), then any ``bash`` on PATH.
    """
    override = os.environ.get("ISABELLE_CYGWIN_BASH")
    if override and os.path.isfile(override):
        return override
    # <root>/bin/isabelle  ->  <root>
    root = os.path.dirname(os.path.dirname(os.path.abspath(isabelle_bin)))
    candidates = [
        os.path.join(root, "cygwin", "bin", "bash.exe"),
        os.path.join(root, "contrib", "cygwin", "bin", "bash.exe"),
    ]
    for c in candidates:
        if os.path.isfile(c):
            return c
    found = shutil.which("bash")
    if found:
        return found
    raise RuntimeError(
        "Could not locate the Cygwin bash bundled with Isabelle. "
        "Set the ISABELLE_CYGWIN_BASH environment variable to the full path "
        "of <Isabelle>/cygwin/bin/bash.exe")


_cygwin_path_done = False


def _ensure_cygwin_on_path(bash):
    """Prepend Cygwin's bin directory to PATH (once).

    Launched straight from Windows, bash inherits the Windows PATH, which does
    not contain Cygwin's bin -- so the isabelle script's calls to ``basename``,
    ``dirname`` etc. fail with "command not found", which in turn breaks its
    ISABELLE_HOME computation.  Cygwin translates the inherited Windows PATH to
    POSIX form on startup, so adding the bin dir here makes those tools resolve.
    """
    global _cygwin_path_done
    if _cygwin_path_done:
        return
    cyg_bin = os.path.dirname(os.path.abspath(bash))
    parts = os.environ.get("PATH", "").split(os.pathsep)
    if cyg_bin.lower() not in (p.lower() for p in parts):
        os.environ["PATH"] = cyg_bin + os.pathsep + os.environ.get("PATH", "")
    _cygwin_path_done = True


def isabelle_argv(isabelle_bin, args):
    """Return an argv list that runs ``isabelle <args>`` on this platform.

    POSIX: ``[isabelle_bin, *args]`` unchanged.
    Windows: ``[bash, <isabelle-as-cygwin-path>, *args-with-paths-converted]``,
    with Cygwin's bin ensured on PATH so the script's Unix tools resolve.
    """
    args = list(args)
    if not IS_WINDOWS:
        return [isabelle_bin] + args
    bash = find_cygwin_bash(isabelle_bin)
    _ensure_cygwin_on_path(bash)
    return [bash, to_cygwin_path(isabelle_bin)] + [to_cygwin_path(a) for a in args]


# Spawn keyword args: POSIX puts the child in its own session so a later
# os.killpg() reaches the whole tree; Windows uses a new process group and is
# torn down with taskkill /T (see terminate_tree).
if IS_WINDOWS:
    SPAWN_KW = {"creationflags": subprocess.CREATE_NEW_PROCESS_GROUP}
else:
    SPAWN_KW = {"start_new_session": True}


def force_utf8_stdio():
    """Make stdout/stderr UTF-8 on Windows, whatever the console codepage is.

    Native Windows Python encodes stdout with the locale codepage (e.g.
    cp1252), so the ``●`` in our status lines raises UnicodeEncodeError and
    kills the process during startup.  ``PYTHONUTF8=1`` fixes it, but the I/Q jEdit
    plugin spawns ``python3 repl.py`` with no flags and its own environment, so
    we cannot rely on that being set -- we have to be robust on our own.

    ``errors="replace"`` means an unencodable character can never be fatal.
    Java 18+ (JEP 400) decodes subprocess output as UTF-8 by default, so I/Q
    reads these bytes correctly.  No-op on POSIX.
    """
    if not IS_WINDOWS:
        return
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, ValueError, OSError):
            pass   # not a reconfigurable TextIOWrapper (e.g. already wrapped)


def restrict_file_to_user(path):
    """Restrict *path* to the current user only.  Returns True on success.

    POSIX uses ``chmod 0600``.  Windows has no mode bits, so we reset the
    file's inherited ACEs and grant full control to the current user alone via
    ``icacls``.  This matters because on Windows the management-console
    rendezvous file holds an auth token (see ``mgmt_listen`` in repl_srv.py);
    the README threat model requires keeping other local OS users out.
    """
    if not IS_WINDOWS:
        os.chmod(path, 0o600)
        return True
    user = os.environ.get("USERNAME") or getpass.getuser()
    try:
        r = subprocess.run(
            ["icacls", path, "/inheritance:r", "/grant:r", f"{user}:F"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=15)
        return r.returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False


def terminate_tree(proc):
    """Terminate a child process *and its descendants*, cross-platform.

    POSIX: ``os.killpg(proc.pid, SIGTERM)``, with ``proc.terminate()`` as the
    fallback if the process group is already gone.  Windows has no ``killpg``,
    so use ``taskkill /F /T`` (kill tree) there instead.
    """
    if proc is None or proc.poll() is not None:
        return
    if IS_WINDOWS:
        subprocess.run(["taskkill", "/F", "/T", "/PID", str(proc.pid)],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    else:
        import signal
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except OSError:
            proc.terminate()
