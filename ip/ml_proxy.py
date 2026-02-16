#!/usr/bin/env python3
"""
Isabelle Remote ML Prover Proxy
===============================

Runs the Isabelle ML prover (Poly/ML) and Bash.Server on a remote machine
while keeping jEdit + Scala/PIDE local. No Isabelle source changes required.

Normal Isabelle Architecture
----------------------------

In a standard local session, Isabelle has three communicating processes:

    jEdit/Scala (GUI + PIDE)          Poly/ML (prover)
    ┌─────────────────────┐           ┌─────────────────────┐
    │                     │           │                     │
    │  Document model     │  PIDE     │  Theory processing  │
    │  Rendering          │◄════════► │  Proof checking     │
    │  Session management │  TCP      │  Code generation    │
    │                     │           │                     │
    │  Bash.Server ◄──────┼───────────┼── bash_process()    │
    │  (localhost:P2)     │  TCP      │  (sledgehammer etc) │
    │                     │           │                     │
    └─────────────────────┘           └─────────────────────┘

Startup sequence:
  1. jEdit/Scala creates a System_Channel (TCP server on localhost:P1)
     and writes its address + password to ISABELLE_PROCESS_OPTIONS file.
  2. Scala starts a Bash.Server on localhost:P2 (random port + password).
  3. Scala spawns the poly process wrapped in a configurable `process_policy`,
     passing the full poly command line. The poly process inherits
     ISABELLE_PROCESS_OPTIONS.
  4. Poly/ML reads ISABELLE_PROCESS_OPTIONS, connects back to localhost:P1,
     sends the password. The PIDE channel is established.
  5. Scala sends `Prover.options` over PIDE, which includes
     bash_process_address=127.0.0.1:P2 and bash_process_password=UUID.
  6. When ML needs external tools (e.g. sledgehammer), it connects to
     the Bash.Server at 127.0.0.1:P2 to run shell commands.
  7. For heap builds, Scala sends `build_session` over PIDE, which includes
     session_directories (filesystem paths) and options (including
     bash_process_address/password). ML reads theory files from disk.
  8. For interactive builds, Poly/ML receives file contents via PIDE;
     it does not read the file system.

Proxied Architecture
--------------------

This script interposes between Scala and a remote Poly/ML:

    LOCAL MACHINE                                   REMOTE MACHINE
    ┌──────────────────┐                            ┌──────────────────┐
    │ jEdit/Scala      │                            │ Poly/ML          │
    │                  │                            │                  │
    │ System_Channel   │ ┌───────────────┐   SSH    │                  │
    │ (localhost:P1) ◄─┼─┤ PIDE proxy    ├───-R────►│ connects to      │
    │                  │ │ (localhost:P3)│  tunnel  │ localhost:P3     │
    │ Bash.Server      │ │               │          │                  │
    │ (localhost:P2)   │ │ Intercepts:   │          │ bash_process()───┼─┐
    │ (unused)         │ │  • Prover.    │          │                  │ │
    │                  │ │    options    │          └──────────────────┘ │
    │                  │ │  • build_     │                               │
    │                  │ │    session    │          ┌──────────────────┐ │
    │                  │ │  • ML→Scala   │          │ Remote           │ │
    │                  │ │    errors     │          │ Bash.Server      │◄┘
    │                  │ └───────────────┘          │ (localhost:P4)   │
    │                  │                            └──────────────────┘
    └──────────────────┘

Startup sequence:
  1. The proxy + configuration is passed to Isabelle as a `process_policy`;
     whenever Isabelle invokes Poly/ML, the invocation will thus be wrapped
     by the proxy.
  2. Proxy rewrites paths in the command line: ISABELLE_HOME, POLYML_HOME,
     ML_PLATFORM, HOME (for heap paths in ~/.isabelle/).
  3. Proxy matches local Isabelle components to remote components by basename,
     building a path rewrite table for components outside ISABELLE_HOME/HOME.
  4. Proxy extracts the PIDE channel port (P1) from ISABELLE_PROCESS_OPTIONS.
  5. Proxy creates a PIDE proxy server on localhost:P3 (random port).
  6. Proxy starts a Bash.Server on the remote (localhost:P4), capturing its
     address and password.
  7. Proxy rewrites ISABELLE_PROCESS_OPTIONS: P1 → P3 (so ML connects to
     the proxy, not directly to Scala). Copies it to the remote.
  8. Proxy rewrites ISABELLE_INIT_SESSION: replaces local paths with remote
     paths (components, ISABELLE_HOME, HOME). Copies it to the remote.
  9. Proxy queries remote Isabelle env vars and builds the remote command.
 10. For heap builds of local sessions (cwd outside ISABELLE_HOME), proxy
     rsyncs the session source directory to a temp dir on the remote.
 11. Proxy starts the PIDE proxy thread (bidirectional message forwarding).
 12. Proxy launches poly on the remote via SSH with a reverse tunnel
     (remote:P3 → local:P3) so ML can reach the PIDE proxy.

PIDE proxy interceptions (Scala→ML):
  • Prover.options: rewrites bash_process_address/password to point to the
    remote Bash.Server (P4) instead of the local one (P2).
  • build_session: rewrites session_directories paths (local → remote) and
    bash_process_address/password (same as Prover.options).

PIDE proxy interceptions (ML→Scala):
  • "error" with "No such file": downgraded to "warning" (remote ML cannot
    verify local file existence for \\<^file> annotations).
  • "status" with "failed" on text commands: dropped (cosmetic failure from
    \\<^file> checks; the subsequent "finished" status completes the command).

Post-build:
  • If ML_Heap.save_child is in the command (heap build), the built heap is
    rsynced back from remote to the local heap directory, reversing the
    platform/HOME/ISABELLE_HOME path rewrites. This way, an 'inventory' of
    remote heaps can be retained on the localhost.
  • Temp files on the remote are cleaned up.

Usage
-----

To use the proxy directly, pass it as a Poly/ML wrapper via the existing
`process_policy` option, e.g.:

    isabelle jedit -l HOL -o 'process_policy=/path/to/ml_proxy.py \\
      -v --log /tmp/ml_proxy.log \\
      --host user@remote \\
      --target-isabelle-home /path/to/isabelle/on/remote \\
      --target-ml-platform arm64-linux --'

To make this more convenient, however, the `configure-remote.py` script
should be used to generate the required Isabelle flags. See the documentation
of `configure-remote.py` for more information.
"""

import argparse
import os
import re
import shlex
import socket
import subprocess
import sys
import tempfile
import threading
import time

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

import logging

logger = logging.getLogger("ml_proxy")

def setup_logging(verbose, log_file=None):
    """Configure the logger. DEBUG for verbose, WARNING otherwise.

    Always logs to stderr. If log_file is set, also logs to that file.
    """
    level = logging.DEBUG if verbose else logging.WARNING
    fmt = logging.Formatter("[ml_proxy] %(asctime)s.%(msecs)03d %(levelname)s %(message)s",
                           datefmt="%H:%M:%S")
    logger.setLevel(level)
    stderr_handler = logging.StreamHandler(sys.stderr)
    stderr_handler.setFormatter(fmt)
    logger.addHandler(stderr_handler)
    if log_file:
        file_handler = logging.FileHandler(log_file)
        file_handler.setFormatter(fmt)
        logger.addHandler(file_handler)

# ---------------------------------------------------------------------------
# Remote command helpers
# ---------------------------------------------------------------------------

# SSH multiplexing: first call establishes a master, subsequent calls reuse it.
_ssh_control_path = None

def ssh_control_flags():
    """Return SSH flags for connection multiplexing."""
    global _ssh_control_path
    if _ssh_control_path is None:
        _ssh_control_path = f"/tmp/ml_proxy_ssh_{os.getpid()}_%h"
    return ["-o", "ControlMaster=auto",
            "-o", f"ControlPath={_ssh_control_path}",
            "-o", "ControlPersist=60s"]

def ssh_control_cleanup():
    """Stop the SSH master connection."""
    if _ssh_control_path:
        import glob
        for sock in glob.glob(_ssh_control_path.replace("%h", "*")):
            subprocess.run(["ssh", "-o", f"ControlPath={sock}", "-O", "exit", "dummy"],
                           capture_output=True)


def ssh_run(host, *cmd_args, capture=True, ssh_flags=None, **kwargs):
    """Run a command on the remote host via SSH. Returns CompletedProcess or Popen.

    All remote command execution goes through this function.
    """
    ssh_cmd = ["ssh"] + ssh_control_flags() + (ssh_flags or []) + [host] + [" ".join(shlex.quote(str(a)) for a in cmd_args)]
    if capture:
        return subprocess.run(ssh_cmd, capture_output=True, text=True, **kwargs)
    return subprocess.Popen(ssh_cmd, **kwargs)


def ssh_run_stdout(host, *cmd_args):
    """Run a command on the remote host, return stdout stripped."""
    return ssh_run(host, *cmd_args).stdout.strip()


def query_getenv(host, isabelle_home, var):
    """Query an Isabelle environment variable on the remote via `isabelle getenv`."""
    val = ssh_run_stdout(host, isabelle_home + "/bin/isabelle", "getenv", "-b", var)
    logger.debug(f"getenv {var} = {val}")
    return val


# ---------------------------------------------------------------------------
# YXML helpers
# ---------------------------------------------------------------------------

def yxml_text_leaves(data):
    """Extract leaf text nodes from YXML-encoded data.

    YXML uses \\x05 (X) and \\x06 (Y) as delimiters instead of < and >.
    Text between markup tags appears as plain bytes between X/Y sequences.
    Returns a list of decoded text strings (skipping empty ones).
    """
    # Split on markup: \x05\x06...\x05 is an open/close tag pair
    texts = re.split(rb'\x05[\x05\x06][^\x05]*\x05', data)
    return [t.decode(errors="replace") for t in texts if t.strip()]


def parse_yxml_options(data):
    """Parse ISABELLE_PROCESS_OPTIONS YXML into (name, type, value) triples."""
    leaves = yxml_text_leaves(data)
    # Options come in groups of 3: name, type, value
    return list(zip(leaves[0::3], leaves[1::3], leaves[2::3]))


# ---------------------------------------------------------------------------
# PIDE protocol helpers
# ---------------------------------------------------------------------------

def read_pide_message(sock):
    """Read one PIDE message: header line + chunks. Returns (header, chunks) or None.

    Wire format:
        "len1,len2,...\\n"   <- ASCII header
        <chunk1><chunk2>...  <- raw bytes
    """
    header = b""
    while True:
        b = sock.recv(1)
        if not b:
            return None
        header += b
        if b == b"\n":
            break
    header_line = header.rstrip(b"\n")
    try:
        sizes = [int(s) for s in header_line.decode().split(",")]
    except (ValueError, UnicodeDecodeError):
        return None
    chunks = []
    for size in sizes:
        data = b""
        while len(data) < size:
            part = sock.recv(size - len(data))
            if not part:
                return None
            data += part
        chunks.append(data)
    return (header_line, chunks)


def write_pide_message(sock, chunks):
    """Write a PIDE message with recomputed header."""
    header = ",".join(str(len(c)) for c in chunks) + "\n"
    sock.sendall(header.encode())
    for chunk in chunks:
        sock.sendall(chunk)


def inject_proxy_message(sock, function, props=None, body=b""):
    """Inject a synthetic PIDE protocol message into the ML→Scala stream.

    Args:
        sock: The Scala-side socket.
        function: Protocol function name (e.g. "proxy_log", "proxy_status").
        props: Optional dict of additional properties (beyond "function").
        body: Optional body bytes.
    """
    prop_chunks = [f"function={function}".encode()]
    for k, v in (props or {}).items():
        prop_chunks.append(f"{k}={v}".encode())
    chunks = [b"protocol", str(len(prop_chunks)).encode()] + prop_chunks
    if body:
        chunks.append(body if isinstance(body, bytes) else body.encode())
    write_pide_message(sock, chunks)


def rewrite_bash_process_in_chunk(chunk, remote_bash_addr, remote_bash_pw):
    """Rewrite bash_process_address and password in a YXML chunk.

    Matches the YXML-encoded option fields by regex and replaces the values.
    Returns (new_chunk, was_modified).
    """
    modified = False
    if remote_bash_addr:
        m = re.search(
            rb"bash_process_address([\x05\x06:]+)string([\x05\x06:]+)(127\.0\.0\.1:\d+)",
            chunk)
        if m:
            chunk = chunk.replace(m.group(3), remote_bash_addr.encode(), 1)
            logger.debug(f"Rewrote bash_process_address: {m.group(3).decode()} -> {remote_bash_addr}")
            modified = True
    if remote_bash_pw:
        m = re.search(
            rb"(bash_process_password[\x05\x06:]+string[\x05\x06:]+)"
            rb"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})",
            chunk)
        if m:
            chunk = chunk.replace(m.group(2), remote_bash_pw.encode(), 1)
            modified = True
    return chunk, modified


def rewrite_bash_process_options(chunks, remote_bash_addr, remote_bash_pw):
    """Rewrite bash_process fields in a Prover.options message.
    Returns (new_chunks, was_modified).
    """
    if not chunks or chunks[0] != b"Prover.options":
        return chunks, False
    modified = False
    new_chunks = [chunks[0]]
    for chunk in chunks[1:]:
        chunk, m = rewrite_bash_process_in_chunk(chunk, remote_bash_addr, remote_bash_pw)
        modified = modified or m
        new_chunks.append(chunk)
    return new_chunks, modified

# ---------------------------------------------------------------------------
# PIDE proxy: sits between Scala and ML, intercepts Prover.options
# ---------------------------------------------------------------------------

def rewrite_build_session_paths(chunks, path_rewrites,
                                remote_bash_addr, remote_bash_pw):
    """Rewrite local paths and bash_process options in a build_session command.

    chunks: [b"build_session", resources_yxml, args_yxml].
    - resources_yxml: session_directories with local paths → rewritten via path_rewrites.
    - args_yxml: options including bash_process_address/password → rewritten to remote.

    Returns (new_chunks, was_modified).
    """
    if not chunks or chunks[0] != b"build_session":
        return chunks, False
    modified = False
    new_chunks = [chunks[0]]
    for chunk in chunks[1:]:
        # Rewrite paths
        for old, new in path_rewrites:
            if old in chunk:
                chunk = chunk.replace(old, new)
                modified = True
        # Rewrite bash_process fields
        chunk, m = rewrite_bash_process_in_chunk(chunk, remote_bash_addr, remote_bash_pw)
        modified = modified or m
        new_chunks.append(chunk)
    if modified:
        logger.debug("Rewrote build_session protocol command")
    return new_chunks, modified


def _start_remote_stats_monitor(host, pid, stats_dir, target_isabelle_home,
                                target_ml_home, scala_sock, scala_write_lock):
    """Start a remote poly process to monitor ML stats, inject as proxy_ml_stats."""
    def monitor_thread():
        try:
            cmd = (
                f"POLYSTATSDIR={shlex.quote(stats_dir)} "
                f"{shlex.quote(target_ml_home + '/poly')} -q "
                f"--use {shlex.quote(target_isabelle_home + '/src/Pure/ML/ml_statistics.ML')} "
                f"--eval 'ML_Statistics.monitor {pid} 0.5'"
            )
            proc = subprocess.Popen(
                ["ssh"] + ssh_control_flags() + [host, cmd],
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                stdin=subprocess.DEVNULL)
            while True:
                line = proc.stdout.readline()
                if not line:
                    break
                line = line.strip()
                if line:
                    try:
                        with scala_write_lock:
                            inject_proxy_message(scala_sock, "proxy_ml_stats",
                                                 body=line)
                    except (ConnectionError, OSError):
                        break
        except Exception as e:
            logger.debug(f"Remote stats monitor error: {e}")

    t = threading.Thread(target=monitor_thread, daemon=True)
    t.start()


def pide_proxy(server_sock, scala_port, scala_password,
               remote_bash_addr, remote_bash_pw, local_isabelle_home,
               path_rewrites=None, remote_host=None,
               stats_rewrite=None, target_isabelle_home=None,
               target_ml_home=None):
    """PIDE protocol proxy.

        ML (remote, via SSH tunnel)
            │
            ▼
        proxy_port (this proxy listens here)
            │  intercepts Prover.options
            ▼
        scala_port (Scala's System_Channel)
    """
    # Accept ML's connection
    logger.debug(f"PIDE proxy listening on {server_sock.getsockname()}")

    ml_sock, ml_addr = server_sock.accept()
    server_sock.close()
    logger.debug(f"ML connected from {ml_addr}")

    # Read ML's password line
    ml_pw = b""
    while True:
        b = ml_sock.recv(1)
        if not b or b == b"\n":
            break
        ml_pw += b

    # Connect to Scala's System_Channel, forward the password
    scala_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    scala_sock.connect(("127.0.0.1", scala_port))
    scala_sock.sendall(ml_pw + b"\n")
    logger.debug(f"Connected to Scala on 127.0.0.1:{scala_port}")

    # --- Bidirectional forwarding ---

    # Lock for writes to scala_sock (shared by ML forwarder and heartbeat)
    scala_write_lock = threading.Lock()

    def forward_scala_to_ml():
        """Parse Scala→ML messages, intercept Prover.options and build_session."""
        try:
            while True:
                msg = read_pide_message(scala_sock)
                if msg is None:
                    logger.debug("Scala disconnected")
                    try: ml_sock.shutdown(socket.SHUT_WR)
                    except OSError: pass
                    break
                header_line, chunks = msg
                cmd = chunks[0] if chunks else b""

                # Intercept Prover.options: rewrite bash_process_address/password
                if cmd == b"Prover.options":
                    new_chunks, modified = rewrite_bash_process_options(
                        chunks, remote_bash_addr, remote_bash_pw)
                    if modified:
                        write_pide_message(ml_sock, new_chunks)
                        continue

                # Intercept build_session: rewrite session_directories paths
                # and bash_process_address/password
                if cmd == b"build_session" and path_rewrites:
                    new_chunks, modified = rewrite_build_session_paths(
                        chunks, path_rewrites,
                        remote_bash_addr, remote_bash_pw)
                    if modified:
                        write_pide_message(ml_sock, new_chunks)
                        continue

                # Forward unmodified (preserve original header for efficiency)
                ml_sock.sendall(header_line + b"\n")
                for chunk in chunks:
                    ml_sock.sendall(chunk)
                count_bytes(len(header_line) + 1 + sum(len(c) for c in chunks))
        except (ConnectionError, OSError) as e:
            logger.debug(f"Scala->ML error: {e}")

    def forward_ml_to_scala():
        """Forward ML→Scala messages, downgrading file-not-found errors to warnings.

        ML→Scala message format:
            chunk[0] = kind ("error", "writeln", "status", ...)
            chunk[1] = props_length (number of property chunks)
            chunk[2..2+N-1] = property chunks
            chunk[2+N..] = body chunks (YXML-encoded text)

        When kind is "error" and the body contains "No such file" with a path
        under the local ISABELLE_HOME, we change kind to "warning". This
        suppresses red error markup for remote file-not-found errors (e.g.
        \\<^file> annotations) while preserving the message as a warning.
        """
        local_home_bytes = local_isabelle_home.encode() if local_isabelle_home else b""
        try:
            while True:
                msg = read_pide_message(ml_sock)
                if msg is None:
                    logger.debug("ML disconnected")
                    try: scala_sock.shutdown(socket.SHUT_WR)
                    except OSError: pass
                    break
                header_line, chunks = msg
                kind = chunks[0] if chunks else b""

                # Downgrade file-not-found errors to warnings with clearer message
                if (kind == b"error" and
                        any(b"No such file" in c for c in chunks[2:])):
                    error_text = b" ".join(chunks[2:])
                    file_match = re.search(rb'No such file: "([^"]*)"', error_text)
                    missing = file_match.group(1).decode() if file_match else "?"
                    logger.debug("File-not-found error chunks:\n" + "\n".join(
                        f"  chunk[{i}]: {c[:300]!r}" for i, c in enumerate(chunks)))
                    new_prefix = b"Prover cannot verify existence of file: "
                    for j in range(2, len(chunks)):
                        chunks[j] = chunks[j].replace(b"No such file: ", new_prefix)
                    chunks[0] = b"warning"
                    logger.info(f"Prover cannot verify existence of file: {missing}")
                    with scala_write_lock:
                        write_pide_message(scala_sock, chunks)
                    continue

                # Drop "failed" status on text commands
                # (text blocks fail when \<^file> can't check remote paths,
                #  but the failure is cosmetic — the proof state is unaffected.
                #  The subsequent "finished" status will mark the command as done.)
                if (kind == b"status" and
                        any(b"label=command.text" == c for c in chunks) and
                        any(b"failed" in c for c in chunks)):
                    logger.debug("Dropped text command failed status")
                    continue

                # Suppress ML_statistics and start remote stats monitoring instead
                if (kind == b"protocol" and stats_rewrite and
                        any(b"function=ML_statistics" == c for c in chunks)):
                    # Extract PID from the message
                    stats_pid = None
                    for c in chunks:
                        if c.startswith(b"pid="):
                            stats_pid = c[4:].decode()
                    remote_stats_dir, local_stats_dir = stats_rewrite
                    if stats_pid:
                        logger.debug(f"Suppressed ML_statistics, starting remote monitor "
                                     f"(pid={stats_pid}, dir={remote_stats_dir})")
                        _start_remote_stats_monitor(
                            remote_host, stats_pid, remote_stats_dir,
                            target_isabelle_home, target_ml_home,
                            scala_sock, scala_write_lock)
                    continue

                # Forward unmodified
                n = len(header_line) + 1 + sum(len(c) for c in chunks)
                with scala_write_lock:
                    scala_sock.sendall(header_line + b"\n")
                    for chunk in chunks:
                        scala_sock.sendall(chunk)
                count_bytes(n)
        except (ConnectionError, OSError) as e:
            logger.debug(f"ML->Scala error: {e}")

    # Byte counter for throughput reporting (updated by both forwarding threads)
    byte_counter = [0]  # mutable via list; protected by GIL for atomic reads
    byte_counter_lock = threading.Lock()

    def count_bytes(n):
        with byte_counter_lock:
            byte_counter[0] += n

    def proxy_heartbeat():
        """Send periodic proxy_status with throughput to Scala/jEdit."""
        host_label = remote_host or "unknown"
        interval = 0.5
        try:
            with scala_write_lock:
                inject_proxy_message(scala_sock, "proxy_log",
                                     body=f"Proxy connected to {host_label}")
                inject_proxy_message(scala_sock, "proxy_status",
                                     props={"host": host_label, "mbps": "0.0"})
            while True:
                time.sleep(interval)
                with byte_counter_lock:
                    b = byte_counter[0]
                    byte_counter[0] = 0
                mbps = b / interval / (1024 * 1024)
                with scala_write_lock:
                    inject_proxy_message(scala_sock, "proxy_status",
                                         props={"host": host_label,
                                                "mbps": f"{mbps:.1f}"})
        except (ConnectionError, OSError):
            pass

    t1 = threading.Thread(target=forward_scala_to_ml, daemon=True)
    t2 = threading.Thread(target=forward_ml_to_scala, daemon=True)
    t3 = threading.Thread(target=proxy_heartbeat, daemon=True)
    t1.start()
    t2.start()
    t3.start()
    t1.join()
    t2.join()
    ml_sock.close()
    scala_sock.close()
    logger.debug("PIDE proxy stopped")

# ---------------------------------------------------------------------------
# Path rewriting
# ---------------------------------------------------------------------------

def rewrite_argv(poly_argv, local_isabelle_home, target_isabelle_home,
                 local_polyml_home, target_polyml_home,
                 local_platform, target_platform,
                 local_home, remote_home):
    """Rewrite paths in the poly command line.

    Replaces ISABELLE_HOME, POLYML_HOME, ML_PLATFORM, and user HOME
    (for heap paths in ~/.isabelle/).
    """
    new_argv = []
    for i, arg in enumerate(poly_argv):
        new_arg = arg
        if local_isabelle_home:
            new_arg = new_arg.replace(local_isabelle_home, target_isabelle_home)
        if local_polyml_home and local_polyml_home != target_polyml_home:
            new_arg = new_arg.replace(local_polyml_home, target_polyml_home)
        if local_platform and target_platform and local_platform != target_platform:
            new_arg = new_arg.replace(local_platform, target_platform)
        if local_home and remote_home and local_home != remote_home:
            new_arg = new_arg.replace(local_home, remote_home)
        if new_arg != arg:
            logger.debug(f"  REWRITE arg[{i}]")
        new_argv.append(new_arg)
    return new_argv

# ---------------------------------------------------------------------------
# Options file helpers
# ---------------------------------------------------------------------------

def extract_channel_port(opts_file):
    """Extract the system_channel_address port from the ISABELLE_PROCESS_OPTIONS file.

    The file is YXML-encoded and contains exactly one 127.0.0.1:PORT entry
    at this point (the PIDE channel). bash_process_address is set later via
    the PIDE protocol, not in this file.
    """
    data = open(opts_file, "rb").read()
    match = re.search(rb"127\.0\.0\.1:(\d+)", data)
    return int(match.group(1)) if match else None


def make_proxy_server():
    """Create a TCP server socket on a free port for the PIDE proxy."""
    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.bind(("127.0.0.1", 0))
    server.listen(1)
    return server

# ---------------------------------------------------------------------------
# Remote Bash.Server
# ---------------------------------------------------------------------------

def start_remote_bash_server(host, target_isabelle_home):
    """Start a Bash.Server on the remote via `isabelle scala -e`.

    A dummy `tput` is placed in PATH to work around Scala 3's `tput cols`
    crash in non-interactive SSH. Slow on first invocation (~15-30s).

    Returns (address, password, Popen).
    """
    ssh_run(host, "sh", "-c",
            "mkdir -p /tmp/isabelle-proxy-bin && "
            "printf '#!/bin/sh\\necho 80\\n' > /tmp/isabelle-proxy-bin/tput && "
            "chmod +x /tmp/isabelle-proxy-bin/tput")
    logger.debug("Starting remote Bash.Server...")
    bash_server_cmd = (
        f"PATH=/tmp/isabelle-proxy-bin:$PATH "
        f"{shlex.quote(target_isabelle_home + '/bin/isabelle')} scala -e "
        f"'{{ val server = isabelle.Bash.Server.start(debugging = true); "
        f"println(\"BASH_SERVER_ADDRESS=\" + server.address); "
        f"println(\"BASH_SERVER_PASSWORD=\" + server.password); "
        f"Thread.sleep(Long.MaxValue) }}'"
    )
    proc = subprocess.Popen(
        ["ssh"] + ssh_control_flags() + [host, bash_server_cmd],
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    addr = None
    pw = None
    deadline = time.time() + 60
    while time.time() < deadline:
        line = proc.stdout.readline().decode().strip()
        if line.startswith("BASH_SERVER_ADDRESS="):
            addr = line.split("=", 1)[1]
            logger.debug(f"Remote Bash.Server address: {addr}")
        elif line.startswith("BASH_SERVER_PASSWORD="):
            pw = line.split("=", 1)[1]
        if addr and pw:
            break
        if proc.poll() is not None:
            err = proc.stderr.read().decode()
            logger.debug(f"Remote Bash.Server failed: {err}")
            break

    if not addr or not pw:
        logger.error("Failed to start remote Bash.Server")
        sys.exit(1)
    return addr, pw, proc


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Isabelle remote ML prover proxy",
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--target-isabelle-home", required=True,
                        help="ISABELLE_HOME on the target machine")
    parser.add_argument("--target-ml-platform", default=None,
                        help="ML platform on the target (e.g. arm64-linux). "
                             "If unset, assumed same as local.")
    parser.add_argument("--host", required=True,
                        help="SSH host (user@host)")
    parser.add_argument("-v", "--verbose", action="store_true")
    parser.add_argument("--log", default=None,
                        help="Log file (default: stderr)")
    parser.add_argument("--minheap", default=None,
                        help="Override poly --minheap (MB)")
    parser.add_argument("--maxheap", default=None,
                        help="Override poly --maxheap (MB)")
    parser.add_argument("--gcthreads", default=None,
                        help="Override poly --gcthreads")
    parser.add_argument("-H", dest="initial_heap", default=None,
                        help="Override poly -H initial heap size (MB)")
    parser.add_argument("--gcpercent", default=None,
                        help="Override poly --gcpercent (1-99)")
    args, poly_argv = parser.parse_known_args()

    setup_logging(args.verbose, args.log)

    if poly_argv and poly_argv[0] == "--":
        poly_argv = poly_argv[1:]
    if not poly_argv:
        logger.error("No poly command provided")
        sys.exit(1)

    # Override poly runtime options
    for opt, val in [("--minheap", args.minheap),
                     ("--maxheap", args.maxheap),
                     ("--gcthreads", args.gcthreads),
                     ("-H", args.initial_heap),
                     ("--gcpercent", args.gcpercent)]:
        if val is not None:
            # Replace existing or append
            replaced = False
            for i, a in enumerate(poly_argv):
                if a == opt and i + 1 < len(poly_argv):
                    poly_argv[i + 1] = val
                    replaced = True
                    break
            if not replaced:
                # Insert after the poly binary (argv[0])
                poly_argv[1:1] = [opt, val]
            logger.debug(f"Override: {opt} {val}")

    target_isabelle_home = args.target_isabelle_home
    host = args.host
    local_isabelle_home = os.environ.get("ISABELLE_HOME", "")
    local_polyml_home = os.environ.get("POLYML_HOME", "")

    # Derive local ML_PLATFORM from the poly binary path in the command line.
    # The path looks like: .../contrib/polyml-X.Y.Z/PLATFORM/poly
    # This is more reliable than reading heap dirs, because ML_system_64
    # can change the platform at runtime.
    local_platform = None
    poly_path = poly_argv[0] if poly_argv else ""
    poly_match = re.search(r"/polyml-[\d.]+-?\d*/([^/]+)/poly", poly_path)
    if poly_match:
        local_platform = poly_match.group(1)
    target_platform = args.target_ml_platform or local_platform
    logger.debug(f"Local ML_PLATFORM (from command): {local_platform}")
    logger.debug(f"Target ML_PLATFORM: {target_platform}")

    local_home = os.path.expanduser("~")

    # Step 1: Query all remote environment in one SSH call
    env_dump = ssh_run_stdout(host,
        target_isabelle_home + "/bin/isabelle", "env", "bash", "-c",
        "echo __HOME__=$HOME; env | grep -E '^(ISABELLE_|ML_|POLYML_)' | sort")
    if not env_dump:
        logger.error("Failed to query remote environment")
        sys.exit(1)

    # Parse into dict; resolve symlink normalization
    raw_env = {}
    remote_home = None
    for line in env_dump.splitlines():
        if line.startswith("__HOME__="):
            remote_home = line.split("=", 1)[1]
        elif "=" in line:
            k, v = line.split("=", 1)
            raw_env[k] = v

    if not remote_home:
        logger.error("Failed to query remote HOME")
        sys.exit(1)

    resolved_isabelle_home = raw_env.get("ISABELLE_HOME", target_isabelle_home)
    target_polyml_home = raw_env.get("POLYML_HOME", "")
    if not target_polyml_home:
        logger.error("Failed to query POLYML_HOME")
        sys.exit(1)

    # Normalize resolved symlinks
    target_env_vars = {}
    for k, v in raw_env.items():
        if resolved_isabelle_home and resolved_isabelle_home != target_isabelle_home:
            v = v.replace(resolved_isabelle_home, target_isabelle_home)
        target_env_vars[k] = v
    if resolved_isabelle_home and resolved_isabelle_home != target_isabelle_home:
        target_polyml_home = target_polyml_home.replace(
            resolved_isabelle_home, target_isabelle_home)
    target_env_vars.update({
        "ISABELLE_HOME": target_isabelle_home,
        "ML_HOME": target_polyml_home + "/" + target_platform,
        "ML_PLATFORM": target_platform,
        "POLYML_HOME": target_polyml_home,
    })

    remote_components_str = target_env_vars.get("ISABELLE_COMPONENTS", "")

    logger.debug(f"Local  ISABELLE_HOME: {local_isabelle_home}")
    logger.debug(f"Target ISABELLE_HOME: {target_isabelle_home}")
    logger.debug(f"Local  HOME: {local_home}")
    logger.debug(f"Remote HOME: {remote_home}")
    logger.debug(f"POLYML_HOME: {target_polyml_home}")
    logger.debug(f"Forwarding {len(target_env_vars)} env vars")

    # Step 2: Rewrite poly command line
    # The command line contains local paths for the poly binary and session heaps.
    # We replace ISABELLE_HOME, POLYML_HOME, ML_PLATFORM, and user HOME.
    new_argv = rewrite_argv(poly_argv, local_isabelle_home, target_isabelle_home,
                            local_polyml_home, target_polyml_home,
                            local_platform, target_platform,
                            local_home, remote_home)
    logger.debug(f"Command: {new_argv[0]}")

    # Step 2b: Build component path rewrites.
    local_components = os.environ.get("ISABELLE_COMPONENTS", "").split(":")
    remote_components = remote_components_str.split(":") if remote_components_str else []
    remote_comp_by_name = {os.path.basename(c): c for c in remote_components if c}
    component_rewrites = []  # [(local_path, remote_path)]
    for lc in local_components:
        logger.debug(f"Processing local component: {lc}")
        if not lc:
            continue
        if local_isabelle_home and lc.startswith(local_isabelle_home):
            logger.debug(f"-> Skip (in local_isabelle_home: {local_isabelle_home})")
            continue
        name = os.path.basename(lc)
        rc = remote_comp_by_name.get(name)
        if rc:
            component_rewrites.append((lc, rc))
            logger.debug(f"Component rewrite: {lc} -> {rc}")
        else:
            logger.warning(f"Local component {name} ({lc}) has no match on remote")


    # Step 3: Extract PIDE channel info from options file
    local_opts = os.environ.get("ISABELLE_PROCESS_OPTIONS", "")
    local_init = os.environ.get("ISABELLE_INIT_SESSION", "")
    opts_data = open(local_opts, "rb").read() if local_opts else b""

    scala_port = extract_channel_port(local_opts) if local_opts else None
    if not scala_port:
        logger.error("Cannot extract PIDE port from options file")
        sys.exit(1)
    logger.debug(f"Scala PIDE port: {scala_port}")

    pw_match = re.search(
        rb"system_channel_password[\x05\x06:]+string[\x05\x06:]+([0-9a-f-]{36})", opts_data)
    scala_password = pw_match.group(1).decode() if pw_match else ""

    # Step 4: Pick a port for the PIDE proxy
    proxy_server = make_proxy_server()
    proxy_port = proxy_server.getsockname()[1]
    logger.debug(f"PIDE proxy port: {proxy_port}")

    # Step 5: Start remote Bash.Server (in background — result needed only for PIDE proxy)
    bash_server_future = {}
    def _start_bash_server():
        bash_server_future["result"] = start_remote_bash_server(host, target_isabelle_home)
    bash_server_thread = threading.Thread(target=_start_bash_server, daemon=True)
    bash_server_thread.start()

    # Step 6: Rewrite options file and copy to remote
    #   - system_channel_address: Scala's port → proxy port
    #   (bash_process_address is rewritten later via PIDE interception)
    opts_modified = opts_data.replace(
        f"127.0.0.1:{scala_port}".encode(),
        f"127.0.0.1:{proxy_port}".encode())
    logger.debug(f"ISABELLE_PROCESS_OPTIONS ({len(opts_modified)} bytes, "
                 f"channel rewritten {scala_port} -> {proxy_port})")
    # Dump options in human-readable form
    for name, typ, val in parse_yxml_options(opts_modified):
        logger.debug(f"  opt: {name} : {typ} = {val}")
    tmp_opts = tempfile.NamedTemporaryFile(delete=False, prefix="isabelle-proxy-opts-")
    tmp_opts.write(opts_modified)
    tmp_opts.close()

    init_modified = None
    tmp_init = None
    if local_init:
        init_data = open(local_init, "rb").read()
        logger.debug(f"ISABELLE_INIT_SESSION ({len(init_data)} bytes)")
        init_modified = init_data
        for lc, rc in component_rewrites:
            init_modified = init_modified.replace(lc.encode(), rc.encode())
        if local_isabelle_home:
            init_modified = init_modified.replace(
                local_isabelle_home.encode(), target_isabelle_home.encode())
        if local_home and remote_home and local_home != remote_home:
            init_modified = init_modified.replace(
                local_home.encode(), remote_home.encode())
        tmp_init = tempfile.NamedTemporaryFile(delete=False, prefix="isabelle-proxy-init-")
        tmp_init.write(init_modified)
        tmp_init.close()

    # Create remote tmp dir and copy both files in one batch
    remote_tmp = ssh_run_stdout(host, "mktemp", "-d", "/tmp/isabelle-proxy-XXXXXX")
    local_files = [tmp_opts.name]
    if tmp_init:
        local_files.append(tmp_init.name)
    subprocess.run(
        ["rsync", "-az", "-e", "ssh " + " ".join(ssh_control_flags())]
        + local_files + [f"{host}:{remote_tmp}/"],
        check=True)
    remote_opts = f"{remote_tmp}/{os.path.basename(tmp_opts.name)}"
    remote_init = f"{remote_tmp}/{os.path.basename(tmp_init.name)}" if tmp_init else ""
    logger.debug(f"Copied {len(local_files)} files to {host}:{remote_tmp}/")
    os.unlink(tmp_opts.name)
    if tmp_init:
        os.unlink(tmp_init.name)

    # Step 8: Build remote command
    env_parts = [
        f"ISABELLE_PROCESS_OPTIONS={shlex.quote(remote_opts)}",
        f"ISABELLE_INIT_SESSION={shlex.quote(remote_init)}",
        f"ISABELLE_TMP={shlex.quote(remote_tmp)}",
        f"POLYSTATSDIR={shlex.quote(remote_tmp)}",
    ]
    for k, v in target_env_vars.items():
        env_parts.append(f"{k}={shlex.quote(v)}")
    remote_cmd = " ".join(env_parts) + " " + " ".join(shlex.quote(a) for a in new_argv)

    # Rewrite the working directory for the remote.
    # Build processes (e.g. building HOL) use cwd=session_source_dir which is
    # under ISABELLE_HOME — we translate that to the remote equivalent.
    # Interactive sessions (jEdit) use the user's project directory as cwd,
    # which typically doesn't exist on the remote. Since all paths in the
    # poly command line are absolute, we can safely skip the cd in that case.
    #
    # Special case: building a heap for a local session (cwd outside ISABELLE_HOME).
    # The remote ML process reads theory files from disk, so we rsync the local
    # directory to a temp dir on the remote, cd into it, and add a path rewrite
    # so that session_directories in build_session point there.
    local_cwd = os.getcwd()
    is_heap_build = any("ML_Heap.save_child" in a for a in poly_argv)
    remote_src_dir = ""  # set if we rsync sources to remote

    if local_isabelle_home and local_cwd.startswith(local_isabelle_home):
        # Build inside ISABELLE_HOME (e.g. HOL): translate directly
        remote_cwd = local_cwd.replace(local_isabelle_home, target_isabelle_home)
        remote_cmd = f"cd {shlex.quote(remote_cwd)} && " + remote_cmd
        logger.debug(f"Remote cwd: {remote_cwd}")
    elif is_heap_build:
        # Build outside ISABELLE_HOME (e.g. user session): rsync sources to remote
        remote_src_dir = ssh_run_stdout(host, "mktemp", "-d", "/tmp/isabelle-proxy-src-XXXXXX")
        logger.info(f"Syncing {local_cwd}/ to {host}:{remote_src_dir}/")
        subprocess.run(
            ["rsync", "--copy-links", "-az", "-e", "ssh " + " ".join(ssh_control_flags()),
             "--chmod=a-w", local_cwd + "/", f"{host}:{remote_src_dir}/"],
            check=True)
        remote_cmd = f"cd {shlex.quote(remote_src_dir)} && " + remote_cmd
        logger.debug(f"Remote cwd (synced): {remote_src_dir}")

    # Build path rewrite table for PIDE protocol interception (build_session).
    # Order matters: more specific (longer) prefixes first to avoid partial matches.
    path_rewrites = []
    if remote_src_dir:
        # Rewrite local project path to the remote temp dir.
        # Must come before other rewrites to avoid partial match.
        path_rewrites.append((local_cwd.encode(), remote_src_dir.encode()))
    for lc, rc in component_rewrites:
        # Skip components already covered by the rsync cwd rewrite
        if remote_src_dir and lc.startswith(local_cwd):
            continue
        path_rewrites.append((lc.encode(), rc.encode()))
    if local_isabelle_home and target_isabelle_home and local_isabelle_home != target_isabelle_home:
        path_rewrites.append((local_isabelle_home.encode(), target_isabelle_home.encode()))
    if local_home and remote_home and local_home != remote_home:
        path_rewrites.append((local_home.encode(), remote_home.encode()))

    # Stats rewrite: (remote_path, local_path) for POLYSTATSDIR
    local_polystatsdir = os.environ.get("POLYSTATSDIR", "")
    stats_rewrite = (remote_tmp, local_polystatsdir) if local_polystatsdir else None
    if stats_rewrite:
        logger.debug(f"Stats rewrite: {remote_tmp} -> {local_polystatsdir}")

    # Step 9: Wait for Bash.Server, then start PIDE proxy
    bash_server_thread.join()
    remote_bash_addr, remote_bash_pw, bash_server_proc = bash_server_future["result"]
    pide_thread = threading.Thread(
        target=pide_proxy,
        args=(proxy_server, scala_port, scala_password,
              remote_bash_addr, remote_bash_pw, local_isabelle_home,
              path_rewrites, host, stats_rewrite,
              target_isabelle_home, target_env_vars.get("ML_HOME", "")),
        daemon=True)
    pide_thread.start()

    # Step 10: Launch remote poly via SSH with reverse tunnel
    ssh_cmd = [
        "ssh",
        "-C",
        "-o", "ServerAliveInterval=15",
        "-o", "ServerAliveCountMax=86400",
        "-R", f"{proxy_port}:127.0.0.1:{proxy_port}",
    ] + ssh_control_flags() + [
        host,
        remote_cmd
    ]
    logger.debug(f"SSH tunnel: remote:{proxy_port} -> local:{proxy_port} (PIDE proxy)")
    logger.debug(f"Remote command (first 500 chars): {remote_cmd[:500]}")
    logger.debug(f"Remote command (last 500 chars): ...{remote_cmd[-500:]}")
    if args.log:
        cmd_dump = os.path.splitext(args.log)[0] + "_cmd.txt"
        with open(cmd_dump, "w") as f:
            f.write(remote_cmd)
        logger.debug(f"Full remote command dumped to {cmd_dump}")

    proc = subprocess.Popen(ssh_cmd, stdin=sys.stdin, stdout=sys.stdout, stderr=sys.stderr)

    try:
        rc = proc.wait()
    except KeyboardInterrupt:
        proc.terminate()
        rc = proc.wait()

    logger.debug(f"Process exited with rc={rc}")

    # If this was a heap build (ML_Heap.save_child in command), copy the
    # built heap back from the remote to the local expected path.
    if rc == 0:
        copy_heap_back(host, new_argv, target_platform, local_platform,
                       remote_home, local_home, target_isabelle_home, local_isabelle_home)

    # Cleanup
    cleanup_remote(host, bash_server_proc, remote_opts, remote_init,
                   remote_tmp, remote_src_dir)
    ssh_control_cleanup()

    sys.exit(rc)


def copy_heap_back(host, new_argv, target_platform, local_platform,
                   remote_home, local_home, target_isabelle_home, local_isabelle_home):
    """After a successful heap build, rsync the heap from remote to local.

    Reverses the platform/HOME/ISABELLE_HOME path rewrites to determine
    the local destination path.
    """
    for arg in new_argv:
        m = re.search(r'ML_Heap\.save_child "([^"]+)"', arg)
        if m:
            remote_heap = m.group(1)
            local_heap = remote_heap
            if target_platform and local_platform and target_platform != local_platform:
                local_heap = local_heap.replace(target_platform, local_platform)
            if remote_home and local_home and remote_home != local_home:
                local_heap = local_heap.replace(remote_home, local_home)
            if target_isabelle_home and local_isabelle_home:
                local_heap = local_heap.replace(target_isabelle_home, local_isabelle_home)
            local_heap_dir = os.path.dirname(local_heap)
            os.makedirs(local_heap_dir, exist_ok=True)
            logger.info(f"Copying built heap from remote: {remote_heap} -> {local_heap}")
            try:
                t0 = time.time()
                subprocess.run(
                    ["rsync", "-az", "-e", "ssh " + " ".join(ssh_control_flags()),
                     f"{host}:{remote_heap}", local_heap],
                    check=True, timeout=300)
                elapsed = time.time() - t0
                size = os.path.getsize(local_heap)
                logger.info(f"Heap copied successfully ({size} bytes, {elapsed:.1f}s)")
            except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as e:
                logger.warning(f"Failed to copy heap: {e}")


def cleanup_remote(host, bash_server_proc, remote_opts, remote_init,
                   remote_tmp, remote_src_dir):
    """Terminate remote Bash.Server and remove temp files."""
    if bash_server_proc and bash_server_proc.poll() is None:
        bash_server_proc.terminate()
        logger.debug("Stopped remote Bash.Server")

    parts = []
    if remote_opts: parts.append(f"rm -f {shlex.quote(remote_opts)}")
    if remote_init: parts.append(f"rm -f {shlex.quote(remote_init)}")
    if remote_tmp: parts.append(f"rm -rf {shlex.quote(remote_tmp)}")
    if remote_src_dir: parts.append(f"rm -rf {shlex.quote(remote_src_dir)}")
    if parts:
        try:
            ssh_run(host, "; ".join(parts), timeout=5)
        except Exception:
            pass


if __name__ == "__main__":
    main()
