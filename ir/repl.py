#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

"""
TCP server wrapping an Isabelle/Poly/ML console with the I/R REPL.

Starts an Isabelle console process, loads ir.ML, then listens for
TCP connections on localhost. Clients send commands as single lines
(terminated by newline). The server responds with the output followed
by a sentinel line "<<DONE>>\\n". Multiple commands can be sent on the
same connection. Commands are serialized across all clients.

Note: The I/R REPL operates at the Isar level. A session (created
via Ir.init) starts in the context of a named theory — there is
no need to issue 'theory' commands. Steps are Isar commands such as
lemma, definition, fun, apply, by, etc.

The server operator gets a management console on stdin/stdout:
  - Lines starting with / are management commands
  - Everything else is sent to the REPL directly

Management commands:
  /connections   Show number of open client connections
  /log           Toggle verbose logging
  /quit          Shut down the server
  /help          Show available commands

Usage:
    python3 repl.py [--port PORT] [--isabelle PATH] [--session SESSION]
                    [--dir DIR]
"""

import argparse
import os
import re
import select
import shlex
import signal
import socket
import subprocess
import sys
import threading
import time

try:
    from prompt_toolkit import PromptSession
    from prompt_toolkit.completion import Completer, Completion
    from prompt_toolkit.filters import Always
    from prompt_toolkit.formatted_text import HTML
    from prompt_toolkit.history import FileHistory
    from prompt_toolkit.patch_stdout import patch_stdout
    _HAVE_PROMPT_TOOLKIT = True
except ImportError:
    _HAVE_PROMPT_TOOLKIT = False

IR_CMDS = {
    'Ir.init':           'id ["thy"]  — create REPL "id" importing theories',
    'Ir.fork':           'id state_idx  — fork new REPL from current at given state (0=base, ~1=latest)',
    'Ir.focus':          'id  — switch to REPL "id"',
    'Ir.step':           '"isar text"  — execute Isar text as next step in current REPL',
    'Ir.step_file':      'path  — execute Isar text from file as next step',
    'Ir.show':           '()  — show current REPL: origin, steps, staleness',
    'Ir.state':          'idx  — show proof state at step idx in current REPL (0=base, ~1=latest)',
    'Ir.text':           '()  — print concatenated Isar text of current REPL',
    'Ir.edit':           'idx "text"  — replace step idx in current REPL, mark later steps stale',
    'Ir.replay':         '()  — re-execute all stale steps in current REPL',
    'Ir.truncate':       'idx  — keep steps 0..idx in current REPL, discard the rest',
    'Ir.merge':          '()  — inline current sub-REPL back into its parent',
    'Ir.remove':         'id  — delete REPL "id" and all its sub-REPLs',
    'Ir.repls':           '()  — list all REPLs with step counts and origins',
    'Ir.theories':  '()  — list all theories loaded in the session',
    'Ir.load_theory': 'name  — load theory by name, e.g. "HOL-Library.Multiset"',
    'Ir.source':       'thy start stop  — list theory commands (start/stop are 0-based, ~N from end)',
    'Ir.sledgehammer':   'secs  — run sledgehammer on current proof goal with timeout',
    'Ir.timeout':        'secs  — set step timeout (0=unlimited, default 5s)',
    'Ir.explode':        'idx  — split multi-command step idx into individual steps',
    'Ir.find_theorems':  'n "query"  — search theorems (n=max results, 0=unlimited)',
    'Ir.back':           '()  — revert last step (synonym for truncate ~1)',
    'Ir.config':         'f  — update config (color, show_ignored, full_spans, auto_replay)',
    'Ir.help':           '()  — show full help text',
    '/connections':           'show open client connections',
    '/log':                   'toggle verbose logging',
    '/quit':                  'shut down the server',
    '/help':                  'show available commands',
}

# Structured signatures: (params_list, description)
IR_SIGS = {
    'Ir.init':          (['id', '["thy"]'], 'create REPL "id" importing theories'),
    'Ir.fork':          (['id', 'state_idx'], 'fork new REPL from current at given state (0=base, ~1=latest)'),
    'Ir.focus':         (['id'], 'switch to REPL "id"'),
    'Ir.step':          (['"isar text"'], 'execute Isar text as next step in current REPL'),
    'Ir.step_file':     (['path'], 'execute Isar text from file as next step'),
    'Ir.show':          ([], 'show current REPL: origin, steps, staleness'),
    'Ir.state':         (['idx'], 'show proof state at step idx in current REPL (0=base, ~1=latest)'),
    'Ir.text':          ([], 'print concatenated Isar text of current REPL'),
    'Ir.edit':          (['idx', '"text"'], 'replace step idx in current REPL, mark later steps stale'),
    'Ir.replay':        ([], 're-execute all stale steps in current REPL'),
    'Ir.truncate':      (['idx'], 'keep steps 0..idx in current REPL, discard the rest'),
    'Ir.merge':         ([], 'inline current sub-REPL back into its parent'),
    'Ir.remove':        (['id'], 'delete REPL "id" and all its sub-REPLs'),
    'Ir.repls':          ([], 'list all REPLs with step counts and origins'),
    'Ir.theories': ([], 'list all theories loaded in the session'),
    'Ir.load_theory': (['name'], 'load theory by name, e.g. "HOL-Library.Multiset"'),
    'Ir.source':      (['thy', 'start', 'stop'], 'list theory commands (start/stop 0-based, ~N from end)'),
    'Ir.sledgehammer':  (['secs'], 'run sledgehammer on current proof goal with timeout'),
    'Ir.timeout':       (['secs'], 'set step timeout (0=unlimited, default 5s)'),
    'Ir.explode':       (['idx'], 'split multi-command step idx into individual steps'),
    'Ir.find_theorems': (['n', '"query"'], 'search theorems (n=max results, 0=unlimited)'),
    'Ir.back':          ([], 'revert last step (synonym for truncate ~1)'),
    'Ir.config':        (['f'], 'update config (color, show_ignored, full_spans, auto_replay)'),
    'Ir.help':          ([], 'show full help text'),
}

if _HAVE_PROMPT_TOOLKIT:
    from prompt_toolkit.contrib.regular_languages.compiler import compile as grammar_compile
    from prompt_toolkit.contrib.regular_languages.completion import GrammarCompleter
    from prompt_toolkit.completion import WordCompleter


class _DynWordCompleter(Completer if _HAVE_PROMPT_TOOLKIT else object):
    """A WordCompleter whose word list can be updated at runtime."""
    def __init__(self):
        self.words = []

    def get_completions(self, document, complete_event):
        word = document.text_before_cursor
        for w in self.words:
            if w.startswith(word):
                yield Completion(w, start_position=-len(word))


class IrCompleter(Completer if _HAVE_PROMPT_TOOLKIT else object):
    """Grammar-based completer for the I/R REPL.

    Uses prompt_toolkit's regular_languages module to define the syntax of
    each command and attach completers to the variable positions.
    """

    def __init__(self):
        self._theory_completer = _DynWordCompleter()
        self._repl_completer = _DynWordCompleter()
        self.source_cache = {}

        if not _HAVE_PROMPT_TOOLKIT:
            return

        # Grammar for all Ir.* commands.
        # The prompt_toolkit grammar compiler ignores whitespace and supports
        # (?P<name>...) for named variables that get their own completer.
        g = grammar_compile(
            r"""
                (
                    # init: id then theory list
                    (?P<cmd>Ir\.init) \s+ (?P<sid>"[^"]*") \s+
                        \[ \s* (?P<thy>"[^"]*") \s*
                           (, \s* (?P<thy>"[^"]*") \s* )*
                        \]?
                |
                    (?P<cmd>Ir\.load_theory) \s+ (?P<thy>"[^"]*")
                |
                    (?P<cmd>Ir\.source) \s+ (?P<thy>"[^"]*") \s+ (?P<num>[^\s]+) \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>Ir\.focus)  \s+ (?P<rid>"[^"]*")
                |
                    (?P<cmd>Ir\.remove) \s+ (?P<rid>"[^"]*")
                |
                    (?P<cmd>Ir\.fork)   \s+ (?P<rid>"[^"]*") \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>Ir\.step)      \s+ (?P<sid>"[^"]*")
                |
                    (?P<cmd>Ir\.step_file) \s+ (?P<sid>"[^"]*")
                |
                    (?P<cmd>Ir\.edit)   \s+ (?P<num>[^\s]+) \s+ (?P<sid>"[^"]*")
                |
                    (?P<cmd>Ir\.state)        \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>Ir\.truncate)     \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>Ir\.timeout)      \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>Ir\.sledgehammer) \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>Ir\.explode)      \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>Ir\.find_theorems) \s+ (?P<num>[^\s]+) \s+ (?P<sid>"[^"]*")
                |
                    # No-arg commands and slash commands
                    (?P<cmd>[^\s]+)
                )
            """,
            unescape_funcs={'thy': lambda s: s.strip('"')},
            escape_funcs={'thy': lambda s: '"' + s + '"'},
        )

        cmd_completer = WordCompleter(sorted(IR_CMDS.keys()), sentence=True)
        self._grammar = g
        self._grammar_completer = GrammarCompleter(
            g,
            {
                'cmd': cmd_completer,
                'thy': self._theory_completer,
                'rid': self._repl_completer,
            },
        )

    @property
    def theories(self):
        return self._theory_completer.words

    def learn_theories(self, output):
        self._theory_completer.words = [l.strip() for l in output.splitlines() if l.strip()]

    def learn_source(self, theory, output):
        entries = []
        for line in output.splitlines():
            m = re.match(r'\s*(\d+)\s+(.*)', line)
            if m:
                entries.append((int(m.group(1)), m.group(2).strip()))
        self.source_cache[theory] = entries

    def learn_repls(self, output):
        self._repl_completer.words = re.findall(r'[>]?\s*(\S+)\s+\(', output)

    def get_completions(self, document, complete_event):
        if not _HAVE_PROMPT_TOOLKIT:
            return
        yield from self._grammar_completer.get_completions(document, complete_event)

PROMPT = "Poly/ML> "
PROMPT_RE = re.compile(re.escape(PROMPT) + r"$", re.MULTILINE)
SENTINEL = "<<DONE>>"


def _load_symbols(isabelle_bin):
    """Load unicode-to-Isabelle-ASCII mapping from $ISABELLE_HOME/etc/symbols."""
    isabelle_home = subprocess.check_output(
        [isabelle_bin, "getenv", "-b", "ISABELLE_HOME"],
        text=True, timeout=10).strip()
    symbols_path = os.path.join(isabelle_home, "etc", "symbols")
    unicode_to_ascii = {}
    with open(symbols_path, "r") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) >= 3 and parts[1] == "code:":
                sym = parts[0].replace('\\', '\\\\')
                cp = int(parts[2], 16)
                unicode_to_ascii[chr(cp)] = sym
    return unicode_to_ascii


UNICODE_TO_ASCII = {}


def unicode_to_isabelle(text):
    """Replace unicode characters with Isabelle ASCII encoding."""
    return "".join(UNICODE_TO_ASCII.get(c, c) for c in text)

# ANSI colors
RST = "\033[0m"
BOLD = "\033[1m"
DIM = "\033[2m"
RED = "\033[31m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
BLUE = "\033[34m"
CYAN = "\033[36m"


class BashServer:
    """Starts an Isabelle Bash.Server for external tool support (e.g. Sledgehammer)."""

    def __init__(self, isabelle):
        cmd = [isabelle, "scala", "-e",
               '{ val server = isabelle.Bash.Server.start(debugging = false); '
               'println("BASH_SERVER_ADDRESS=" + server.address); '
               'println("BASH_SERVER_PASSWORD=" + server.password); '
               'Thread.sleep(Long.MaxValue) }']
        self.proc = subprocess.Popen(
            cmd, stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            start_new_session=True)
        self.address = None
        self.password = None
        done = threading.Event()
        t = threading.Thread(target=spinner, args=("Starting Bash.Server...", done), daemon=True)
        t.start()
        while True:
            line = self.proc.stdout.readline().decode().strip()
            if not line and self.proc.poll() is not None:
                done.set(); t.join()
                err = self.proc.stderr.read().decode()
                raise RuntimeError(f"Bash.Server failed to start: {err}")
            if line.startswith("BASH_SERVER_ADDRESS="):
                self.address = line.split("=", 1)[1]
            elif line.startswith("BASH_SERVER_PASSWORD="):
                self.password = line.split("=", 1)[1]
            if self.address and self.password:
                break
        done.set()
        t.join()

    def close(self):
        if self.proc.poll() is None:
            os.killpg(self.proc.pid, signal.SIGTERM)
            try:
                self.proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(self.proc.pid, signal.SIGKILL)


def spinner(label, done_event):
    """Print a spinner with elapsed time to stderr until done_event is set."""
    frames = ['⠋', '⠙', '⠹', '⠸', '⠼', '⠴', '⠦', '⠧', '⠇', '⠏']
    start = time.time()
    i = 0
    while not done_event.is_set():
        elapsed = int(time.time() - start)
        sys.stderr.write(f"\r{frames[i % len(frames)]} {label} ({elapsed}s)  ")
        sys.stderr.flush()
        done_event.wait(0.1)
        i += 1
    sys.stderr.write(f"\r\033[K")  # clear the spinner line
    sys.stderr.flush()


class PolyMLProcess:
    """Manages a long-running Poly/ML console process."""

    def __init__(self, isabelle, session, directory, bash_server=None,
                 verbose=False, no_build=True):
        cmd = [isabelle, "console"]
        if directory:
            cmd += ["-d", directory]
        cmd += ["-l", session]
        remote = os.environ.get("ISABELLE_REMOTE")
        if remote:
            print(f"{BOLD}ISABELLE_REMOTE detected — using remote ML prover{RST}", flush=True)
            cmd += shlex.split(remote)
        if no_build:
            cmd.append("-n")
        if bash_server:
            cmd += ["-o", f"bash_process_address={bash_server.address}",
                    "-o", f"bash_process_password={bash_server.password}"]

        self.proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=0,
        )
        done = threading.Event()
        t = threading.Thread(target=spinner, args=("Loading heap...", done), daemon=True)
        t.start()
        startup = self._read_until_prompt()
        done.set()
        t.join()
        if verbose:
            print(startup, end="", flush=True)

    def _read_until_prompt(self):
        buf = b""
        while True:
            select.select([self.proc.stdout], [], [])
            chunk = os.read(self.proc.stdout.fileno(), 4096)
            if not chunk:
                rc = self.proc.wait()
                raise EOFError(
                    f"Poly/ML process terminated (rc={rc}), output so far:\n"
                    + buf.decode("utf-8", errors="replace"))
            buf += chunk
            text = buf.decode("utf-8", errors="replace")
            if PROMPT_RE.search(text):
                return text

    def send(self, command):
        line = unicode_to_isabelle(command.strip()) + "\n"
        self.proc.stdin.write(line.encode("utf-8"))
        self.proc.stdin.flush()
        raw = self._read_until_prompt()
        return self._clean_output(raw)

    @staticmethod
    def _clean_output(raw):
        text = PROMPT_RE.sub("", raw)
        text = re.sub(r"\nval it = \(\): unit\n?$", "", text)
        text = text.lstrip("\n")
        return text

    def alive(self):
        return self.proc.poll() is None

    def close(self):
        self.proc.stdin.close()
        self.proc.wait(timeout=5)


class Server:
    """TCP server that serializes client commands to the Poly/ML process."""

    def __init__(self, poly, port, host="127.0.0.1"):
        self.poly = poly
        self.port = port
        self.host = host
        self.lock = threading.Lock()
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind((host, port))
        self.sock.listen(8)
        self.running = True
        self.verbose = True
        self.clients = {}
        self.clients_lock = threading.Lock()

    def log(self, msg):
        """Print from background thread — patch_stdout handles redisplay."""
        print(msg)

    def serve_forever(self):
        self.sock.settimeout(1.0)
        while self.running:
            try:
                client, addr = self.sock.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            with self.clients_lock:
                self.clients[client] = {
                    "peer": f"{addr[0]}:{addr[1]}",
                    "started": time.time(),
                    "last_active": time.time(),
                    "commands": 0,
                    "bytes_in": 0,
                    "bytes_out": 0,
                }
            threading.Thread(
                target=self._handle_client, args=(client,), daemon=True
            ).start()

    def _handle_client(self, client):
        buf = b""
        cmd_lines = []
        logged_connect = False
        with self.clients_lock:
            peer = self.clients[client]["peer"] if client in self.clients else "?"
        try:
            while True:
                chunk = client.recv(4096)
                if not chunk:
                    break
                buf += chunk
                with self.clients_lock:
                    if client in self.clients:
                        self.clients[client]["bytes_in"] += len(chunk)
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    text = line.decode("utf-8")
                    cmd_lines.append(text)
                    if not text.rstrip().endswith(";"):
                        continue
                    command = " ".join(cmd_lines).strip()
                    cmd_lines = []
                    if not command:
                        continue
                    if not logged_connect:
                        self.log(f"{GREEN}[+] {peer} connected ({self.num_clients} total){RST}")
                        logged_connect = True
                    if self.verbose:
                        self.log(f"{CYAN}[{peer}]{RST} {YELLOW}>>>{RST} {command}")
                    with self.lock:
                        if not self.poly.alive():
                            msg = f"ERR: Poly/ML process terminated\n{SENTINEL}\n"
                            client.sendall(msg.encode("utf-8"))
                            self.running = False
                            return
                        output = self.poly.send(command)
                    if self.verbose:
                        for ln in output.splitlines():
                            self.log(f"{CYAN}[{peer}]{RST} {DIM}<<<{RST} {ln}")
                    response = (output + "\n" + SENTINEL + "\n").encode("utf-8")
                    client.sendall(response)
                    with self.clients_lock:
                        if client in self.clients:
                            self.clients[client]["commands"] += 1
                            self.clients[client]["bytes_out"] += len(response)
                            self.clients[client]["last_active"] = time.time()
        except (ConnectionResetError, BrokenPipeError):
            pass
        finally:
            with self.clients_lock:
                info = self.clients.pop(client, None)
            client.close()
            if logged_connect:
                peer = info["peer"] if info else "unknown"
                self.log(f"{RED}[-] {peer} disconnected ({self.num_clients} total){RST}")
            elif info and info.get("bytes_in", 0) > 0:
                # Received data but no valid command — log for debugging
                self.log(f"{DIM}[probe] {peer} sent {info['bytes_in']}B, no command{RST}")

    def client_info(self):
        with self.clients_lock:
            return list(self.clients.values())

    @property
    def num_clients(self):
        with self.clients_lock:
            return len(self.clients)

    def shutdown(self):
        self.running = False
        self.sock.close()


def make_toolbar(completer):
    """Create a bottom toolbar that shows the current command's signature,
    and source context when typing Theory:N arguments."""

    def toolbar():
        app = __import__('prompt_toolkit').application.get_app()
        text = app.current_buffer.text

        # Use the grammar to parse the current input
        grammar = completer._grammar
        match = grammar.match_prefix(text) if grammar else None

        cmd = ""
        active_var = None
        partial = ""
        if match:
            variables = match.variables()
            cmd = variables.get('cmd', '')
            # Find which variable the cursor is currently in (end_nodes)
            for node in match.end_nodes():
                if node.varname != 'cmd':
                    active_var = node.varname
                    partial = node.value

        # Check if we're typing a Theory:N argument for source preview
        if active_var == 'thy' and partial and ':' in partial:
            thy, idx_str = partial.rsplit(':', 1)
            segs = completer.source_cache.get(thy)
            if segs and idx_str.lstrip('~').isdigit():
                try:
                    n = int(idx_str)
                    if idx_str.startswith('~'):
                        n = max(s[0] for s in segs) + 1 + n
                except ValueError:
                    n = 0
                ctx = 3
                lines = []
                ansi_re = re.compile(r'\033\[[0-9;]*m')
                for idx, txt in segs:
                    if abs(idx - n) <= ctx:
                        display = ansi_re.sub('', txt)
                        if len(display) > 60:
                            display = display[:60] + '...'
                        display = display.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
                        if idx == n:
                            lines.append(f"<b>   {idx:4d}  {display}</b>")
                        else:
                            lines.append(f"<ansigray>   {idx:4d}  {display}</ansigray>")
                    if idx == n:
                        lines.append(f"<ansigreen>   ---- REPL starts here ----</ansigreen>")
                if lines:
                    return HTML('\n'.join(lines))

        sig = IR_SIGS.get(cmd)
        if not sig:
            return ""
        params, desc = sig
        if not params:
            return HTML(f" <b>{cmd}</b> ()  <i>{desc}</i>")

        # Map grammar variable names to param indices for highlighting.
        # For commands with multiple params of the same grammar type (e.g.
        # source has thy, num, num), we track all occurrences and use the
        # cursor position to pick the right one.
        var_to_params = {}  # varname -> [param_idx, ...]
        for i, p in enumerate(params):
            if p in ('"thy"', '["thy"]', 'name', 'thy'):
                var_to_params.setdefault('thy', []).append(i)
            elif p == 'id':
                var_to_params.setdefault('sid', []).append(i)
                var_to_params.setdefault('rid', []).append(i)
            elif p in ('idx', 'state_idx', 'secs', 'start', 'stop', 'n'):
                var_to_params.setdefault('num', []).append(i)
            elif p in ('"isar text"', '"text"', '"query"', 'path'):
                var_to_params.setdefault('sid', []).append(i)

        active_idx = None
        if active_var and active_var in var_to_params:
            indices = var_to_params[active_var]
            if len(indices) == 1:
                active_idx = indices[0]
            elif match:
                # Count how many times this variable appears up to cursor
                count = sum(1 for mv in match.variables()
                            if mv.varname == active_var and mv.stop <= len(text))
                active_idx = indices[min(count, len(indices) - 1)]

        parts = []
        for i, p in enumerate(params):
            if i == active_idx:
                parts.append(f"<b><u>{p}</u></b>")
            else:
                parts.append(f"<ansigray>{p}</ansigray>")
        return HTML(f" <b>{cmd}</b> {' '.join(parts)}  <i>{desc}</i>")
    return toolbar


def console_loop(server, session):
    """Interactive console for the server operator."""
    cmd_lines = []
    last_interrupt = 0
    while server.running:
        try:
            prompt = HTML("<b><ansicyan>%&gt;</ansicyan></b> ") if not cmd_lines \
                else HTML("<ansigray>.. </ansigray>")
            line = session.prompt(prompt, bottom_toolbar=make_toolbar(session.completer))
            last_interrupt = 0
        except KeyboardInterrupt:
            now = time.time()
            if now - last_interrupt < 2:
                break
            last_interrupt = now
            if cmd_lines:
                cmd_lines = []
                print(f"{YELLOW}Input cancelled.{RST}")
            else:
                print(f"{YELLOW}Press Ctrl+C again to quit.{RST}")
            continue
        except EOFError:
            break

        stripped = line.strip()
        if not stripped and not cmd_lines:
            continue

        if stripped.startswith("/") and not cmd_lines:
            cmd = stripped.split()[0].lower()
            if cmd == "/connections":
                infos = server.client_info()
                print(f"{DIM}Listening on 127.0.0.1:{server.port}{RST}")
                if not infos:
                    print(f"{DIM}No open connections.{RST}")
                else:
                    now = time.time()
                    print(f"{BOLD}{len(infos)} open connection(s):{RST}")
                    for i, c in enumerate(infos):
                        age = int(now - c["started"])
                        idle = int(now - c["last_active"])
                        print(f"  {CYAN}{i}: {c['peer']}{RST}  "
                              f"age={age}s  "
                              f"idle={idle}s  "
                              f"cmds={c['commands']}  "
                              f"in={c['bytes_in']}B out={c['bytes_out']}B")
            elif cmd == "/quit":
                break
            elif cmd == "/log":
                server.verbose = not server.verbose
                state = f"{GREEN}ON{RST}" if server.verbose else f"{RED}OFF{RST}"
                print(f"Verbose logging {state}")
            elif cmd == "/help":
                print(f"{BOLD}Management commands:{RST}")
                log_state = f"{GREEN}ON{RST}" if server.verbose else f"{RED}OFF{RST}"
                print(f"  {YELLOW}/connections{RST}   Show open client connections")
                print(f"  {YELLOW}/log{RST}           Toggle verbose logging (currently {log_state})")
                print(f"  {YELLOW}/quit{RST}          Shut down the server")
                print(f"  {YELLOW}/help{RST}          This help")
                print("Anything else is sent to the REPL.")
            else:
                print(f"{RED}Unknown command: {cmd}{RST} (try /help)")
        else:
            cmd_lines.append(line)
            if not line.rstrip().endswith(";"):
                continue
            command = " ".join(cmd_lines).strip()
            cmd_lines = []
            with server.lock:
                if not server.poly.alive():
                    print(f"{RED}ERR: Poly/ML process terminated{RST}")
                    break
                output = server.poly.send(command)
            print(output)
            # Update completer from command output
            if command.startswith("Ir.theories"):
                session.completer.learn_theories(output)
            elif command.startswith("Ir.load_theory"):
                # After loading, refresh the theory list
                refresh = server.poly.send("Ir.theories ();")
                session.completer.learn_theories(refresh)
            elif command.startswith("Ir.repls"):
                session.completer.learn_repls(output)
            elif command.startswith("Ir.source"):
                m = re.match(r'Ir\.source\s+"([^"]+)"', command)
                if m:
                    session.completer.learn_source(m.group(1), output)


def main():
    p = argparse.ArgumentParser(description="I/R REPL TCP server")
    p.add_argument("--port", type=int, default=9147)
    p.add_argument("--isabelle", default=os.path.expanduser(
        "~/Isabelle2025-2-experimental.app/bin/isabelle"))
    p.add_argument("--session", default="AutoCorrode")
    p.add_argument("--dir", default=None)
    p.add_argument("-v", "--verbose", action="store_true",
                   help="Print the Isabelle/Poly/ML command being invoked")
    p.add_argument("--check-heap", action="store_true",
                   help="Check and rebuild session heap if needed (default: load as-is)")
    p.add_argument("--no-bash-server", action="store_true",
                   help="Skip Bash.Server startup (disables sledgehammer)")
    p.add_argument("--server-only", action="store_true",
                   help="Expose TCP server only; do not start a REPL on stdin")
    p.add_argument("--host", default="127.0.0.1",
                   help="Host address to bind the TCP server on (default: 127.0.0.1)")
    p.add_argument("--mcp", action="store_true",
                   help="Start mcp_server.py in the background (streamable-http by default)")
    p.add_argument("--mcp-options", default="--transport streamable-http",
                   help="Options for mcp_server.py (default: '--transport streamable-http')")
    args = p.parse_args()

    ml_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "ir.ML")

    global UNICODE_TO_ASCII
    UNICODE_TO_ASCII = _load_symbols(args.isabelle)

    bash_server = None
    if not args.no_bash_server:
        print(f"{BOLD}Starting Bash.Server...{RST}", flush=True)
        bash_server = BashServer(args.isabelle)
        print(f"{GREEN}● Bash.Server ready at {bash_server.address}{RST}", flush=True)
    else:
        print(f"{DIM}Bash.Server skipped (sledgehammer unavailable){RST}", flush=True)

    def _signal_cleanup(signum, frame):
        if bash_server:
            bash_server.close()
        sys.exit(128 + signum)
    signal.signal(signal.SIGTERM, _signal_cleanup)
    signal.signal(signal.SIGHUP, _signal_cleanup)

    print(f"{BOLD}Starting Isabelle console (session={args.session})...{RST}", flush=True)
    poly = PolyMLProcess(args.isabelle, args.session, args.dir,
                         bash_server=bash_server, verbose=args.verbose,
                         no_build=not args.check_heap)
    print(f"{GREEN}● Isabelle console ready.{RST}", flush=True)

    print(f"Loading {BOLD}{ml_path}{RST}...", flush=True)
    ml_code = open(ml_path).read().replace('\n', ' ')
    out = poly.send(ml_code)
    if "Exception" in out or "ML error" in out:
        print(f"{RED}Failed to load {ml_path}:{RST}\n{out}", file=sys.stderr)
        poly.close()
        sys.exit(1)
    # Verify the structure is actually available
    probe = poly.send('Ir.help ();')
    if "Ir.init" not in probe:
        print(f"{RED}Ir structure not available after load.{RST}", file=sys.stderr)
        print(f"{DIM}Load output:{RST}\n{out}", file=sys.stderr)
        print(f"{DIM}Probe output:{RST}\n{probe}", file=sys.stderr)
        poly.close()
        sys.exit(1)

    server = Server(poly, args.port, host=args.host)
    accept_thread = threading.Thread(target=server.serve_forever, daemon=True)
    accept_thread.start()

    print(f"{GREEN}● REPL ready.{RST} Waiting for connections on "
          f"{BOLD}{args.host}:{args.port}{RST}", flush=True)

    mcp_proc = None
    if args.mcp:
        print(f"{BOLD}Starting MCP server...{RST}", flush=True)
        mcp_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "mcp_server.py")
        mcp_cmd = [sys.executable, mcp_path] + shlex.split(args.mcp_options)
        mcp_proc = subprocess.Popen(mcp_cmd, stdin=subprocess.DEVNULL,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, start_new_session=True)

        def _mcp_log_reader():
            started = False
            for raw in mcp_proc.stdout:
                line = raw.decode("utf-8", errors="replace").rstrip()
                if line:
                    if "No module named" in line:
                        req_path = os.path.join(os.path.dirname(mcp_path), "requirements.txt")
                        print(f"{RED}[MCP] {line}{RST}")
                        print(f"{YELLOW}⚠️  MCP server failed to start. "
                              f"Install dependencies: "
                              f"pip install -r {req_path}{RST}")
                        print(f"{DIM}   REPL is still available on "
                              f"{args.host}:{args.port}{RST}")
                    elif not started and "running on" in line.lower():
                        started = True
                        print(f"{DIM}[MCP]{RST} {line}")
                        print(f"{GREEN}● MCP server started{RST}")
                    else:
                        if line.startswith("ERROR:"):
                            print(f"{RED}[MCP] {line}{RST}")
                        else:
                            print(f"{DIM}[MCP]{RST} {line}")
            rc = mcp_proc.wait()
            if rc != 0:
                print(f"{RED}⚠️  MCP server exited (rc={rc}){RST}")
                print(f"{DIM}   REPL is still available on "
                      f"{args.host}:{args.port}{RST}")

        threading.Thread(target=_mcp_log_reader, daemon=True).start()

    if args.server_only:
        print(f"{DIM}Running in server-only mode (no stdin REPL). "
              f"Send SIGTERM or SIGINT to stop.{RST}", flush=True)
        try:
            accept_thread.join()
        except KeyboardInterrupt:
            pass
    elif not _HAVE_PROMPT_TOOLKIT or not sys.stdin.isatty():
        if not _HAVE_PROMPT_TOOLKIT:
            req_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "requirements.txt")
            print(f"{YELLOW}⚠️  prompt_toolkit is not installed. "
                  f"Install dependencies for the full experience: "
                  f"pip install -r {req_path}{RST}", flush=True)
        print(f"{DIM}Running in server-only mode. "
              f"Connect on {args.host}:{args.port}, "
              f"e.g. nc {args.host} {args.port}{RST}", flush=True)
        try:
            accept_thread.join()
        except KeyboardInterrupt:
            pass
    else:
        histfile = os.path.expanduser("~/.ir_repl_history")
        completer = IrCompleter()
        # Seed completer with loaded theories
        with server.lock:
            completer.learn_theories(server.poly.send("Ir.theories ();"))
        session = PromptSession(history=FileHistory(histfile), completer=completer,
                                complete_while_typing=Always())
        try:
            with patch_stdout(raw=True):
                console_loop(server, session)
        except KeyboardInterrupt:
            pass

    print("Shutting down...", flush=True)
    if mcp_proc and mcp_proc.poll() is None:
        os.killpg(mcp_proc.pid, signal.SIGTERM)
        try:
            mcp_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(mcp_proc.pid, signal.SIGKILL)
    server.shutdown()
    poly.close()
    if bash_server:
        bash_server.close()


if __name__ == "__main__":
    main()
