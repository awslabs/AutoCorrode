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

Authentication: TCP clients must send the server token as the
first line after connecting; the server responds with "OK\\n" or
"ERR: authentication failed\\n".

Note: The I/R REPL operates at the Isar level. A session (created
via Ir.init) starts in the context of a named theory — there is
no need to issue 'theory' commands. Steps are Isar commands such as
lemma, definition, fun, apply, by, etc.

The server operator gets a management console on stdin/stdout:
  - Lines starting with / are management commands
  - Everything else is sent to the REPL directly

Management commands:
  /connections   Show open client connections with stats
  /info          Show server status summary
  /verbosity N   Set verbosity 0-3 (0=off, 1=non-empty, 2=all, 3=hex)
  /show_types    Toggle type annotations in output
  /quit          Shut down the server
  /help          Show available commands

Environment variables:
  IR_AUTH_TOKEN        Override the TCP server token (default: random)
  IR_REPL_AUTH_TOKEN   ML_Repl token (for --expect-ml mode)

Usage:
    python3 repl.py [--port PORT] [--isabelle PATH] [--session SESSION]
                    [--dir DIR]
    python3 repl.py --daemon [...]   Start in daemon mode (mgmt console on Unix socket)
    python3 repl.py --attach         Connect to a running daemon's mgmt console
"""

import argparse
import os
import re
import select
import shlex
import signal
import hmac
import secrets
import socket
import subprocess
import sys
import threading

# Ensure stdout/stderr are unbuffered so parent processes reading our
# output via pipes see lines immediately.
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(line_buffering=True)
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(line_buffering=True)
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
    'Ir.init_from_document': 'id "node" cmd_id  — create REPL from PIDE document state',
    'Ir.fork':           'id new_id state_idx  — fork sub-REPL from id at state (~1=latest)',
    'Ir.step':           'id "isar text"  — execute Isar text as next step',
    'Ir.show':           'id  — show REPL: origin, steps, staleness',
    'Ir.state':          'id idx  — show proof state at step idx (0=base, ~1=latest)',
    'Ir.text':           'id  — print concatenated Isar text',
    'Ir.edit':           'id idx "text"  — replace step idx, mark later steps stale',
    'Ir.replay':         'id  — re-execute all stale steps',
    'Ir.truncate':       'id idx  — keep steps 0..idx, discard the rest',
    'Ir.merge':          'id  — inline sub-REPL back into its parent',
    'Ir.remove':         'id  — delete REPL and all its sub-REPLs',
    'Ir.repls':          '()  — list all REPLs with step counts and origins',
    'Ir.theories':       '()  — list all theories loaded in the session',
    'Ir.load_theory':    'name  — load theory by name, e.g. "HOL-Library.Multiset"',
    'Ir.source':         'thy start stop  — list theory commands (start/stop 0-based, ~N from end)',
    'Ir.source_map':     'thy start stop  — segment-to-position map (start/stop 0-based, ~N from end)',
    'Ir.sledgehammer':   'id secs  — run sledgehammer on proof state with timeout',
    'Ir.timeout':        'secs  — set step timeout (0=unlimited, default 5s)',
    'Ir.find_theorems':  'id n "query"  — search theorems (n=max results, 0=unlimited)',
    'Ir.back':           'id  — revert last step (synonym for truncate ~1)',
    'Ir.config':         'f  — update config (color, show_ignored, full_spans, auto_replay)',
    'Ir.help':           '()  — show full help text',
    '/sources':               'list source files from heap DB with verification status',
    '/timings':               '[--top N] [--theory "NAME"]  — command timing hotspots',
    '/source-map':            '"THEORY"  — segment-to-line mapping with timing',
    '/resolve':               '"THEORY" LINE  — find theory:segment for a location',
    '/connections':           'show open client connections',
    '/verbosity':             'set verbosity 0-3 (0=off, 1=non-empty, 2=all, 3=hex)',
    '/show_types':            'toggle display of type annotations',
    '/info':                  'show server status summary',
    '/quit':                  'shut down the server',
    '/help':                  'show available commands',
}

# Structured signatures: (params_list, description)
IR_SIGS = {
    'Ir.init':          (['id', '["thy"]'], 'create REPL "id" importing theories'),
    'Ir.init_from_document': (['id', 'node', 'cmd_id'], 'create REPL from PIDE document state'),
    'Ir.fork':          (['id', 'new_id', 'state_idx'], 'fork sub-REPL from id at state (~1=latest)'),
    'Ir.step':          (['id', '"isar text"'], 'execute Isar text as next step'),
    'Ir.show':          (['id'], 'show REPL: origin, steps, staleness'),
    'Ir.state':         (['id', 'idx'], 'show proof state at step idx (0=base, ~1=latest)'),
    'Ir.text':          (['id'], 'print concatenated Isar text'),
    'Ir.edit':          (['id', 'idx', '"text"'], 'replace step idx, mark later steps stale'),
    'Ir.replay':        (['id'], 're-execute all stale steps'),
    'Ir.truncate':      (['id', 'idx'], 'keep steps 0..idx, discard the rest'),
    'Ir.merge':         (['id'], 'inline sub-REPL back into its parent'),
    'Ir.remove':        (['id'], 'delete REPL and all its sub-REPLs'),
    'Ir.repls':         ([], 'list all REPLs with step counts and origins'),
    'Ir.theories':      ([], 'list all theories loaded in the session'),
    'Ir.load_theory':   (['name'], 'load theory by name, e.g. "HOL-Library.Multiset"'),
    'Ir.source':        (['thy', 'start', 'stop'], 'list theory commands (start/stop 0-based, ~N from end)'),
    'Ir.source_map':    (['thy', 'start', 'stop'], 'segment-to-position map (start/stop 0-based, ~N from end)'),
    'Ir.sledgehammer':  (['id', 'secs'], 'run sledgehammer on proof state with timeout'),
    'Ir.timeout':       (['secs'], 'set step timeout (0=unlimited, default 5s)'),
    'Ir.find_theorems': (['id', 'n', '"query"'], 'search theorems (n=max results, 0=unlimited)'),
    'Ir.back':          (['id'], 'revert last step (synonym for truncate ~1)'),
    'Ir.config':        (['f'], 'update config (color, show_ignored, full_spans, auto_replay)'),
    'Ir.help':          ([], 'show full help text'),
    '/sources':         ([], 'list source files from heap DB with verification status'),
    '/timings':         (['--top N', '--theory "NAME"'], 'command timing hotspots'),
    '/source-map':      (['"THEORY"'], 'segment-to-line mapping with timing'),
    '/resolve':         (['"THEORY"', 'LINE'], 'find theory:segment for location'),
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

        # Grammar for all Ir.* commands and /-commands.
        # The prompt_toolkit grammar compiler ignores whitespace and supports
        # (?P<name>...) for named variables that get their own completer.
        # Variable 'thy' uses quote escape/unescape for ML-style "Theory" args.
        # Variable 'uthy' is unquoted, for /-commands that take plain theory/file args.
        g = grammar_compile(
            r"""
                (
                    # init_from_document must come before init (longer prefix)
                    (?P<cmd>Ir\.init_from_document) \s+ (?P<rid>"[^"]*") \s+ (?P<sid>"[^"]*") \s+ (?P<num>[^\s]+)
                |
                    # init: id then theory list
                    (?P<cmd>Ir\.init) \s+ (?P<rid>"[^"]*") \s+
                        \[ \s* (?P<thy>"[^"]*") \s*
                           (, \s* (?P<thy>"[^"]*") \s* )*
                        \]?
                |
                    (?P<cmd>Ir\.load_theory) \s+ (?P<thy>"[^"]*")
                |
                    (?P<cmd>Ir\.source_map) \s+ (?P<thy>"[^"]*") \s+ (?P<num>[^\s]+) \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>Ir\.source) \s+ (?P<thy>"[^"]*") \s+ (?P<num>[^\s]+) \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>Ir\.remove) \s+ (?P<rid>"[^"]*")
                |
                    # fork: id new_id state_idx
                    (?P<cmd>Ir\.fork) \s+ (?P<rid>"[^"]*") \s+ (?P<sid>"[^"]*") \s+ (?P<num>[^\s]+)
                |
                    # step: id "isar text"
                    (?P<cmd>Ir\.step) \s+ (?P<rid>"[^"]*") \s+ (?P<sid>"[^"]*")
                |
                    # edit: id idx "text"
                    (?P<cmd>Ir\.edit) \s+ (?P<rid>"[^"]*") \s+ (?P<num>[^\s]+) \s+ (?P<sid>"[^"]*")
                |
                    # state: id idx
                    (?P<cmd>Ir\.state) \s+ (?P<rid>"[^"]*") \s+ (?P<num>[^\s]+)
                |
                    # truncate: id idx
                    (?P<cmd>Ir\.truncate) \s+ (?P<rid>"[^"]*") \s+ (?P<num>[^\s]+)
                |
                    # sledgehammer: id secs
                    (?P<cmd>Ir\.sledgehammer) \s+ (?P<rid>"[^"]*") \s+ (?P<num>[^\s]+)
                |
                    # find_theorems: id n "query"
                    (?P<cmd>Ir\.find_theorems) \s+ (?P<rid>"[^"]*") \s+ (?P<num>[^\s]+) \s+ (?P<sid>"[^"]*")
                |
                    # Commands taking just a REPL id: show, text, replay, merge, back
                    (?P<cmd>Ir\.show)    \s+ (?P<rid>"[^"]*")
                |
                    (?P<cmd>Ir\.text)    \s+ (?P<rid>"[^"]*")
                |
                    (?P<cmd>Ir\.replay)  \s+ (?P<rid>"[^"]*")
                |
                    (?P<cmd>Ir\.merge)   \s+ (?P<rid>"[^"]*")
                |
                    (?P<cmd>Ir\.back)    \s+ (?P<rid>"[^"]*")
                |
                    (?P<cmd>Ir\.timeout) \s+ (?P<num>[^\s]+)
                |
                    # /-commands with quoted arguments
                    (?P<cmd>/source-map) \s+ (?P<thy>"[^"]*")
                |
                    (?P<cmd>/resolve) \s+ (?P<thy>"[^"]*") \s+ (?P<num>[^\s]+)
                |
                    # /timings with various flag combinations
                    (?P<cmd>/timings) \s+ --top \s+ (?P<num>[^\s]+) \s+ --theory \s+ (?P<thy>"[^"]*")
                |
                    (?P<cmd>/timings) \s+ --top \s+ (?P<num>[^\s]+)
                |
                    (?P<cmd>/timings) \s+ --theory \s+ (?P<thy>"[^"]*")
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
REPL_DEFAULT_PORT = 9147
ML_REPL_DEFAULT_PORT = 9146


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
                sym = parts[0]
                cp = int(parts[2], 16)
                unicode_to_ascii[chr(cp)] = sym
    return unicode_to_ascii


UNICODE_TO_ASCII = {}
ASCII_TO_UNICODE = {}


def unicode_to_isabelle(text):
    """Replace unicode characters with Isabelle ASCII encoding."""
    return "".join(UNICODE_TO_ASCII.get(c, c) for c in text)


def isabelle_to_unicode(text):
    """Replace Isabelle symbol encoding (\\<forall> etc.) with UTF-8."""
    if "\\" not in text:
        return text
    import re
    return re.sub(r'(?<!\\)\\<[a-zA-Z_]+>', lambda m: ASCII_TO_UNICODE.get(m.group(), m.group()), text)


# YXML elements whose content should be suppressed (invisible in jEdit)
# Mutable: toggled via /show_types command
yxml_suppress = {"typing"}


def walk_yxml(text, on_open, on_close, on_text):
    """Walk YXML tree, calling callbacks for open/close tags and text spans."""
    X = "\x05"
    i = 0
    n = len(text)
    while i < n:
        j = text.find(X, i)
        if j < 0:
            on_text(text[i:])
            break
        if j > i:
            on_text(text[i:j])
        if j + 1 < n and text[j + 1] == "\x06":
            k = text.index(X, j + 2)
            tag_content = text[j + 2:k]
            i = k + 1
            if tag_content == "":
                on_close()
            else:
                parts = tag_content.split("\x06")
                name = parts[0]
                props = dict(p.split("=", 1) for p in parts[1:] if "=" in p)
                on_open(name, props)
        else:
            on_text(X)
            i = j + 1


def strip_yxml(text):
    """Parse YXML and extract plain text content, discarding all markup.
    Suppresses content inside xml_body of xml_elem xml_name=typing blocks."""
    result = []
    suppress = 0
    in_typing_elem = 0
    def on_open(name, props):
        nonlocal suppress, in_typing_elem
        if suppress > 0:
            suppress += 1
        elif name == "xml_elem" and props.get("xml_name") in yxml_suppress:
            in_typing_elem += 1
        elif name == "xml_body" and in_typing_elem > 0:
            suppress += 1
    def on_close():
        nonlocal suppress, in_typing_elem
        if suppress > 0:
            suppress -= 1
        elif in_typing_elem > 0:
            in_typing_elem -= 1
    def on_text(s):
        if suppress == 0:
            result.append(s)
    walk_yxml(text, on_open, on_close, on_text)
    return "".join(result)


# YXML markup name -> ANSI color mapping (matching Isabelle/jEdit defaults)
_MARKUP_ANSI = {
    "keyword1": "\033[1;34m",   # bold blue
    "keyword2": "\033[34m",     # blue
    "keyword3": "\033[34m",     # blue
    "string": "\033[32m",       # green
    "alt_string": "\033[32m",   # green
    "cartouche": "\033[32m",    # green
    "var": "\033[33m",          # yellow
    "tfree": "\033[33m",        # yellow
    "tvar": "\033[33m",         # yellow
    "free": "\033[34m",         # blue
    "bound": "\033[32m",        # green
    "comment": "\033[90m",      # gray
    "improper": "\033[35m",     # magenta
    "delimiter": "",            # no color
    "error": "\033[31m",        # red
    "writeln": "",              # no color (content channel)
    "state": "",                # no color (content channel)
    "warning": "\033[33m",      # yellow
    "legacy": "\033[33m",       # yellow
    "information": "\033[36m",  # cyan
    "tracing": "\033[90m",      # gray
}


def yxml_to_ansi(text):
    """Parse YXML control chars and convert markup to ANSI colors.
    Suppresses content inside xml_body of xml_elem xml_name=typing blocks."""
    RST = "\033[0m"
    result = []
    color_stack = []
    suppress = 0
    in_typing_elem = 0
    def on_open(name, props):
        nonlocal suppress, in_typing_elem
        if suppress > 0:
            suppress += 1
            return
        if name == "xml_elem" and props.get("xml_name") in yxml_suppress:
            in_typing_elem += 1
            return
        if name == "xml_body" and in_typing_elem > 0:
            suppress += 1
            return
        ansi = _MARKUP_ANSI.get(name, "")
        color_stack.append(ansi)
        if ansi:
            result.append(ansi)
    def on_close():
        nonlocal suppress, in_typing_elem
        if suppress > 0:
            suppress -= 1
            return
        if in_typing_elem > 0:
            in_typing_elem -= 1
            return
        if color_stack:
            color_stack.pop()
        result.append(RST)
        if color_stack:
            result.append(color_stack[-1])
    def on_text(s):
        if suppress == 0:
            result.append(s)
    walk_yxml(text, on_open, on_close, on_text)
    return "".join(result)

# ---------------------------------------------------------------------------
# Output transformer pipelines
# ---------------------------------------------------------------------------
# Each channel (console, TCP, MCP) has a list of str -> str transformers
# applied in order to every response from the ML process.

def apply_transforms(transforms, text):
    for t in transforms:
        text = t(text)
    return text

# Default pipelines (can be reconfigured at runtime)
console_transforms = [isabelle_to_unicode, yxml_to_ansi]
tcp_transforms = [isabelle_to_unicode, strip_yxml]
mcp_transforms = [isabelle_to_unicode, strip_yxml]

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

    def __init__(self, isabelle, quiet=False):
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
        if quiet:
            done = None; t = None
        else:
            done = threading.Event()
            t = threading.Thread(target=spinner, args=("Starting Bash.Server...", done), daemon=True)
            t.start()
        while True:
            line = self.proc.stdout.readline().decode().strip()
            if not line and self.proc.poll() is not None:
                if done: done.set(); t.join()
                err = self.proc.stderr.read().decode()
                raise RuntimeError(f"Bash.Server failed to start: {err}")
            if line.startswith("BASH_SERVER_ADDRESS="):
                self.address = line.split("=", 1)[1]
            elif line.startswith("BASH_SERVER_PASSWORD="):
                self.password = line.split("=", 1)[1]
            if self.address and self.password:
                break
        if done: done.set(); t.join()

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
    """Manages a Poly/ML process running ML_Repl via isabelle ML_process."""

    def __init__(self, isabelle, session, directory, ml_dir, port,
                 bash_server=None, no_build=False, redirect=True):
        self.requested_port = port
        self.port = port  # updated to actual port after start
        self.cmd = self._build_cmd(isabelle, session, directory, ml_dir, port,
                                   bash_server=bash_server, redirect=redirect)
        self.startup_output = []
        self.proc = subprocess.Popen(
            self.cmd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=0,
            start_new_session=True,
        )

    def read_actual_port(self, timeout=60):
        """Read stdout until Tcp_Handler reports its port and token.
        Updates self.port and self.token.  Non-matching lines are
        accumulated in self.startup_output for diagnostics."""
        import re
        self.token = None
        self.max_connections = None
        self.startup_output = []
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline and self.alive():
            line = self.proc.stdout.readline().decode("utf-8", errors="replace")
            if not line:
                break
            self.startup_output.append(line.rstrip("\n"))
            m = re.search(
                r'Tcp_Handler: listening on 127\.0\.0\.1:(\d+)'
                r'(?: \(token "([^"]*)")?'
                r'(?:, max (\d+) connections)?', line)
            if m:
                self.port = int(m.group(1))
                self.token = m.group(2)
                if m.group(3):
                    self.max_connections = int(m.group(3))
                return self.port
        return None

    @staticmethod
    def _build_cmd(isabelle, session, directory, ml_dir, port,
                   bash_server=None, redirect=False):
        cmd = [isabelle, "ML_process"]
        if directory:
            cmd += ["-d", directory]
        cmd += ["-l", session]
        if bash_server:
            cmd += ["-o", f"bash_process_address={bash_server.address}",
                    "-o", f"bash_process_password={bash_server.password}"]
        if redirect:
            cmd.append("-r")
        # Forward ISABELLE_REMOTE options (e.g. process_policy for I/P remote execution)
        isabelle_remote = os.environ.get("ISABELLE_REMOTE", "")
        if isabelle_remote:
            cmd += shlex.split(isabelle_remote)
        # Load order: tcp_handler, ir, ml_repl (ml_repl wires them together)
        cmd += ["-f", os.path.join(ml_dir, "tcp_handler.ML"),
                "-f", os.path.join(ml_dir, "ir.ML"),
                "-f", os.path.join(ml_dir, "ml_repl.ML"),
                "-e", f"case ML_Repl.start {port} of SOME (_, f) => Future.join f | NONE => ();"]
        return cmd

    def alive(self):
        return self.proc.poll() is None

    def close(self):
        # Step 1: Ask ML_Repl to stop gracefully via TCP
        if self.port:
            try:
                s = socket.create_connection(("127.0.0.1", self.port), timeout=2)
                if self.token:
                    s.sendall((self.token + "\n").encode())
                s.sendall(b"ML_Repl.stop ();\n")
                s.close()
            except Exception:
                pass
            try:
                self.proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
        # Step 2: SIGTERM to process group (catchable — lets ml_proxy cleanup run)
        if self.proc.poll() is None:
            try:
                os.killpg(self.proc.pid, signal.SIGTERM)
            except OSError:
                self.proc.terminate()
            try:
                self.proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                print("WARNING: Poly/ML process did not exit after SIGTERM",
                      flush=True)


class PolyMLConnection:
    """TCP connection to ML_Repl running inside Poly/ML.

    Speaks the PIDE message framing protocol: each message is a
    length-prefixed list of YXML-encoded chunks, matching the format
    produced by Byte_Message.write_message_yxml on the ML side.

    Messages are structured as:
      chunk 0: kind (e.g. "writeln", "error", "done")
      chunk 1: number of property chunks (as string)
      chunks 2..2+n: properties (e.g. "serial=42")
      remaining chunks: YXML-encoded body

    The "done" message signals end of output for a command.
    """

    def __init__(self, host="127.0.0.1", port=9146, token=None):
        self.host = host
        self.port = port
        self.token = token
        self.sock = None
        self._buf = b""

    def connect(self, timeout=None):
        self.sock = socket.create_connection((self.host, self.port),
                                             timeout=timeout)
        self.sock.settimeout(None)  # back to blocking for subsequent I/O
        self._buf = b""
        if self.token:
            self.sock.sendall((self.token + "\n").encode())

    def _read_exact(self, n):
        """Read exactly n bytes from socket, using internal buffer."""
        while len(self._buf) < n:
            chunk = self.sock.recv(max(4096, n - len(self._buf)))
            if not chunk:
                self.sock = None
                raise EOFError("ML_Repl connection closed")
            self._buf += chunk
        result = self._buf[:n]
        self._buf = self._buf[n:]
        return result

    def _read_line(self):
        """Read until newline, return bytes without newline."""
        while b"\n" not in self._buf:
            chunk = self.sock.recv(4096)
            if not chunk:
                self.sock = None
                raise EOFError("ML_Repl connection closed")
            self._buf += chunk
        line, self._buf = self._buf.split(b"\n", 1)
        return line

    def read_message(self):
        """Read one PIDE-framed message. Returns (kind, props, body_chunks).

        kind: str, e.g. "writeln", "error", "done"
        props: list of (key, value) tuples
        body_chunks: list of bytes (raw YXML)
        """
        header = self._read_line().decode("ascii")
        sizes = [int(x) for x in header.split(",")]
        chunks = [self._read_exact(n) for n in sizes]
        kind = chunks[0].decode("utf-8")
        props_length = int(chunks[1].decode("utf-8")) if len(chunks) > 1 else 0
        props = []
        for i in range(props_length):
            raw = chunks[2 + i].decode("utf-8")
            if "=" in raw:
                k, v = raw.split("=", 1)
                props.append((k, v))
        body_chunks = chunks[2 + props_length:]
        return kind, props, body_chunks

    def send(self, command):
        """Send an ML command and return the output as a string.

        Reads PIDE-framed messages until a "done" message, concatenates
        the YXML body text of all non-done messages, and returns it.
        """
        line = unicode_to_isabelle(command.strip()) + "\n"
        self.sock.sendall(line.encode("utf-8"))
        parts = []
        while True:
            kind, props, body_chunks = self.read_message()
            if kind == "done":
                return "\n".join(parts).strip()
            body = "".join(c.decode("utf-8", errors="replace")
                           for c in body_chunks)
            if body:
                parts.append(body)

    def send_streaming(self, command, on_message):
        """Send an ML command, call on_message(kind, props, body) for each message.

        on_message receives:
          kind: str (e.g. "writeln", "error", "status", "done")
          props: list of (key, value) tuples
          body: str (decoded YXML body, may be empty)

        Returns (text, had_error) where text is the concatenated body text
        and had_error is True if any PIDE "error" message was received.
        """
        line = unicode_to_isabelle(command.strip()) + "\n"
        self.sock.sendall(line.encode("utf-8"))
        parts = []
        had_error = False
        while True:
            kind, props, body_chunks = self.read_message()
            body = "".join(c.decode("utf-8", errors="replace")
                           for c in body_chunks)
            on_message(kind, props, body)
            if kind == "error":
                had_error = True
            if kind == "done":
                return "\n".join(parts).strip(), had_error
            if body:
                parts.append(body)

    def alive(self):
        return self.sock is not None

    def close(self):
        if self.sock:
            try:
                self.sock.close()
            except OSError:
                pass
            self.sock = None
        self._buf = b""


class MLConnectionPool:
    """Fixed pool of persistent TCP connections to the ML_Repl.

    All connections are established at startup and kept alive for the
    lifetime of repl.py.  One connection is reserved for the management
    console; the remainder are available for client requests.

    acquire() blocks until a pool connection is free, release() returns it.
    drain_and_release() handles abandoned requests: reads until "done" in
    a background thread, then returns the connection to the pool.
    """

    def __init__(self, host, port, token, size=5, connect_timeout=3):
        self.host = host
        self.ml_port = port
        self.token = token
        self._size = size
        self._lock = threading.Lock()
        # Open connections (stop on first failure)
        conns = []
        for i in range(max(2, size)):
            try:
                c = PolyMLConnection(host, port, token)
                c.connect(timeout=connect_timeout)
                conns.append(c)
                print(f"  ML connection {i + 1}/{size} established",
                      flush=True)
            except (OSError, EOFError) as e:
                print(f"  ML connection {i + 1}/{size} failed: {e}",
                      flush=True)
                break
        if not conns:
            raise ConnectionError(
                f"Could not establish any ML connections to {host}:{port}")
        # Last connection is reserved for the console
        self._console = conns.pop()
        self._idle = conns
        self._semaphore = threading.Semaphore(max(1, len(self._idle)))
        print(f"  {len(conns)} pool + 1 console = "
              f"{len(conns) + 1} ML connections", flush=True)

    @property
    def console(self):
        """The reserved console connection (not in the shared pool)."""
        return self._console

    def acquire(self):
        """Block until a pool connection is available, then return it."""
        self._semaphore.acquire()
        with self._lock:
            return self._idle.pop()

    def release(self, conn):
        """Return a connection to the idle pool."""
        with self._lock:
            self._idle.append(conn)
        self._semaphore.release()

    def drain_and_release(self, conn):
        """Background: read until 'done' on a busy connection, then release."""
        def _drain():
            c = conn
            try:
                while True:
                    kind, _, _ = c.read_message()
                    if kind == "done":
                        break
            except Exception:
                c.close()
                c = PolyMLConnection(self.host, self.ml_port, self.token)
                c.connect()
            self.release(c)
        threading.Thread(target=_drain, daemon=True).start()

    def alive(self):
        """Check if the console connection is alive."""
        return self._console is not None and self._console.alive()

    def close_all(self):
        """Close all connections."""
        if self._console:
            self._console.close()
        with self._lock:
            for conn in self._idle:
                conn.close()
            self._idle.clear()


class Server:
    """TCP server that dispatches client commands to a pool of ML connections."""

    def __init__(self, pool, port, host="127.0.0.1", mgmt_output=None,
                 session=None, directory=None, heap_info=None,
                 remote_host=None):
        self.pool = pool
        self.poly = pool.console  # convenience alias for console access
        self.host = host
        self.token = os.environ.get("IR_AUTH_TOKEN", "").strip() or secrets.token_urlsafe(24)
        self.mgmt_output = mgmt_output or print
        self.remote_host = remote_host
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        if port == 0:
            # Try default port first; fall back to OS-assigned.
            try:
                self.sock.bind((host, REPL_DEFAULT_PORT))
            except OSError:
                self.sock.bind((host, 0))
        else:
            self.sock.bind((host, port))
        self.port = self.sock.getsockname()[1]
        self.sock.listen(8)
        self.running = True
        self.verbose = 0  # 0=off, 1=body, 2=body+headers, 3=body+headers+hex
        self.clients = {}
        self.clients_lock = threading.Lock()
        self._start_time = time.time()
        self.session = session
        self.directory = directory
        self.heap_info = heap_info
        self._source_maps = {}  # theory -> {seg_idx: {keyword, line, offset, file}}

    def log(self, msg):
        """Print from background thread — patch_stdout handles redisplay."""
        self.mgmt_output(msg)

    def log_input(self, ctx, command):
        """Log an input command (verbose >= 1)."""
        if self.verbose >= 1:
            self.log(f"{CYAN}{ctx}{RST} {YELLOW}>>>{RST} {command}")

    def log_output(self, ctx, kind, props, raw_body):
        """Log a single PIDE output message.

        Verbosity levels:
          0: nothing
          1: header + decoded body, only for messages with non-empty text content
          2: header + decoded body for ALL messages
          3: header + hex dump + decoded body for ALL messages
        """
        if self.verbose < 1:
            return
        props_str = " ".join(f"{k}={v}" for k, v in props) if props else ""
        tag = f"{kind}" + (f" {props_str}" if props_str else "")
        short_tag = kind
        # At level 1, skip messages with empty text content
        text_content = strip_yxml(raw_body) if raw_body else ""
        if self.verbose == 1 and not text_content.strip():
            return
        # Color the tag by message kind
        _KIND_COLOR = {
            "writeln": GREEN,
            "state": BLUE,
            "warning": YELLOW,
            "legacy": YELLOW,
            "error": RED,
            "status": DIM,
            "report": DIM,
            "tracing": DIM,
            "information": CYAN,
            "system": DIM,
            "done": DIM,
        }
        kc = _KIND_COLOR.get(kind, "")
        display_tag = short_tag if self.verbose == 1 else tag
        colored_tag = f"{kc}[{display_tag}]{RST}"
        if self.verbose >= 3 and raw_body:
            raw = raw_body.encode("utf-8")
            lines = []
            for i in range(0, len(raw), 32):
                chunk = raw[i:i+32]
                hx = " ".join(f"{b:02x}" for b in chunk)
                asc = "".join(chr(b) if 32 <= b < 127 else "." for b in chunk)
                lines.append(f"  {i:04x}  {hx:<96s} {asc}")
            self.log(f"{CYAN}{ctx}{RST} \033[35m<<< {colored_tag} hex ({len(raw)}B):{RST}")
            for hl in lines:
                self.log(f"{CYAN}{ctx}{RST} \033[2;35m{hl}{RST}")
        if raw_body:
            display = apply_transforms(console_transforms, raw_body)
            for ln in display.splitlines():
                self.log(f"{CYAN}{ctx}{RST} {DIM}<<<{RST} {colored_tag} {ln}")
        else:
            self.log(f"{CYAN}{ctx}{RST} {DIM}<<<{RST} {colored_tag}")

    def _build_source_map(self, theory):
        """Build segment->position mapping for a theory via Ir.source_map.
        Returns {seg_idx: {keyword, line, offset, file}} or None."""
        if theory in self._source_maps:
            return self._source_maps[theory]
        conn = self.pool.acquire()
        try:
            raw = conn.send(f'Ir.source_map "{theory}" 0 ~1;')
        finally:
            self.pool.release(conn)
        result = {}
        for line in strip_yxml(raw).splitlines():
            # Format: idx(5)  keyword(20)  line(6)  offset(6)  file
            m = re.match(r'\s*(\d+)\s+(\S+)\s+(\d+)\s+(\d+)\s+(\S+)', line)
            if m:
                try:
                    result[int(m.group(1))] = {
                        "keyword": m.group(2),
                        "line": int(m.group(3)),
                        "offset": int(m.group(4)),
                        "file": m.group(5).strip(),
                    }
                except ValueError:
                    continue
        if result:
            self._source_maps[theory] = result
        return result if result else None

    # Regex patterns for /-command argument parsing.
    # All string arguments use mandatory "..." quoting.
    _RE_QUOTED = r'"([^"]*)"'
    _RE_SOURCE_MAP = None   # compiled lazily
    _RE_RESOLVE = None
    _RE_READ = None
    _RE_TIMINGS_TOP = None
    _RE_TIMINGS_THEORY = None

    @staticmethod
    def _parse_slash(text, pattern, usage):
        """Match a /-command against a regex. Returns the match or an error string."""
        m = re.match(pattern, text.strip())
        if not m:
            # Give a specific hint if the user forgot quotes or added semicolons
            hint = ""
            if ";" in text:
                hint = "\n  (/-commands don't use trailing semicolons)"
            elif '"' not in text and pattern.find('"') >= 0:
                hint = "\n  (string arguments require double quotes)"
            return None, f"Usage: {usage}{hint}"
        return m, None

    def _handle_local_command(self, text, ansi=False):
        """Handle a /-prefixed command locally. Returns response string or None.
        ansi=True for the management console (YXML→ANSI), False for TCP (YXML→plain)."""
        stripped = text.strip()
        cmd = stripped.split()[0].lower() if stripped else ""

        if cmd == "/info":
            return self.info_text(ansi=ansi)
        if cmd == "/sources":
            return self._cmd_sources(stripped, ansi=ansi)
        if cmd == "/timings":
            return self._cmd_timings(stripped)
        if cmd == "/source-map":
            return self._cmd_source_map(stripped, ansi=ansi)
        if cmd == "/resolve":
            return self._cmd_resolve(stripped)
        return None  # not a local command

    def _cmd_sources(self, text, ansi=False):
        if not self.heap_info:
            return "No heap DB available"
        sources = self.heap_info.source_files()
        verified = sum(1 for s in sources if s["status"] == "verified")
        changed = sum(1 for s in sources if s["status"] == "changed")
        missing = sum(1 for s in sources if s["status"] == "missing")
        unresolved = sum(1 for s in sources if s["status"] == "unresolved")

        B = BOLD if ansi else ""
        D = DIM if ansi else ""
        G = GREEN if ansi else ""
        R = RED if ansi else ""
        C = CYAN if ansi else ""
        X = RST if ansi else ""

        # Header: DB path
        lines = [f"{D}Source: {self.heap_info.db_path}{X}"]

        # Resolved env vars
        env_vars = self.heap_info.resolved_env_vars()
        if env_vars:
            lines.append("")
            for var, val in sorted(env_vars.items()):
                lines.append(f"  {C}${var}{X} = {val}")

        # Summary
        lines.append("")
        parts = []
        if verified:
            parts.append(f"{G}{verified} ✓ (up to date){X}")
        if changed:
            parts.append(f"{R}{changed} ✗ (out of sync){X}")
        if missing:
            parts.append(f"{R}{missing} ✗ (not present){X}")
        if unresolved:
            parts.append(f"{D}{unresolved} ? (unresolved){X}")
        lines.append(f"{B}{len(sources)}{X} files: {', '.join(parts)}")

        # Group by directory, sort by directory
        by_dir = {}
        # Find common prefix to strip from display
        common_prefix = ""
        for var in sorted(env_vars):
            common_prefix = f"${var}/"
            break  # use first (typically only) env var
        for s in sources:
            name = s["name"]
            slash = name.rfind("/")
            if slash >= 0:
                d, f = name[:slash], name[slash + 1:]
            else:
                d, f = "", name
            by_dir.setdefault(d, []).append((f, s["status"]))

        # Compute column widths
        max_dir = 0
        max_file = 0
        for d, files in by_dir.items():
            display_d = d.replace(common_prefix, "", 1) if common_prefix else d
            max_dir = max(max_dir, len(display_d))
            for fname, _ in files:
                max_file = max(max_file, len(fname))
        dir_w = min(max_dir, 45)
        file_w = min(max_file, 50)

        # Table header
        lines.append("")
        lines.append(f"  {B}{'Directory':{dir_w}s}{X}  {B}{'File':{file_w}s}{X}")
        lines.append(f"  {'─' * dir_w}  {'─' * file_w}  ──")

        # Table rows — directory shown only on first row of each group
        for d in sorted(by_dir):
            display_d = d.replace(common_prefix, "", 1) if common_prefix else d
            first = True
            for fname, status in sorted(by_dir[d]):
                if status == "verified":
                    icon = f"{G}✓{X}"
                elif status == "changed":
                    icon = f"{R}✗{X}"
                elif status == "missing":
                    icon = f"{R}!{X}"
                else:
                    icon = f"{D}?{X}"
                dir_col = f"{D}{display_d:{dir_w}s}{X}" if first else " " * dir_w
                lines.append(f"  {dir_col}  {fname:{file_w}s}  {icon}")
                first = False
        return "\n".join(lines)

    def _cmd_timings(self, text):
        if not self.heap_info:
            return "No heap DB available"
        top_n = 20
        file_filter = None
        m = re.search(r'--top\s+(\d+)', text)
        if m:
            top_n = int(m.group(1))
        m = re.search(r'--theory\s+"([^"]*)"', text)
        if m:
            file_filter = m.group(1)
        return self.heap_info.timing_hotspots(
            top_n=top_n, file_filter=file_filter)

    def _cmd_source_map(self, text, ansi=False):
        m, err = self._parse_slash(
            text, r'/source-map\s+"([^"]*)"$',
            '/source-map "THEORY"')
        if err:
            return err
        theory = m.group(1)

        # Get position map (segment idx -> line, offset, file)
        seg_map = self._build_source_map(theory)
        if not seg_map:
            return (f"No source map for {theory} "
                    "(rebuild with record_theories=true?)")

        # Get the rich Ir.source output (YXML markup)
        conn = self.pool.acquire()
        try:
            raw_source = conn.send(f'Ir.source "{theory}" 0 ~1;')
        finally:
            self.pool.release(conn)

        # Get timing data
        timing_by_offset = {}
        if self.heap_info:
            timing_by_offset = self.heap_info.timing_by_offset()

        # Transform pipeline: YXML → ANSI (console) or plain text (TCP)
        transforms = console_transforms if ansi else tcp_transforms

        # Merge: transform each Ir.source line, prepend line numbers,
        # append timing.  Ir.source lines look like "  42  definition ..."
        # We strip the segment index from display and re-pad it for
        # consistent alignment regardless of Ir.source/YXML quirks.
        max_idx = max(seg_map.keys()) if seg_map else 0
        idx_width = max(4, len(str(max_idx)))
        # Fixed column: line(6) + " " (2) + idx(N) + " " (2) + timing(8) + " " (2)
        timing_w = 8  # "  1.23s " or 8 spaces
        result_lines = []
        for source_line in raw_source.splitlines():
            plain = strip_yxml(source_line).lstrip()
            display = apply_transforms(transforms, source_line)
            idx_match = re.match(r'(\d+)\s', plain)
            if idx_match:
                idx = int(idx_match.group(1))
                # Strip original index prefix from display, re-pad
                display_stripped = re.sub(
                    r'^\s*\d+\s{1,2}', '', display.lstrip())
                idx_str = str(idx).rjust(idx_width)
                seg = seg_map.get(idx)
                if seg:
                    ln = f"L{seg['line']:5d}"
                    elapsed = timing_by_offset.get(
                        (seg["file"], seg["offset"]))
                    timing_col = f"{elapsed:6.2f}s " if elapsed else " " * timing_w
                else:
                    ln = "      "
                    timing_col = " " * timing_w
                result_lines.append(
                    f"{ln} C{idx_str}  {timing_col}{display_stripped}")
            else:
                pad = " " * (6 + 1 + 1 + idx_width + 2 + timing_w)
                result_lines.append(f"{pad}{display.lstrip()}")
        return "\n".join(result_lines)

    def _cmd_resolve(self, text):
        m, err = self._parse_slash(
            text, r'/resolve\s+"([^"]*)"\s+(\d+)$',
            '/resolve "THEORY" LINE')
        if err:
            return err
        target = m.group(1)
        line_num = int(m.group(2))

        theory = None
        if ".thy" in target.lower():
            # File pattern — find matching theory
            conn = self.pool.acquire()
            try:
                raw = conn.send("Ir.theories ();")
            finally:
                self.pool.release(conn)
            theory_names = [l.strip() for l in
                            strip_yxml(raw).splitlines() if l.strip()]
            stem = os.path.splitext(os.path.basename(target))[0]
            for t in theory_names:
                if t.endswith("." + stem) or t == stem:
                    theory = t
                    break
            if not theory:
                for t in theory_names:
                    smap = self._build_source_map(t)
                    if smap:
                        for s in smap.values():
                            if target.lower() in s["file"].lower():
                                theory = t
                                break
                    if theory:
                        break
            if not theory:
                return f"Cannot find theory for file '{target}'"
        else:
            theory = target

        seg_map = self._build_source_map(theory)
        if not seg_map:
            return (f"No source map for {theory} "
                    "(rebuild with record_theories=true?)")

        best_idx = None
        best_line = 0
        for idx, s in seg_map.items():
            if s["line"] <= line_num and s["line"] > best_line:
                best_line = s["line"]
                best_idx = idx
        if best_idx is None:
            return f"No segment at or before line {line_num} in {theory}"
        return f"{theory}:{best_idx}"


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
        disconnect_reason = "closed by client"
        with self.clients_lock:
            peer = self.clients[client]["peer"] if client in self.clients else "?"
        try:
            # Token authentication: first line must match self.token
            auth_buf = b""
            while b"\n" not in auth_buf:
                chunk = client.recv(4096)
                if not chunk:
                    disconnect_reason = "closed during auth (no data)"
                    return
                auth_buf += chunk
            auth_line, buf = auth_buf.split(b"\n", 1)
            received_token = auth_line.decode("utf-8", errors="replace")
            if not hmac.compare_digest(received_token, self.token):
                client.sendall(b"ERR: authentication failed\n")
                disconnect_reason = "authentication failed"
                preview = received_token[:8] + "..." if len(received_token) > 8 else received_token
                self.log(f"{YELLOW}[auth] {peer} authentication failed "
                         f"(received {len(received_token)} bytes: "
                         f"{preview!r}){RST}")
                return
            client.sendall(b"OK\n")

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
                    # Intercept /-commands before command accumulation
                    if not cmd_lines and text.strip().startswith("/"):
                        local_result = self._handle_local_command(text)
                        if local_result is not None:
                            response = (local_result +
                                        "\n" + SENTINEL + "\n").encode("utf-8")
                            client.sendall(response)
                            with self.clients_lock:
                                if client in self.clients:
                                    self.clients[client]["commands"] += 1
                                    self.clients[client]["bytes_out"] += len(response)
                                    self.clients[client]["last_active"] = time.time()
                            continue
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
                    ml_conn = self.pool.acquire()
                    try:
                        if not ml_conn.alive():
                            ml_conn.close()
                            ml_conn = PolyMLConnection(
                                self.pool.host, self.pool.ml_port,
                                self.pool.token)
                            ml_conn.connect()
                        self.log_input(f"[{peer}]", command)
                        def on_msg(kind, props, body):
                            self.log_output(f"[{peer}]", kind, props, body)
                        raw_output, had_error = ml_conn.send_streaming(command, on_msg)
                        self.pool.release(ml_conn)
                        ml_conn = None
                    except (ConnectionResetError, BrokenPipeError):
                        # Client disconnected mid-request — drain ML in background
                        if ml_conn is not None:
                            self.pool.drain_and_release(ml_conn)
                            ml_conn = None
                        raise
                    except Exception:
                        if ml_conn is not None:
                            self.pool.release(ml_conn)
                            ml_conn = None
                        raise
                    err_prefix = "ERR\n" if had_error else ""
                    response = (err_prefix +
                                apply_transforms(tcp_transforms, raw_output) +
                                "\n" + SENTINEL + "\n").encode("utf-8")
                    client.sendall(response)
                    with self.clients_lock:
                        if client in self.clients:
                            self.clients[client]["commands"] += 1
                            self.clients[client]["bytes_out"] += len(response)
                            self.clients[client]["last_active"] = time.time()
        except (ConnectionResetError, BrokenPipeError) as e:
            disconnect_reason = f"connection reset ({e})"
        except EOFError as e:
            disconnect_reason = f"ML backend connection closed ({e})"
            self.log(f"{RED}[!] {peer} command failed: ML backend connection "
                     f"closed{RST}")
        except OSError as e:
            disconnect_reason = f"OS error ({e})"
        except Exception as e:
            disconnect_reason = f"{type(e).__name__}: {e}"
            self.log(f"{RED}[!] {peer} unexpected error: "
                     f"{type(e).__name__}: {e}{RST}")
        finally:
            with self.clients_lock:
                info = self.clients.pop(client, None)
            client.close()
            if logged_connect:
                peer_str = info["peer"] if info else peer
                cmds = info["commands"] if info else 0
                self.log(f"{RED}[-] {peer_str} disconnected: {disconnect_reason} "
                         f"(cmds={cmds}, {self.num_clients} remaining){RST}")
            elif disconnect_reason != "closed by client":
                self.log(f"{DIM}[probe] {peer} {disconnect_reason}{RST}")
            elif info and info.get("bytes_in", 0) > 0:
                self.log(f"{DIM}[probe] {peer} sent {info['bytes_in']}B, no command{RST}")

    def client_info(self):
        with self.clients_lock:
            return list(self.clients.values())

    @property
    def num_clients(self):
        with self.clients_lock:
            return len(self.clients)

    def info_text(self, ansi=True):
        """Return a server status summary string."""
        uptime = int(time.time() - self._start_time)
        h, m, s = uptime // 3600, (uptime % 3600) // 60, uptime % 60
        n = self.num_clients
        labels = {0: "off", 1: "non-empty", 2: "all messages", 3: "all+hex"}
        d = self.directory or "(none)"
        db = self.heap_info.db_path if self.heap_info else "(none)"
        rh = self.remote_host
        if ansi:
            lines = [
                f"{BOLD}Server info:{RST}",
                f"  session   = {CYAN}{self.session}{RST}",
                f"  dir       = {CYAN}{d}{RST}",
                f"  heap_db   = {CYAN}{db}{RST}",
                f"  remote    = {CYAN}{rh}{RST}" if rh else f"  remote    = {DIM}(local){RST}",
                f"  listen    = {CYAN}127.0.0.1:{self.port}{RST}",
                f"  ml_repl   = {CYAN}127.0.0.1:{self.poly.port}{RST}",
                f"  uptime    = {h}h {m}m {s}s",
                f"  clients   = {n}",
                f"  verbosity = {self.verbose} / {labels[self.verbose]}",
            ]
        else:
            lines = [
                "Server info:",
                f"  session   = {self.session}",
                f"  dir       = {d}",
                f"  heap_db   = {db}",
                f"  remote    = {rh}" if rh else "  remote    = (local)",
                f"  listen    = 127.0.0.1:{self.port}",
                f"  ml_repl   = 127.0.0.1:{self.poly.port}",
                f"  uptime    = {h}h {m}m {s}s",
                f"  clients   = {n}",
                f"  verbosity = {self.verbose} / {labels[self.verbose]}",
            ]
        return "\n".join(lines)

    def shutdown(self):
        self.running = False
        self.sock.close()


def make_toolbar(completer):

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
            if p in ('"thy"', '["thy"]', 'name', 'thy',
                     '"THEORY"', '"FILE"'):
                var_to_params.setdefault('thy', []).append(i)
            elif p in ('id', 'new_id'):
                var_to_params.setdefault('rid', []).append(i)
            elif p in ('idx', 'state_idx', 'secs', 'start', 'stop',
                        'n', 'cmd_id', 'LINE', 'START', 'END'):
                var_to_params.setdefault('num', []).append(i)
            elif p in ('"isar text"', '"text"', '"query"', 'path', 'node'):
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


def process_mgmt_console_input(line, server, cmd_lines, output_fn=None,
                               completer=None):
    """Process a single line of management console input.

    Handles both / commands and REPL commands (accumulated across lines
    until a trailing semicolon).

    Args:
        line: The input line to process.
        server: The Server instance.
        cmd_lines: Mutable list of accumulated (incomplete) command lines.
        output_fn: Callable for output (default: server.mgmt_output).
        completer: Optional IrCompleter to update from command output.

    Returns:
        True if the console should quit, False otherwise.
    """
    out = output_fn or server.mgmt_output
    stripped = line.strip()
    if not stripped and not cmd_lines:
        return False

    if stripped.startswith("/") and not cmd_lines:
        cmd = stripped.split()[0].lower()
        if cmd == "/connections":
            infos = server.client_info()
            out(f"{DIM}Listening on 127.0.0.1:{server.port}{RST}")
            if not infos:
                out(f"{DIM}No open connections.{RST}")
            else:
                now = time.time()
                out(f"{BOLD}{len(infos)} open connection(s):{RST}")
                for i, c in enumerate(infos):
                    age = int(now - c["started"])
                    idle = int(now - c["last_active"])
                    out(f"  {CYAN}{i}: {c['peer']}{RST}  "
                        f"age={age}s  "
                        f"idle={idle}s  "
                        f"cmds={c['commands']}  "
                        f"in={c['bytes_in']}B out={c['bytes_out']}B")
        elif cmd == "/info":
            out(server.info_text(ansi=True))
        elif cmd in ("/sources", "/timings", "/source-map", "/resolve"):
            result = server._handle_local_command(stripped, ansi=True)
            if result is not None:
                out(result)
        elif cmd == "/quit":
            return True
        elif cmd == "/verbosity":
            parts = stripped.split()
            if len(parts) >= 2 and parts[1].isdigit():
                server.verbose = min(int(parts[1]), 3)
            else:
                server.verbose = (server.verbose + 1) % 4
            labels = {0: "off", 1: "non-empty", 2: "all messages", 3: "all+hex"}
            state = labels[server.verbose]
            out(f"Verbosity {server.verbose} / {state}")
        elif cmd == "/show_types":
            if "typing" in yxml_suppress:
                yxml_suppress.discard("typing")
                out("Type annotations: shown")
            else:
                yxml_suppress.add("typing")
                out("Type annotations: hidden")
        elif cmd == "/help":
            out(f"{BOLD}Management commands:{RST}")
            labels = {0: "off", 1: "non-empty", 2: "all messages", 3: "all+hex"}
            state = labels[server.verbose]
            out(f"  {YELLOW}/connections{RST}     Show open client connections")
            out(f"  {YELLOW}/info{RST}            Show server status summary")
            out(f"  {YELLOW}/verbosity [N]{RST}   Set verbosity (currently {server.verbose} / {state})")
            out(f"                      0=off  1=non-empty  2=all messages  3=all+hex")
            types_state = "hidden" if "typing" in yxml_suppress else "shown"
            out(f"  {YELLOW}/show_types{RST}      Toggle type annotations (currently {types_state})")
            out(f"  {YELLOW}/quit{RST}            Shut down the server")
            out(f"  {YELLOW}/help{RST}            This help")
            if server.heap_info:
                out(f"\n{BOLD}Heap DB commands:{RST}")
                out(f"  {YELLOW}/sources{RST}                        List/verify source files")
                out(f"  {YELLOW}/timings [--top N]{RST}              Command timing hotspots")
                out(f"  {YELLOW}/source-map \"THEORY\"{RST}            Segment-to-line mapping")
                out(f"  {YELLOW}/resolve \"THEORY\" LINE{RST}  Find theory:segment for location")
            out("Anything else is sent to the REPL.")
        else:
            out(f"{RED}Unknown command: {cmd}{RST} (try /help)")
        return False

    # REPL command accumulation
    cmd_lines.append(line)
    if not line.rstrip().endswith(";"):
        return False
    command = " ".join(cmd_lines).strip()
    cmd_lines.clear()
    console = server.pool.console
    if not console.alive():
        out(f"{RED}ERR: Poly/ML process terminated{RST}")
        return True
    def on_msg(kind, props, body):
        if body and strip_yxml(body).strip():
            out(apply_transforms(console_transforms, body))
        server.log_output("[this]", kind, props, body)
    server.log_input("[this]", command)
    try:
        output, _had_error = console.send_streaming(command, on_msg)
    except EOFError as e:
        out(f"{RED}ERR: ML backend connection closed: {e}{RST}")
        out(f"{DIM}The Poly/ML process may have crashed. "
            f"Check if it is still running.{RST}")
        return False
    except OSError as e:
        out(f"{RED}ERR: connection error: {e}{RST}")
        return False
    except Exception as e:
        out(f"{RED}ERR: {type(e).__name__}: {e}{RST}")
        return False
    # Update completer from command output
    if completer:
        try:
            if command.startswith("Ir.theories"):
                completer.learn_theories(output)
            elif command.startswith("Ir.load_theory"):
                refresh = console.send("Ir.theories ();")
                completer.learn_theories(refresh)
            elif command.startswith("Ir.repls"):
                completer.learn_repls(output)
            elif command.startswith("Ir.source"):
                m = re.match(r'Ir\.source\s+"([^"]+)"', command)
                if m:
                    completer.learn_source(m.group(1), output)
        except (EOFError, OSError) as e:
            out(f"{DIM}Completer refresh failed: {e}{RST}")
    return False


def console_loop(server, session, output_fn=None):
    """Interactive console for the server operator.

    Args:
        server: The Server instance.
        session: prompt_toolkit PromptSession.
        output_fn: Callable for output (default: server.mgmt_output).
    """
    out = output_fn or server.mgmt_output
    cmd_lines = []
    last_interrupt = 0
    host_prefix = (f"<ansicyan>[{server.remote_host}]</ansicyan>"
                   if server.remote_host else "")
    while server.running:
        try:
            prompt = HTML(f"{host_prefix}<b><ansicyan>%&gt;</ansicyan></b> ") if not cmd_lines \
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
                out(f"{YELLOW}Input cancelled.{RST}")
            else:
                out(f"{YELLOW}Press Ctrl+C again to quit.{RST}")
            continue
        except EOFError:
            break

        if process_mgmt_console_input(line, server, cmd_lines,
                                      output_fn=out,
                                      completer=session.completer):
            break


MGMT_SOCKET_DIR = os.path.expanduser("~")
MGMT_SOCKET_PREFIX = ".ir_repl_mgmt_"
MGMT_SOCKET_SUFFIX = ".sock"

def mgmt_socket_path(port):
    """Return the mgmt socket path for a given repl.py TCP port."""
    return os.path.join(MGMT_SOCKET_DIR, f"{MGMT_SOCKET_PREFIX}{port}{MGMT_SOCKET_SUFFIX}")

def discover_mgmt_sockets():
    """Return list of (port, path) for all existing mgmt sockets."""
    import glob
    pattern = os.path.join(MGMT_SOCKET_DIR,
                           f"{MGMT_SOCKET_PREFIX}*{MGMT_SOCKET_SUFFIX}")
    results = []
    for path in sorted(glob.glob(pattern)):
        base = os.path.basename(path)
        try:
            port = int(base[len(MGMT_SOCKET_PREFIX):-len(MGMT_SOCKET_SUFFIX)])
            results.append((port, path))
        except ValueError:
            pass
    return results


class MgmtSocketServer:
    """Unix socket server for the management console in daemon mode.

    Accepts multiple connections. Output is broadcast to all connected
    clients. Input from any client is fed to process_mgmt_console_input.
    """

    def __init__(self, server, sock_path, completer=None):
        self.server = server
        self.sock_path = sock_path
        self.completer = completer
        self.clients = []
        self.clients_lock = threading.Lock()
        # Wire server output to broadcast
        server.mgmt_output = self.broadcast
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        if os.path.exists(sock_path):
            os.unlink(sock_path)
        self.sock.bind(sock_path)
        os.chmod(sock_path, 0o600)
        self.sock.listen(4)
        self.running = True

    def broadcast(self, msg):
        """Send a line to all connected management clients."""
        data = (str(msg) + "\n").encode("utf-8")
        with self.clients_lock:
            dead = []
            for c in self.clients:
                try:
                    c.sendall(data)
                except (BrokenPipeError, OSError):
                    dead.append(c)
            for c in dead:
                self.clients.remove(c)
                try:
                    c.close()
                except OSError:
                    pass

    def serve_forever(self):
        self.sock.settimeout(1.0)
        while self.running and self.server.running:
            try:
                client, _ = self.sock.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            with self.clients_lock:
                self.clients.append(client)
            print("Management console attached", flush=True)
            threading.Thread(target=self._handle_client, args=(client,),
                             daemon=True).start()

    def _handle_client(self, client):
        cmd_lines = []
        buf = b""
        try:
            while self.running and self.server.running:
                chunk = client.recv(4096)
                if not chunk:
                    break
                buf += chunk
                while b"\n" in buf:
                    line_bytes, buf = buf.split(b"\n", 1)
                    line = line_bytes.decode("utf-8", errors="replace")
                    if process_mgmt_console_input(line, self.server, cmd_lines,
                                                  output_fn=self.broadcast,
                                                  completer=self.completer):
                        self.server.running = False
                        return
        except (ConnectionResetError, BrokenPipeError, OSError):
            pass
        finally:
            with self.clients_lock:
                if client in self.clients:
                    self.clients.remove(client)
            try:
                client.close()
            except OSError:
                pass
            print("Management console detached", flush=True)

    def shutdown(self):
        self.running = False
        self.sock.close()
        with self.clients_lock:
            for c in self.clients:
                try:
                    c.close()
                except OSError:
                    pass
            self.clients.clear()
        try:
            os.unlink(self.sock_path)
        except OSError:
            pass


def attach_mode(sock_path):
    """Connect to a daemon's management socket and run the prompt loop locally.

    If sock_path is None, discover available sockets automatically:
    unique → connect; multiple → interactive choice."""
    if sock_path is None:
        sockets = discover_mgmt_sockets()
        if not sockets:
            print(f"{RED}No daemon sockets found{RST}", file=sys.stderr)
            print(f"{DIM}Start a daemon with: repl.py --daemon{RST}", file=sys.stderr)
            print(f"{DIM}Or specify a socket: repl.py --attach --mgmt-socket PATH{RST}",
                  file=sys.stderr)
            sys.exit(1)
        elif len(sockets) == 1:
            port, sock_path = sockets[0]
            print(f"{DIM}Found daemon on port {port}{RST}", flush=True)
        else:
            print(f"Multiple daemons running:", flush=True)
            for i, (port, path) in enumerate(sockets):
                print(f"  {BOLD}[{i + 1}]{RST} port {GREEN}{port}{RST}  {DIM}({path}){RST}")
            while True:
                try:
                    choice = input(f"Connect to [1-{len(sockets)}]: ").strip()
                    idx = int(choice) - 1
                    if 0 <= idx < len(sockets):
                        _, sock_path = sockets[idx]
                        break
                except (ValueError, EOFError):
                    pass
                print("Invalid choice, try again.")

    if not os.path.exists(sock_path):
        print(f"{RED}No daemon socket at {sock_path}{RST}", file=sys.stderr)
        print(f"{DIM}Start with: repl.py --daemon{RST}", file=sys.stderr)
        sys.exit(1)

    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    try:
        sock.connect(sock_path)
    except (ConnectionRefusedError, OSError) as e:
        print(f"{RED}Cannot connect to {sock_path}: {e}{RST}", file=sys.stderr)
        sys.exit(1)

    print(f"{GREEN}● Attached to daemon at {sock_path}{RST}", flush=True)

    # Background thread: read output from daemon and print it
    stop = threading.Event()

    def reader():
        buf = b""
        try:
            while not stop.is_set():
                chunk = sock.recv(4096)
                if not chunk:
                    break
                buf += chunk
                while b"\n" in buf:
                    line_bytes, buf = buf.split(b"\n", 1)
                    print(line_bytes.decode("utf-8", errors="replace"))
        except OSError:
            pass
        if not stop.is_set():
            print(f"\n{RED}Daemon disconnected.{RST}")

    reader_thread = threading.Thread(target=reader, daemon=True)
    reader_thread.start()

    # Prompt loop
    if _HAVE_PROMPT_TOOLKIT and sys.stdin.isatty():
        histfile = os.path.expanduser("~/.ir_repl_history")
        completer = IrCompleter()
        session = PromptSession(history=FileHistory(histfile), completer=completer,
                                complete_while_typing=Always())
        last_interrupt = 0
        try:
            with patch_stdout(raw=True):
                while not stop.is_set():
                    try:
                        prompt = HTML("<b><ansicyan>%&gt;</ansicyan></b> ")
                        line = session.prompt(prompt,
                                              bottom_toolbar=make_toolbar(completer))
                        last_interrupt = 0
                    except KeyboardInterrupt:
                        now = time.time()
                        if now - last_interrupt < 2:
                            break
                        last_interrupt = now
                        print(f"{YELLOW}Press Ctrl+C again to detach.{RST}")
                        continue
                    except EOFError:
                        break
                    sock.sendall((line + "\n").encode("utf-8"))
        except (BrokenPipeError, OSError):
            pass
    else:
        # Fallback: raw stdin
        try:
            for line in sys.stdin:
                sock.sendall(line.encode("utf-8"))
        except (BrokenPipeError, OSError, KeyboardInterrupt):
            pass

    stop.set()
    sock.close()
    print(f"{DIM}Detached.{RST}")


def find_isabelle_installation(isabelle_arg):
    """Find Isabelle installation path.

    If isabelle_arg is set, try it (handling both directory and binary paths).
    Otherwise, try platform-specific default locations.
    Returns the path to the isabelle executable on success.
    Raises RuntimeError if no installation is found.
    """
    candidates = []

    if isabelle_arg:
        expanded = os.path.expanduser(isabelle_arg)
        # If it's a directory, try common binary locations
        if os.path.isdir(expanded):
            candidates.extend([
                os.path.join(expanded, "bin", "isabelle"),
                os.path.join(expanded, "isabelle"),
            ])
        else:
            candidates.append(expanded)
    else:
        if sys.platform == "darwin":
            # macOS: try /Applications and user directory
            candidates.extend([
                "/Applications/Isabelle2025-2.app/bin/isabelle",
                os.path.expanduser("~/Isabelle2025-2.app/bin/isabelle"),
            ])
        else:
            # Linux: try home directory
            candidates.extend([
                os.path.expanduser("~/Isabelle2025-2/bin/isabelle"),
            ])

    for candidate in candidates:
        if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate

    raise RuntimeError(
        f"Isabelle installation not found. Tried: {', '.join(candidates)}"
    )


def main():
    p = argparse.ArgumentParser(description="I/R REPL TCP server")
    p.add_argument("--port", type=int, default=0,
                   help=f"TCP port for repl.py server (default: try {REPL_DEFAULT_PORT}, "
                        f"then any free port)")
    p.add_argument("--poly-ml-port", type=int, default=0,
                   help="Port for ML_Repl inside Poly/ML (default: 0 = OS picks a free port)")
    p.add_argument("--isabelle", default=None,
                   help="Path to Isabelle executable (auto-detected if not provided)")
    p.add_argument("--session", default="HOL")
    p.add_argument("--dir", default=None)
    p.add_argument("--heaps", default=None,
                   help="Heaps base directory (overrides auto-discovery)")
    p.add_argument("--no-heap-db", action="store_true",
                   help="Disable heap DB integration (source verification, timings)")
    p.add_argument("--repl-only", action="store_true",
                   help="Plain REPL mode: skip heap DB, source matching, and other extras")
    p.add_argument("--kill-orphaned-processes", action="store_true",
                   help="Kill orphaned remote Bash.Server processes (>6h old, PPID=1)")
    p.add_argument("-v", "--verbose", action="store_true",
                   help="Print the command being invoked")
    p.add_argument("--no-bash-server", action="store_true",
                   help="Skip Bash.Server startup (disables sledgehammer)")
    p.add_argument("--server-only", action="store_true",
                   help="Expose TCP server only; do not start a REPL on stdin")
    p.add_argument("--start-only", action="store_true",
                   help="Exec into Poly/ML with ML_Repl (replaces this process)")
    p.add_argument("--show-server", action="store_true",
                   help="Show info about a running ML_Repl and exit")
    p.add_argument("--kill-server", action="store_true",
                   help="Show info about a running ML_Repl, stop it, and exit")
    p.add_argument("--mcp", action="store_true",
                   help="Start mcp_server.py in the background (streamable-http by default)")
    p.add_argument("--mcp-options", default="--transport streamable-http",
                   help="Options for mcp_server.py (default: '--transport streamable-http')")
    p.add_argument("--daemon", action="store_true",
                   help="Run in daemon mode: mgmt console on Unix socket instead of stdin")
    p.add_argument("--expect-ml", action="store_true",
                   help="Require an existing ML_Repl (retry, never start own Poly/ML). "
                        "Set IR_REPL_AUTH_TOKEN to provide the ML_Repl token.")
    p.add_argument("--attach", action="store_true",
                   help="Attach to a running daemon's mgmt console")
    p.add_argument("--kill-daemon", action="store_true",
                   help="Kill a running daemon and exit")
    p.add_argument("--mgmt-socket", default=None,
                   help="Unix socket path for --daemon/--attach "
                        "(default: auto-derived from TCP port)")
    p.add_argument("--pool-size", type=int, default=5,
                   help="Number of persistent ML connections (default: 5, "
                        "1 reserved for console)")
    args = p.parse_args()
    if args.repl_only:
        args.no_heap_db = True

    # Find Isabelle installation
    try:
        args.isabelle = find_isabelle_installation(args.isabelle)
    except RuntimeError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    # --kill-daemon: send /quit to the daemon's mgmt socket
    if args.kill_daemon:
        sock_path = args.mgmt_socket
        if sock_path is None:
            sockets = discover_mgmt_sockets()
            if not sockets:
                print(f"{DIM}No daemon running{RST}")
                sys.exit(0)
            elif len(sockets) == 1:
                _, sock_path = sockets[0]
            else:
                print("Multiple daemons running:")
                for port, path in sockets:
                    print(f"  port {port}  ({path})")
                print(f"{DIM}Use --mgmt-socket to specify which one{RST}")
                sys.exit(1)
        if not os.path.exists(sock_path):
            print(f"{DIM}No daemon running (no socket at {sock_path}){RST}")
            sys.exit(0)
        try:
            sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            sock.connect(sock_path)
            sock.sendall(b"/quit\n")
            sock.close()
            # Wait for socket file to disappear
            for _ in range(20):
                if not os.path.exists(sock_path):
                    break
                time.sleep(0.25)
            print(f"{GREEN}Daemon stopped{RST}")
        except (ConnectionRefusedError, OSError) as e:
            print(f"{RED}Failed to stop daemon: {e}{RST}")
            # Stale socket — clean up
            try:
                os.unlink(sock_path)
            except OSError:
                pass
        sys.exit(0)

    # --attach: connect to daemon and run prompt loop
    if args.attach:
        attach_mode(args.mgmt_socket)  # None → auto-discover
        sys.exit(0)

    # --show-server / --kill-server: probe a running ML_Repl and exit
    if args.show_server or args.kill_server:
        port = args.poly_ml_port
        try:
            conn = PolyMLConnection(port=port)
            conn.connect()
            info = conn.send('val _ = writeln (Session.welcome ());')
            # Get PID holding the port
            try:
                pid = subprocess.check_output(
                    ["lsof", "-ti", f":{port}"], text=True).strip()
            except Exception:
                pid = "unknown"
            print(f"{GREEN}ML_Repl on 127.0.0.1:{port}{RST}  pid={pid}")
            if info:
                print(f"  {strip_yxml(isabelle_to_unicode(info))}")
            if args.kill_server:
                try:
                    conn.send('ML_Repl.stop ();')
                except (EOFError, OSError):
                    pass
                time.sleep(0.5)
                print(f"{YELLOW}Server stopped{RST}")
            conn.close()
        except (ConnectionRefusedError, OSError):
            print(f"{RED}No ML_Repl on 127.0.0.1:{port}{RST}")
            sys.exit(1)
        sys.exit(0)

    ml_dir = os.path.dirname(os.path.abspath(__file__))

    global UNICODE_TO_ASCII, ASCII_TO_UNICODE
    UNICODE_TO_ASCII = _load_symbols(args.isabelle)
    ASCII_TO_UNICODE = {v: k for k, v in UNICODE_TO_ASCII.items()}

    # --start-only: exec into Poly/ML directly (replaces this process)
    if args.start_only:
        cmd = PolyMLProcess._build_cmd(
            args.isabelle, args.session, args.dir, ml_dir, args.poly_ml_port,
            redirect=False)
        print(f"{BOLD}Exec into Isabelle ML_process "
              f"(session={args.session}, port={args.poly_ml_port}){RST}", flush=True)
        if args.verbose:
            safe_cmd = [
                (arg.split("=", 1)[0] + "=****")
                if arg.startswith("bash_process_password=")
                else arg
                for arg in cmd
            ]
            print(f"{DIM}{' '.join(safe_cmd)}{RST}", flush=True)
        os.execvp(cmd[0], cmd)

    # Connect to existing ML_Repl, or start our own Poly/ML
    if args.poly_ml_port == 0 and args.expect_ml:
        print(f"{YELLOW}Warning: --expect-ml without --poly-ml-port; "
              f"trying default port {ML_REPL_DEFAULT_PORT}{RST}", flush=True)
        args.poly_ml_port = ML_REPL_DEFAULT_PORT

    poly = None
    bash_server = None
    remote_host = None
    quiet = args.daemon

    def _log(msg):
        """Startup log: plain in daemon mode, styled otherwise."""
        print(msg, flush=True)

    if args.expect_ml:
        # --expect-ml: connect to an already-running ML_Repl
        ml_token = os.environ.get("IR_REPL_AUTH_TOKEN", "").strip() or None
        conn = PolyMLConnection(port=args.poly_ml_port, token=ml_token)
        for attempt in range(60):
            try:
                conn.connect()
                probe = conn.send('Ir.help ();')
                if "Ir.init" in probe:
                    print(f"{GREEN}● Connected to existing ML_Repl on "
                          f"127.0.0.1:{args.poly_ml_port}{RST}", flush=True)
                    break
                conn.close()
            except (ConnectionRefusedError, ConnectionError, OSError, EOFError):
                conn.close()
                if attempt == 0:
                    print(f"Waiting for ML_Repl on port {args.poly_ml_port}...",
                          flush=True)
                time.sleep(2)
        else:
            print(f"{RED}ML_Repl not available on port {args.poly_ml_port} "
                  f"after 120s{RST}", file=sys.stderr)
            sys.exit(1)
    else:
        # Start our own Poly/ML

        # Detect remote execution via ISABELLE_REMOTE
        remote_host = None
        isa_remote_env = os.environ.get("ISABELLE_REMOTE", "")
        if isa_remote_env:
            m = re.search(r'--host\s+(\S+)', isa_remote_env)
            if m:
                remote_host = m.group(1)
                _log(f"Remote: {remote_host}" if quiet else
                     f"{CYAN}● Remote execution: {BOLD}{remote_host}{RST}")
                # Check for orphaned Bash.Server process trees (>6h old, PPID=1).
                # Only match setsid (tree root), not descendants.
                try:
                    result = subprocess.run(
                        ["ssh", remote_host,
                         "ps -eo pid,ppid,etimes,comm "
                         "| awk '$2==1 && $3>21600 && $4==\"setsid\" {print $1}'"],
                        capture_output=True, text=True, timeout=10)
                    orphan_pids = [p for p in result.stdout.strip().split() if p]
                    if orphan_pids:
                        n = len(orphan_pids)
                        if args.kill_orphaned_processes:
                            # Kill process groups (setsid makes PID == PGID)
                            kill_cmd = "kill -- " + " ".join(f"-{p}" for p in orphan_pids) + " 2>/dev/null"
                            subprocess.run(
                                ["ssh", remote_host, kill_cmd],
                                capture_output=True, timeout=10)
                            _log(f"Killed {n} orphaned Bash.Server tree(s) on {remote_host}"
                                 if quiet else
                                 f"{YELLOW}Killed {n} orphaned Bash.Server tree(s) "
                                 f"on {remote_host}{RST}")
                        else:
                            _log(f"WARNING: {n} orphaned Bash.Server tree(s) on {remote_host} "
                                 f"(use --kill-orphaned-processes to clean up)"
                                 if quiet else
                                 f"{YELLOW}WARNING: {n} orphaned Bash.Server tree(s) "
                                 f"on {remote_host} "
                                 f"(use --kill-orphaned-processes to clean up){RST}")
                except Exception:
                    pass

        if not args.no_bash_server:
            _log("Starting Bash.Server..." if quiet else
                 f"{BOLD}Starting Bash.Server...{RST}")
            bash_server = BashServer(args.isabelle, quiet=quiet)
            _log(f"Bash.Server ready at {bash_server.address}" if quiet else
                 f"{GREEN}● Bash.Server ready at {bash_server.address}{RST}")
        else:
            _log("Bash.Server skipped (sledgehammer unavailable)" if quiet else
                 f"{DIM}Bash.Server skipped (sledgehammer unavailable){RST}")

        _log(f"Starting Isabelle ML_process (session={args.session})..." if quiet else
             f"{BOLD}Starting Isabelle ML_process "
             f"(session={args.session})...{RST}")
        if not quiet:
            done = threading.Event()
            t = threading.Thread(target=spinner,
                                 args=("Loading heap + ML_Repl...", done), daemon=True)
            t.start()
        else:
            done = None; t = None
        poly = PolyMLProcess(args.isabelle, args.session, args.dir, ml_dir,
                             args.poly_ml_port, bash_server=bash_server)

        # Learn the actual port (important when --poly-ml-port 0)
        actual_port = poly.read_actual_port()
        if actual_port is None:
            if done: done.set(); t.join()
            print(f"{RED}Poly/ML process exited or timed out before "
                  f"reporting port{RST}", file=sys.stderr)
            if poly.startup_output:
                for line in poly.startup_output:
                    print(f"{DIM}{line}{RST}", file=sys.stderr)
            poly.close()
            sys.exit(1)
        conn = PolyMLConnection(port=actual_port, token=poly.token)

        # Wait for ML_Repl TCP port to become available
        for attempt in range(300):  # up to 60s
            if not poly.alive():
                if done: done.set(); t.join()
                # Read any output for diagnostics
                out = poly.proc.stdout.read().decode("utf-8", errors="replace")
                print(f"{RED}Poly/ML process exited (rc={poly.proc.returncode}){RST}",
                      file=sys.stderr)
                if out.strip():
                    print(f"{DIM}{out.strip()}{RST}", file=sys.stderr)
                sys.exit(1)
            try:
                conn.connect()
                probe = conn.send('Ir.help ();')
                if "Ir.init" in probe:
                    break
                conn.close()
            except (ConnectionRefusedError, ConnectionError, OSError, EOFError):
                conn.close()
            time.sleep(0.2)
        else:
            if done: done.set(); t.join()
            print(f"{RED}ML_Repl did not become available{RST}", file=sys.stderr)
            poly.close()
            sys.exit(1)

        if done: done.set(); t.join()
        _log(f"ML_Repl ready on 127.0.0.1:{poly.port}" if quiet else
             f"{GREEN}● ML_Repl ready on "
             f"127.0.0.1:{poly.port}{RST}")

    # Heap DB integration
    heap_info = None
    if not args.no_heap_db:
        try:
            from heap_info import HeapInfo
            # Ask the running ML process for its platform (e.g. "arm64_32-darwin").
            # ML_System.platform is reliable; isabelle getenv ML_PLATFORM is not
            # (empty outside a running Isabelle process).
            # Determine the ML platform directory name.
            # Remote case (ISABELLE_REMOTE set): parse ML_platform from it,
            # because the ML process only knows the remote platform name.
            # Local case: ML_System.platform is correct.
            ml_system = subprocess.check_output(
                [args.isabelle, "getenv", "-b", "ML_SYSTEM"],
                text=True, timeout=10).strip()
            isa_remote = os.environ.get("ISABELLE_REMOTE", "")
            m = re.search(r'-o\s+ML_platform=(\S+)', isa_remote)
            if m:
                ml_platform = m.group(1)
            else:
                ml_platform = strip_yxml(conn.send(
                    'val _ = writeln (ML_System.platform);')).strip()
            ml_identifier = (ml_system + "_" + ml_platform
                             ) if ml_system and ml_platform else ""
            heap_info = HeapInfo.discover(args.session, args.isabelle,
                                          ml_identifier=ml_identifier,
                                          heaps_dir=args.heaps)
            if heap_info:
                _log(f"Heap DB: {heap_info.db_path}" if quiet else
                     f"{GREEN}● Heap DB: {heap_info.db_path}{RST}")
                missing_vars = heap_info.unresolved_env_vars()
                if missing_vars:
                    for var in sorted(missing_vars):
                        if var == "ISABELLE_PROJECT_BASE":
                            default = (os.path.realpath(args.dir)
                                       if args.dir else os.getcwd())
                            _log(f"WARNING: ${var} is not set — "
                                 f"defaulting to {default}. "
                                 f"Set it with: export {var}=/path/to/sources"
                                 if quiet else
                                 f"{YELLOW}WARNING: ${var} is not set — "
                                 f"defaulting to {default}. "
                                 f"Set it with: "
                                 f"export {var}=/path/to/sources{RST}")
                            os.environ[var] = default
                            from heap_info import _isabelle_env_cache
                            _isabelle_env_cache.pop(
                                (var, args.isabelle), None)
                        else:
                            _log(f"WARNING: ${var} is not set — "
                                 f"source files using it cannot be "
                                 f"resolved. Set it with: "
                                 f"export {var}=/path/to/sources"
                                 if quiet else
                                 f"{YELLOW}WARNING: ${var} is not set — "
                                 f"source files using it cannot be "
                                 f"resolved. Set it with: "
                                 f"export {var}=/path/to/sources{RST}")
                if not heap_info.unresolved_env_vars():
                    sources = heap_info.source_files()
                    verified = sum(1 for s in sources
                                   if s["status"] == "verified")
                    changed = sum(1 for s in sources
                                  if s["status"] == "changed")
                    if changed:
                        _log(f"Sources: {verified} verified, "
                             f"{changed} changed since heap build"
                             if quiet else
                             f"{YELLOW}Sources: {verified} verified, "
                             f"{changed} changed since heap build{RST}")
                    elif verified:
                        _log(f"Sources: {verified} verified" if quiet else
                             f"{DIM}Sources: {verified} verified{RST}")
            else:
                _log("No heap DB found" if quiet else
                     f"{DIM}No heap DB found "
                     f"(timing/source features unavailable){RST}")
        except Exception as e:
            _log(f"Heap DB error: {e}" if quiet else
                 f"{YELLOW}Heap DB error: {e}{RST}")

    def _signal_cleanup(signum, frame):
        if poly:
            poly.close()
        if bash_server:
            bash_server.close()
        if heap_info:
            heap_info.close()
        sys.exit(128 + signum)
    signal.signal(signal.SIGTERM, _signal_cleanup)
    signal.signal(signal.SIGHUP, _signal_cleanup)

    pool_size = args.pool_size
    if poly and poly.max_connections is not None:
        ml_max = poly.max_connections
        if pool_size > ml_max:
            print(f"{YELLOW}Pool size {pool_size} exceeds ML connection limit "
                  f"{ml_max}, capping to {ml_max}{RST}", flush=True)
            pool_size = ml_max
    pool_size = max(2, pool_size)
    # Close probe before opening pool connections to free one connection slot.
    pool_host, pool_port, pool_token = conn.host, conn.port, conn.token
    conn.close()
    pool = MLConnectionPool(
        host=pool_host, port=pool_port, token=pool_token,
        size=pool_size)
    server = Server(pool, args.port, host="127.0.0.1",
                    session=args.session, directory=args.dir,
                    heap_info=heap_info, remote_host=remote_host)
    mgmt_output = server.mgmt_output
    accept_thread = threading.Thread(target=server.serve_forever, daemon=True)
    accept_thread.start()

    # Token must be printed before the port line: IQExploreDockable's
    # reader loop exits as soon as it finds the port pattern.
    print(f"IR_Repl.token: {server.token}", flush=True)
    mgmt_output(f"{GREEN}● REPL ready.{RST} Waiting for connections on "
                f"{BOLD}127.0.0.1:{server.port}{RST}")

    mcp_proc = None
    if args.mcp:
        mgmt_output(f"{BOLD}Starting MCP server...{RST}")
        mcp_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "mcp_server.py")
        mcp_cmd = [sys.executable, mcp_path] + shlex.split(args.mcp_options) + ["--repl-port", str(server.port)]
        mcp_proc = subprocess.Popen(mcp_cmd, stdin=subprocess.DEVNULL,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)

        import atexit
        def _kill_mcp():
            if mcp_proc and mcp_proc.poll() is None:
                mcp_proc.terminate()
                try:
                    mcp_proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    mcp_proc.kill()
        atexit.register(_kill_mcp)

        def _mcp_log_reader():
            started = False
            for raw in mcp_proc.stdout:
                line = raw.decode("utf-8", errors="replace").rstrip()
                if line:
                    if "No module named" in line:
                        req_path = os.path.join(os.path.dirname(mcp_path), "requirements.txt")
                        mgmt_output(f"{RED}[MCP] {line}{RST}")
                        mgmt_output(f"{YELLOW}⚠️  MCP server failed to start. "
                                    f"Install dependencies: "
                                    f"pip install -r {req_path}{RST}")
                        mgmt_output(f"{DIM}   REPL is still available on "
                                    f"127.0.0.1:{server.port}{RST}")
                    elif not started and "running on" in line.lower():
                        started = True
                        mgmt_output(f"{DIM}[MCP]{RST} {line}")
                        mgmt_output(f"{GREEN}● MCP server started{RST}")
                    else:
                        if line.startswith("ERROR:"):
                            mgmt_output(f"{RED}[MCP] {line}{RST}")
                        elif server.verbose:
                            mgmt_output(f"{DIM}[MCP]{RST} {line}")
            rc = mcp_proc.wait()
            if rc != 0:
                mgmt_output(f"{RED}⚠️  MCP server exited (rc={rc}){RST}")
                mgmt_output(f"{DIM}   REPL is still available on "
                            f"127.0.0.1:{server.port}{RST}")

        threading.Thread(target=_mcp_log_reader, daemon=True).start()

    if args.server_only:
        mgmt_output(f"{DIM}Running in server-only mode (no stdin REPL). "
                    f"Send SIGTERM or SIGINT to stop.{RST}")
        try:
            accept_thread.join()
        except KeyboardInterrupt:
            pass
    elif args.daemon:
        completer = IrCompleter()
        completer.learn_theories(server.pool.console.send("Ir.theories ();"))
        sock_path = args.mgmt_socket or mgmt_socket_path(server.port)
        mgmt_sock = MgmtSocketServer(server, sock_path, completer=completer)
        mgmt_output = server.mgmt_output  # now points to mgmt_sock.broadcast
        mgmt_output(f"{DIM}Daemon mode. Attach with: repl.py --attach{RST}")
        mgmt_output(f"{DIM}Management socket: {sock_path}{RST}")
        # Print to local stderr too so the operator sees it
        print(f"{GREEN}● Daemon mode.{RST} Mgmt socket: {sock_path}",
              file=sys.stderr, flush=True)
        print(f"{DIM}Attach with: repl.py --attach{RST}",
              file=sys.stderr, flush=True)
        try:
            mgmt_sock.serve_forever()
        except KeyboardInterrupt:
            pass
        finally:
            mgmt_sock.shutdown()
    elif not _HAVE_PROMPT_TOOLKIT or not sys.stdin.isatty():
        if not _HAVE_PROMPT_TOOLKIT:
            req_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "requirements.txt")
            mgmt_output(f"{YELLOW}⚠️  prompt_toolkit is not installed. "
                        f"Install dependencies for the full experience: "
                        f"pip install -r {req_path}{RST}")
        mgmt_output(f"{DIM}Running in server-only mode. "
                    f"Connect on 127.0.0.1:{server.port}, "
                    f"e.g. nc 127.0.0.1 {server.port}{RST}")
        try:
            accept_thread.join()
        except KeyboardInterrupt:
            pass
    else:
        histfile = os.path.expanduser("~/.ir_repl_history")
        completer = IrCompleter()
        # Seed completer with loaded theories and source files
        completer.learn_theories(server.pool.console.send("Ir.theories ();"))
        session = PromptSession(history=FileHistory(histfile), completer=completer,
                                complete_while_typing=Always())
        try:
            with patch_stdout(raw=True):
                console_loop(server, session)
        except KeyboardInterrupt:
            pass

    mgmt_output(f"{DIM}Shutting down...{RST}")
    if mcp_proc and mcp_proc.poll() is None:
        mgmt_output(f"{DIM}  stopping MCP server...{RST}")
        mcp_proc.terminate()
        try:
            mcp_proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            mcp_proc.kill()
    mgmt_output(f"{DIM}  closing TCP server...{RST}")
    server.shutdown()
    mgmt_output(f"{DIM}  closing ML connection...{RST}")
    conn.close()
    if poly:
        mgmt_output(f"{DIM}  stopping Poly/ML process...{RST}")
        poly.close()
    if bash_server:
        mgmt_output(f"{DIM}  stopping Bash.Server...{RST}")
        bash_server.close()
    if heap_info:
        heap_info.close()


if __name__ == "__main__":
    main()
