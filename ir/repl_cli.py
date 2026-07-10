#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

"""One-shot TCP client for the I/R REPL server (repl.py).

Connect to a RUNNING repl.py TCP server, issue a SINGLE command, print the
reply, exit — the shell-level analogue of what I/Q does for an I/R MCP call.
Typed verbs marshal their args into `Ir.*` ML (same quoting as the Scala
IRClient); `raw` sends an ML expression verbatim.

This module is deliberately tiny and imports only the stdlib essentials, so
`repl.py cli ...` (which dispatches here before repl.py's heavy server body
runs) pays almost nothing beyond Python interpreter startup. It shares nothing
with the server but the wire protocol (token line -> OK, send `cmd;`, read
until the `<<DONE>>` sentinel, `ERR\\n` prefix on error).
"""

import argparse
import os
import socket
import sys

SENTINEL = "<<DONE>>"
REPL_DEFAULT_PORT = 9147


def oneshot_send(command, port=REPL_DEFAULT_PORT, token=None,
                 host="127.0.0.1", timeout=None):
    """Open a fresh connection, authenticate, send one command, read until the
    sentinel, close. Returns (output, had_error). The trailing ';' is added if
    missing. Raises OSError/EOFError/PermissionError on connection/protocol
    failure."""
    sock = socket.create_connection((host, port), timeout=timeout)
    try:
        if token:
            sock.sendall((token + "\n").encode("utf-8"))
            auth = b""
            while b"\n" not in auth:
                chunk = sock.recv(1024)
                if not chunk:
                    raise EOFError("connection closed during auth handshake")
                auth += chunk
            if not auth.startswith(b"OK"):
                raise PermissionError("REPL authentication failed (bad token?)")
        cmd = command.strip()
        if not cmd.endswith(";") and not cmd.startswith("/"):
            cmd += ";"
        sock.sendall((cmd + "\n").encode("utf-8"))
        buf = b""
        while True:
            chunk = sock.recv(4096)
            if not chunk:
                raise EOFError("connection closed by repl.py before sentinel")
            buf += chunk
            text = buf.decode("utf-8", errors="replace")
            if SENTINEL in text:
                # Detect the "ERR\n" error marker (repl_srv's err_prefix) on the
                # RAW payload, before stripping trailing newlines: an error with
                # an empty body is just "ERR\n", which rstrip would collapse to
                # "ERR" and hide the marker (misreporting the error as success).
                # Mirrors IRClient.scala's check on the un-stripped join.
                payload = text[:text.index(SENTINEL)]
                if payload.startswith("ERR\n"):
                    return payload[4:].rstrip("\n"), True
                return payload.rstrip("\n"), False
    finally:
        sock.close()


# -- ML argument marshalling (mirrors IRClient.scala's q / ql / mlInt) --

def _ml_str(s):
    """ML string literal with escaping."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'

def _ml_int(s):
    """ML integer literal; negatives use ML's ~ (so -1 -> ~1)."""
    n = int(s)  # raises ValueError on a non-int arg -> caught as a usage error
    return ("~" + str(-n)) if n < 0 else str(n)


# find_theorems query keywords that are NOT term patterns (so must not be quoted).
_FT_KEYWORDS = ("name:", "simp:", "intro", "elim", "dest", "solves")

def _autoquote_ft_query(query):
    """Auto-quote bare term patterns in a `find-theorems` query so a user can
    type  sum _ _  instead of  "sum _ _"  (an unquoted term is an outer-syntax
    error to find_theorems). A criterion is left untouched if it is already
    quoted, is a name:/simp: pattern, or is one of the goal-based keywords
    (intro/elim/dest/solves); a leading `-` (negation) is preserved. This
    mirrors mcp_server.find_theorems so the CLI and MCP grammars stay identical."""
    q = query.strip()
    parts = []
    for criterion in (q.split(" - ") if " - " in q else [q]):
        c = criterion.strip().lstrip("- ").strip()
        neg = criterion.strip().startswith("-")
        prefix = "- " if neg else ""
        if c and not any(c.startswith(k) for k in _FT_KEYWORDS) and not c.startswith('"'):
            parts.append(prefix + '"' + c + '"')
        else:
            parts.append(criterion.strip())
    return " ".join(parts)


# Verb table: name -> (ml_function, arg_kinds, summary).
#   arg_kinds is a list of "s" (ML string) / "i" (ML int), optionally ending in
#   "*s" (variadic trailing strings -> a string list). `raw` is special-cased
#   (one verbatim arg), so it is not in this table.
CLI_VERBS = {
    "theories":      ("Ir.theories",     [],            "list loaded theories"),
    "repls":         ("Ir.repls",        [],            "list all REPLs"),
    "help-ml":       ("Ir.help",         [],            "I/R ML-side help text"),
    "init":          ("Ir.init",         ["s", "*s"],   "create REPL R importing theories"),
    "show":          ("Ir.show",         ["s"],         "REPL info: origin, steps, staleness"),
    "text":          ("Ir.text",         ["s"],         "concatenated Isar text of all steps"),
    "step":          ("Ir.step",         ["s", "s"],    "execute Isar TEXT as the next step"),
    "state":         ("Ir.state",        ["s", "i"],    "proof state at step IDX (0=base, -1=latest)"),
    "fork":          ("Ir.fork",         ["s", "s", "i"], "fork NEW from R at state IDX"),
    "edit":          ("Ir.edit",         ["s", "i", "s"], "replace step IDX with TEXT"),
    "replay":        ("Ir.replay",       ["s"],         "re-execute all stale steps"),
    "truncate":      ("Ir.truncate",     ["s", "i"],    "keep steps 0..IDX (-1 reverts last)"),
    "back":          ("Ir.back",         ["s"],         "revert the last successful step"),
    "merge":         ("Ir.merge",        ["s"],         "inline sub-REPL into its parent"),
    "remove":        ("Ir.remove",       ["s"],         "delete REPL R and its sub-REPLs"),
    "interrupt":     ("Ir.interrupt",    ["s"],         "cooperatively interrupt a busy REPL"),
    "load-theory":   ("Ir.load_theory",  ["s"],         "load theory NAME into the session"),
    "source":        ("Ir.source",       ["s", "i", "i"], "theory THY commands START..STOP"),
    "sledgehammer":  ("Ir.sledgehammer", ["s", "i"],    "run sledgehammer on R (SECS timeout)"),
    "timeout":       ("Ir.timeout",      ["s", "i"],    "set step timeout for R (0=unlimited)"),
    "find-theorems": ("Ir.find_theorems", ["s", "i", "s"], "search theorems: R, max N, QUERY (bare terms auto-quoted; name:/simp:/intro/... kept literal)"),
}

# Human-readable arg placeholders per verb (for help/usage).
_CLI_ARGHELP = {
    "init": "R [THEORY...]", "show": "R", "text": "R", "step": "R TEXT",
    "state": "R IDX", "fork": "R NEW IDX", "edit": "R IDX TEXT", "replay": "R",
    "truncate": "R IDX", "back": "R", "merge": "R", "remove": "R",
    "interrupt": "R",
    "load-theory": "NAME", "source": "THY START STOP", "sledgehammer": "R SECS",
    "timeout": "R SECS", "find-theorems": "R N QUERY",
}


def marshal_cli(verb, args):
    """Turn (verb, args) into the ML command string, or raise ValueError with a
    one-line usage message. `raw` takes exactly one verbatim arg."""
    if verb == "raw":
        if len(args) != 1:
            raise ValueError("raw: expects exactly one ML expression "
                             "(quote it as a single shell arg)")
        return args[0]
    if verb not in CLI_VERBS:
        raise ValueError(f"unknown command '{verb}' (try `repl.py cli help`)")
    ml_fn, kinds, _ = CLI_VERBS[verb]
    variadic = kinds and kinds[-1] == "*s"
    fixed = kinds[:-1] if variadic else kinds
    if variadic:
        if len(args) < len(fixed):
            raise ValueError(f"{verb} {_CLI_ARGHELP.get(verb, '')}: too few arguments")
    elif len(args) != len(fixed):
        raise ValueError(f"{verb} {_CLI_ARGHELP.get(verb, '')}: "
                         f"expected {len(fixed)} argument(s), got {len(args)}")
    # find-theorems' QUERY arg gets bare term patterns auto-quoted, matching the
    # MCP tool (mcp_server.find_theorems), so `find-theorems R N 'sum _ _'` works.
    if verb == "find-theorems" and len(args) == len(fixed):
        args = list(args)
        args[-1] = _autoquote_ft_query(args[-1])
    parts = [ml_fn]
    try:
        for kind, a in zip(fixed, args):
            parts.append(_ml_str(a) if kind == "s" else _ml_int(a))
        if variadic:
            rest = args[len(fixed):]
            parts.append("[" + ", ".join(_ml_str(a) for a in rest) + "]")
        elif not fixed:
            parts.append("()")
    except ValueError:
        raise ValueError(f"{verb} {_CLI_ARGHELP.get(verb, '')}: "
                         "an IDX/N argument must be an integer")
    return " ".join(parts)


def format_cli_help():
    """The `repl.py cli` verb table: each command's signature and its raw form."""
    lines = [
        "Usage: repl.py cli VERB [--port N] [--token TOK] [--] [ARGS...]",
        "",
        "  One-shot client: send a single command to a running repl.py TCP",
        "  server and print the reply. Token from --token or $IR_AUTH_TOKEN.",
        "  Put --port/--token BEFORE any `--`; `--` then marks the rest as args",
        "  (needed only for an arg starting with a non-numeric dash — negative",
        "  ints like -1 work without it).",
        "",
        "  Commands (CLI form  ->  ML sent):",
        f"    {'raw EXPR':<26} -> EXPR            (sent verbatim)",
    ]
    for verb, (ml_fn, kinds, summary) in CLI_VERBS.items():
        arghelp = _CLI_ARGHELP.get(verb, "")
        cli_form = (verb + " " + arghelp).strip()
        # Build the raw form mirroring the marshaller: one placeholder per FIXED
        # arg kind, then a list literal if the verb is variadic.
        variadic = bool(kinds) and kinds[-1] == "*s"
        fixed = kinds[:-1] if variadic else kinds
        if not kinds:
            raw = ml_fn + " ()"
        else:
            toks = [t for t in arghelp.replace("[", "").replace("]", "")
                    .replace("...", "").split()]
            ph = {"R": '"R"', "NEW": '"S"', "TEXT": '"…"', "NAME": '"…"',
                  "THY": '"…"', "QUERY": '"…"', "IDX": "i", "START": "i",
                  "STOP": "i", "SECS": "i", "N": "i"}
            rendered = [ph.get(t, t) for t in toks[:len(fixed)]]
            raw = ml_fn + " " + " ".join(rendered)
            if variadic:
                raw += " [\"…\"]"
        lines.append(f"    {cli_form:<26} -> {raw}")
        lines.append(f"    {'':<26}    {summary}")
    return "\n".join(lines)


def main(argv):
    """Entry point for `repl.py cli <argv...>` (argv = args after `cli`). Parses
    options, marshals the verb into ML, sends it one-shot, prints the reply, and
    exits with a status code (0 ok, 1 ML error, 2 usage/connection error)."""
    p = argparse.ArgumentParser(
        prog="repl.py cli",
        description="One-shot client: send a single command to a running "
                    "repl.py TCP server and print the reply.",
        add_help=False)
    p.add_argument("--port", type=int,
                   default=int(os.environ.get("IR_REPL_PORT", REPL_DEFAULT_PORT)),
                   help=f"repl.py TCP port (default {REPL_DEFAULT_PORT}, or $IR_REPL_PORT)")
    p.add_argument("--token", default=None, help="auth token (default: $IR_AUTH_TOKEN)")
    p.add_argument("-h", "--help", action="store_true", help="show the command table")
    # Collect the verb and its args as leftover positionals rather than as
    # declared `nargs="?"` + `nargs="*"` positionals: argparse before Python
    # 3.13 fills both slots from the FIRST contiguous positional run only, so
    # `cli init --port P cli_r Main` (options between verb and args) drops
    # `cli_r Main` as "unrecognized". parse_known_args has no positional
    # grouping to get wrong, so it works identically across versions.
    ns, extras = p.parse_known_args(argv)
    if "--" in extras:
        extras.remove("--")   # drop the first literal `--` separator, if any
    args = argparse.Namespace(
        verb=extras[0] if extras else None,
        args=extras[1:],
        port=ns.port, token=ns.token, help=ns.help)

    if args.help or args.verb is None or args.verb == "help":
        print(format_cli_help())
        sys.exit(0)
    token = args.token if args.token else (os.environ.get("IR_AUTH_TOKEN", "").strip() or None)
    try:
        command = marshal_cli(args.verb, args.args)
    except ValueError as e:
        print(f"{e}", file=sys.stderr)
        sys.exit(2)
    try:
        output, had_error = oneshot_send(command, port=args.port, token=token)
    except (ConnectionRefusedError, OSError, EOFError, PermissionError) as e:
        print(f"cannot reach repl.py on 127.0.0.1:{args.port}: {e}", file=sys.stderr)
        sys.exit(2)
    # ERR -> message to stderr, exit 1; success -> stdout, exit 0. Cleanly split
    # for piping.
    if had_error:
        if output:
            print(output, file=sys.stderr)
        sys.exit(1)
    if output:
        print(output)
    sys.exit(0)


if __name__ == "__main__":
    main(sys.argv[1:])
