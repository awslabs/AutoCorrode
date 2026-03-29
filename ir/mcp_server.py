#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

"""
MCP server exposing the I/R REPL.

Connects to a running repl.py instance over TCP (via the `connect` tool)
and exposes each I/R function as an MCP tool.  Runs on stdio transport.

Usage:
    python3 mcp_server.py

MCP configuration for communication via stdin/stdout. Adjust BASE as needed.

```json
  "mcpServers": {
    ...
    "ir": {
      "command": "python3",
      "args": ["{BASE}/ir/mcp_server.py"]
    }
    ...
  }
```

MCP configuration for communication via streaming-http
(adjust host and port as needed):

```json
  "mcpServers": {
    "i/r": {
      "type": "http",
      "url": "http://localhost:9148/mcp",
      "description": "Isabelle Isar REPL"
    }
  }
```

"""

import asyncio
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(line_buffering=True)
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(line_buffering=True)

import socket
from mcp.server.fastmcp import Context, FastMCP

SENTINEL = "<<DONE>>"

# ---------------------------------------------------------------------------
# TCP client for repl.py
# ---------------------------------------------------------------------------

class ReplClient:
    """Ephemeral TCP client for the I/R REPL server.

    Opens a fresh TCP connection per send() call — desync is structurally
    impossible since there is no persistent pipe for stale responses.
    """

    def __init__(self, host: str = "127.0.0.1", port: int = 9147,
                 token: str = ""):
        self.host = host
        self.port = port
        self.token = token

    def connect(self, host: str | None = None, port: int | None = None,
                token: str | None = None):
        if host is not None:
            self.host = host
        if port is not None:
            self.port = port
        if token is not None:
            self.token = token
        # Probe reachability
        sock = socket.create_connection((self.host, self.port))
        sock.close()

    def disconnect(self):
        pass

    @property
    def connected(self) -> bool:
        if not self.token:
            return False
        try:
            sock = socket.create_connection((self.host, self.port), timeout=2)
            sock.close()
            return True
        except Exception:
            return False

    def send(self, ml_command: str) -> str:
        """Send an ML command on a fresh connection and return the output.

        Opens a new TCP socket, authenticates, sends the command, reads
        until the sentinel, and closes.  Raises RuntimeError if the ML
        command produced an error (the REPL server prefixes error responses
        with 'ERR\\n').  FastMCP catches this and returns it to the MCP
        client with isError=true.
        """
        if not self.token:
            raise RuntimeError("Not connected — call the 'connect' tool first")
        sock = socket.create_connection((self.host, self.port))
        try:
            # Authenticate
            sock.sendall((self.token + "\n").encode())
            auth_buf = b""
            while b"\n" not in auth_buf:
                chunk = sock.recv(1024)
                if not chunk:
                    raise RuntimeError("Connection closed during auth handshake")
                auth_buf += chunk
            if not auth_buf.startswith(b"OK"):
                raise RuntimeError("REPL authentication failed")
            # Send command
            cmd = ml_command.strip()
            if not cmd.endswith(";") and not cmd.startswith("/"):
                cmd += ";"
            sock.sendall((cmd + "\n").encode())
            # Read until sentinel
            buf = b""
            while True:
                chunk = sock.recv(4096)
                if not chunk:
                    raise EOFError("Connection closed by repl.py")
                buf += chunk
                text = buf.decode("utf-8", errors="replace")
                if SENTINEL in text:
                    raw = text[:text.index(SENTINEL)].strip()
                    result = apply_transforms(raw)
                    if result.startswith("ERR\n"):
                        raise RuntimeError(result[4:])
                    return result
        finally:
            sock.close()

# ---------------------------------------------------------------------------
# Output transforms (applied to every response from the ML process)
# ---------------------------------------------------------------------------

import re

def isabelle_to_unicode(text):
    """Replace Isabelle symbol encoding with UTF-8."""
    if "\\" not in text:
        return text
    return re.sub(r'(?<!\\)\\<[a-zA-Z_]+>', lambda m: _ASCII_TO_UNICODE.get(m.group(), m.group()), text)

def strip_yxml(text):
    """Remove YXML control sequences, keep plain text."""
    return text.replace("\x05", "").replace("\x06", "")

_ASCII_TO_UNICODE = {}  # populated by _load_symbols below

def _load_mcp_symbols():
    """Load symbol table for MCP server."""
    import os, subprocess
    isabelle = os.environ.get("ISABELLE",
        os.path.expanduser("~/Isabelle2025-2-experimental.app/bin/isabelle"))
    try:
        isabelle_home = subprocess.check_output(
            [isabelle, "getenv", "-b", "ISABELLE_HOME"],
            text=True, timeout=10).strip()
        symbols_path = os.path.join(isabelle_home, "etc", "symbols")
        with open(symbols_path) as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                parts = line.split()
                if len(parts) >= 3 and parts[1] == "code:":
                    sym = parts[0]
                    cp = int(parts[2], 16)
                    _ASCII_TO_UNICODE[sym] = chr(cp)
    except Exception:
        pass

_load_mcp_symbols()

mcp_transforms = [isabelle_to_unicode, strip_yxml]

def apply_transforms(text):
    for t in mcp_transforms:
        text = t(text)
    return text

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def ml_str(s: str) -> str:
    """Escape a Python string as an ML string literal."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'

def ml_int(n: int) -> str:
    """Format a Python int as an ML int literal (negative = ~N)."""
    return f"~{-n}" if n < 0 else str(n)

# ---------------------------------------------------------------------------
# MCP server
# ---------------------------------------------------------------------------

mcp = FastMCP("I/R REPL",
              instructions="Isabelle/ML I/R REPL for interactive theory exploration. "
              "Use `connect` first, then `theories` to list available theories, "
              "`init` to create a REPL session rooted at a theory, `step` to advance, "
              "`show` to inspect, `state` to view proof state. "
              "IMPORTANT: Do NOT send 'theory' commands via `step` — the theory context "
              "is established by `init`. Steps are Isar commands like `lemma`, `apply`, "
              "`by`, `definition`, `fun`, `declare`, etc. "
              "IMPORTANT: Use ASCII symbols in all Isar text, NOT Isabelle symbol encoding. "
              "Use => not \\<Rightarrow>, \" not \\<open>/\\<close>, & not \\<and>, "
              "| not \\<or>, ! not \\<forall>, ? not \\<exists>, --> not \\<longrightarrow>, "
              ":: not \\<in>, etc.")

_repl_clients: dict[int, ReplClient] = {}  # id(ctx.session) -> ReplClient
_repl_port = 9147  # overridden by --repl-port in main()

def _get_client(ctx: Context) -> ReplClient:
    """Return the ReplClient for the current MCP session, creating one if needed."""
    key = id(ctx.session)
    client = _repl_clients.get(key)
    if client is None:
        client = ReplClient()
        _repl_clients[key] = client
    return client

async def _send(ctx: Context, ml_command: str) -> str:
    """Send a command on an ephemeral connection in a background thread."""
    return await asyncio.to_thread(_get_client(ctx).send, ml_command)

@mcp.tool(description="Connect to the I/R REPL server. Call this before using any other tool. Can also reconnect after a dropped connection. If the token is not provided to you, use the IR_AUTH_TOKEN environment variable if set.")
async def connect(token: str, port: int = 0, ctx: Context = None) -> str:
    if port == 0:
        port = _repl_port
    client = _get_client(ctx)
    await asyncio.to_thread(client.connect, "127.0.0.1", port, token)
    return f"Connected to {client.host}:{client.port}\n\n{await session_info(ctx=ctx)}"

@mcp.tool(description="Disconnect from the I/R REPL server.")
async def disconnect(ctx: Context = None) -> str:
    client = _get_client(ctx)
    if not client.token:
        return "Already disconnected"
    client.disconnect()
    _repl_clients.pop(id(ctx.session), None)
    return "Disconnected"

@mcp.tool(description="Show the loaded Isabelle session name, directory, and available theories.")
async def session_info(ctx: Context = None) -> str:
    client = _get_client(ctx)
    if not client.token:
        return "Not connected. Call `connect` first."
    info = await asyncio.to_thread(client.send, '/info')
    session = dir_ = heap_db = ""
    for line in info.splitlines():
        line = line.strip()
        if line.startswith("session"):
            session = line.split("=", 1)[1].strip()
        elif line.startswith("dir"):
            dir_ = line.split("=", 1)[1].strip()
        elif line.startswith("heap_db"):
            heap_db = line.split("=", 1)[1].strip()
    theories = await asyncio.to_thread(client.send, 'Ir.theories ();')
    theories = apply_transforms(theories)
    result = f"Session name: {session}\nSession directory: {dir_}"
    if heap_db and heap_db != "(none)":
        result += f"\nHeap DB: {heap_db}"
        result += "\n\nHeap DB commands available: source_files, timings, source_map, init_at_line"
    result += f"\n\nAvailable theories:\n{theories}"
    return result

@mcp.tool(description=(
    "Show server status including the Isabelle session name, "
    "root directory, ports, uptime, and client count. "
    "Use this to find out which session and directory the REPL is running with."))
async def server_info(ctx: Context = None) -> str:
    client = _get_client(ctx)
    if not client.token:
        return "Not connected. Call `connect` first."
    return await _send(ctx, "/info")

@mcp.tool(description=(
    "Create a new REPL session that imports the given Isabelle theories. "
    "This is equivalent to writing `theory T imports A B C begin ...` in a .thy file. "
    "This is the ONLY way to make a theory's definitions, lemmas, and notations available. "
    "Theories not in the initial heap must be loaded first with `load_theory`.\n\n"
    "`theories` is a list of fully qualified theory names. Examples:\n"
    "- [\"Main\"] — start from the standard HOL library\n"
    "- [\"HOL-Library.Multiset\"] — import the Multiset theory\n"
    "- [\"HOL-Library.Multiset\", \"HOL-Library.FSet\"] — import and merge multiple theories\n"
    "- [\"MySession.MyTheory:42\"] — start from a specific source location (single spec only)\n\n"
    "When multiple theories are listed, they are merged so the REPL has access to all of them. "
    "Use `theories` to see what is already loaded in the session."
))
async def init(repl: str, theories: list[str], ctx: Context = None) -> str:
    ml_list = "[" + ", ".join(ml_str(t) for t in theories) + "]"
    return await _send(ctx, f"Ir.init {ml_str(repl)} {ml_list};")

@mcp.tool(description=(
    "Create a new REPL session rooted at a specific command in the PIDE document model. "
    "Requires the exact node name and command ID from the PIDE document model."
))
async def init_from_document(repl: str, node_name: str, command_id: int, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.init_from_document {ml_str(repl)} {ml_str(node_name)} {ml_int(command_id)};")

@mcp.tool(description="Fork a sub-REPL from an existing REPL at the given state index (0=base, -1=latest).")
async def fork(repl: str, new_repl: str, state_idx: int, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.fork {ml_str(repl)} {ml_str(new_repl)} {ml_int(state_idx)};")

@mcp.tool(description=(
    "Apply an Isar command to a REPL. "
    "Examples: 'lemma \"True\"', 'by simp', 'definition ...'. "
    "Don't use 'theory' commands — the theory context is set by 'init'. "
    "IMPORTANT: If a step FAILS (error response), the REPL state is UNCHANGED — "
    "do NOT call 'back' to undo a failed step."))
async def step(repl: str, isar_text: str, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.step {ml_str(repl)} {ml_str(isar_text)};")

@mcp.tool(description="Show a REPL: origin, steps, and staleness.")
async def show(repl: str, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.show {ml_str(repl)};")

@mcp.tool(description="Print the Toplevel.state at the given index (0=base, 1=after step 0, -1=latest).")
async def state(repl: str, state_idx: int, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.state {ml_str(repl)} {ml_int(state_idx)};")

@mcp.tool(description="Print the concatenated Isar text of all steps in a REPL.")
async def text(repl: str, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.text {ml_str(repl)};")

@mcp.tool(description="Replace the step at `idx` with new Isar text. Subsequent steps are replayed if auto_replay is on.")
async def edit(repl: str, idx: int, isar_text: str, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.edit {ml_str(repl)} {ml_int(idx)} {ml_str(isar_text)};")

@mcp.tool(description="Re-execute all stale steps in a REPL.")
async def replay(repl: str, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.replay {ml_str(repl)};")

@mcp.tool(description="Discard all steps after the given index. Use negative indices to count from the end: -1 reverts the last step, -2 the last two, etc.")
async def truncate(repl: str, idx: int, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.truncate {ml_str(repl)} {ml_int(idx)};")

@mcp.tool(description="Revert the last SUCCESSFUL step. Synonym for truncate(-1). Only call after a step that succeeded — failed steps don't change the REPL state.")
async def back(repl: str, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.back {ml_str(repl)};")

@mcp.tool(description="Merge a sub-REPL back into its parent.")
async def merge(repl: str, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.merge {ml_str(repl)};")

@mcp.tool(description=(
    "Run Sledgehammer on the current proof state. "
    "DO NOT set timeout_secs above 15. The default of 15s is almost always "
    "sufficient — Sledgehammer very rarely finds proofs beyond 15s."))
async def sledgehammer(repl: str, timeout_secs: int = 15, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.sledgehammer {ml_str(repl)} {ml_int(timeout_secs)};")

@mcp.tool(description='Search for theorems. Criteria: '
    'name:foo (name pattern, unquoted), intro/elim/dest/solves (goal-based), '
    'simp:"term" (simplification rules for term), or "pattern" (term pattern). '
    'Terms and patterns MUST be in quotes: "_ + _", "_ @ _". '
    'Name patterns are NOT quoted: name:append. '
    'Prefix with - to negate. '
    'Examples: name:conjI, "_ + _ = _", simp:"True", -name:foo, -"_ + _"')
async def find_theorems(repl: str, query: str, max_results: int = 40, ctx: Context = None) -> str:
    q = query.strip()
    # Auto-quote bare term patterns that aren't already quoted or a keyword
    keywords = ("name:", "simp:", "intro", "elim", "dest", "solves")
    parts = []
    for criterion in q.split(" - ") if " - " in q else [q]:
        c = criterion.strip().lstrip("- ").strip()
        neg = criterion.strip().startswith("-")
        prefix = "- " if neg else ""
        if c and not any(c.startswith(k) for k in keywords) and not c.startswith('"'):
            parts.append(prefix + '"' + c + '"')
        else:
            parts.append(criterion.strip())
    return await _send(ctx, f"Ir.find_theorems {ml_str(repl)} {ml_int(max_results)} {ml_str(' '.join(parts))};")

@mcp.tool(description="Set step timeout in seconds (0=unlimited, default 10s). NOTE: DO NOT set this to values >10s unless you have "
          "a specific reason to. Calls like `metis`, `auto`, `blast`, `force`, should NOT take longer than 5s. Even if they do, and the call "
          "ultimately succeeds, it points at a proof that ought to be broken down further. ONLY use a large timeout if you work with very large "
          "scripts or in special circumstances where, exceptionally, a large timeout is expected / tolerated.")
async def timeout(secs: int, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.timeout {ml_int(secs)};")

@mcp.tool(description="Remove a REPL and all its sub-REPLs.")
async def remove(repl: str, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.remove {ml_str(repl)};")

@mcp.tool(description="List all REPL sessions.")
async def repls(ctx: Context = None) -> str:
    return await _send(ctx, "Ir.repls ();")

@mcp.tool(description="List all loaded Isabelle theories. This includes theories from the initial heap plus any loaded via load_theory.")
async def theories(ctx: Context = None) -> str:
    return await _send(ctx, "Ir.theories ();")

@mcp.tool(description=(
    "Load a theory (and its transitive dependencies) by fully qualified name into the Isabelle session. "
    "After loading, the theory becomes available for `init` and appears in `theories`. "
    "Example: load_theory(\"HOL-Library.Multiset\") loads the Multiset theory from HOL-Library. "
    "NOTE: Not available when I/R is running inside Isabelle/jEdit (PIDE mode). "
    "In PIDE mode, open theories in jEdit instead and use init_from_document."
))
async def load_theory(theory_name: str, verbose: bool = False, ctx: Context = None) -> str:
    result = await _send(ctx, f"Ir.load_theory {ml_str(theory_name)};")
    if verbose:
        return result
    return "\n".join(l for l in result.splitlines() if l.startswith("Loaded theory")) or result

@mcp.tool(description="List command spans of a stored theory. Use negative indices to count from the end.")
async def source(theory_name: str, start: int, stop: int, ctx: Context = None) -> str:
    return await _send(ctx, f"Ir.source {ml_str(theory_name)} {ml_int(start)} {ml_int(stop)};")

@mcp.tool(description="Set verbosity of theory source listings. 0 (default): abbreviated command spans. 1: full command spans.")
async def set_verbosity(level: int, ctx: Context = None) -> str:
    val = "true" if level > 0 else "false"
    return await _send(ctx, f"Ir.config (fn c => {{color = #color c, show_ignored = #show_ignored c, "
                     f"full_spans = {val}, show_theory_in_source = #show_theory_in_source c, "
                     f"auto_replay = #auto_replay c}});")

@mcp.tool(description="Enable or disable auto-replay after edits to REPLs. 0: disable, 1: enable (default).")
async def set_auto_replay(enabled: int, ctx: Context = None) -> str:
    val = "true" if enabled > 0 else "false"
    return await _send(ctx, f"Ir.config (fn c => {{color = #color c, show_ignored = #show_ignored c, "
                     f"full_spans = #full_spans c, show_theory_in_source = #show_theory_in_source c, "
                     f"auto_replay = {val}}});")

@mcp.tool(description="Show the I/R help text.")
async def help(ctx: Context = None) -> str:
    return await _send(ctx, "Ir.help ();")

@mcp.tool(description=(
    "List source files recorded in the heap database. "
    "With check=True (default), verifies each file's SHA1 digest against the filesystem "
    "to detect files that have changed since the heap was built."))
async def source_files(check: bool = True, ctx: Context = None) -> str:
    cmd = "/sources --check" if check else "/sources"
    return await _send(ctx, cmd)

@mcp.tool(description=(
    "Show the slowest commands from the heap build. "
    "Useful for identifying proof bottlenecks before starting refactoring. "
    "Returns per-command timing (with file:line) and per-file aggregation."))
async def timings(top_n: int = 20, theory: str = "", ctx: Context = None) -> str:
    cmd = f"/timings --top {top_n}"
    if theory:
        cmd += f" --theory {theory}"
    return await _send(ctx, cmd)

@mcp.tool(description=(
    "Get the segment-to-line-number mapping for a theory. "
    "Shows each segment's index, source line number, command keyword, "
    "and build timing (if available from the heap DB). "
    "Use this to understand a theory's structure before using init()."))
async def source_map(theory_name: str, ctx: Context = None) -> str:
    return await _send(ctx, f'/source-map "{theory_name}"')


@mcp.tool(description=(
    "Create a REPL at a specific line in a source file. "
    "This is the easiest way to start working at a particular source location — "
    "it automatically resolves the file and line number to the correct theory and "
    "segment index, then creates the REPL there. "
    "The theory_or_file argument can be a theory name (e.g. 'MySession.Foo') "
    "or a file suffix (e.g. 'Foo.thy')."))
async def init_at_line(id: str, theory_or_file: str, line: int, ctx: Context = None) -> str:
    client = _get_client(ctx)
    resolution = await asyncio.to_thread(client.send, f'/resolve "{theory_or_file}" {line}')
    spec = resolution.strip()
    if not spec or spec.startswith("ERR") or spec.startswith("No ") or \
       spec.startswith("Cannot") or spec.startswith("Usage"):
        return spec
    return await asyncio.to_thread(client.send, f"Ir.init {ml_str(id)} [{ml_str(spec)}];")

@mcp.tool(description="Send a raw ML expression to the Poly/ML console. Use for anything not covered by other tools. The expression must end with a semicolon.")
async def raw_ml(ml_code: str, ctx: Context = None) -> str:
    code = ml_code.rstrip()
    if not code.endswith(";"):
        code += ";"
    return await _send(ctx, code)

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    import argparse
    p = argparse.ArgumentParser(description="I/R MCP server")
    p.add_argument("--transport", choices=["stdio", "sse", "streamable-http"],
                   default=None)
    p.add_argument("--port", type=int, default=None,
                   help="Port for SSE/streamable-http transport (default: 9148)")
    p.add_argument("--repl-port", type=int, default=9147,
                   help="Port of the I/R REPL to connect to (default: 9147)")
    args = p.parse_args()

    port_explicit = args.port is not None
    transport = args.transport

    if port_explicit and transport == "stdio":
        p.error("--port cannot be used with --transport stdio")

    if transport is None:
        transport = "streamable-http" if port_explicit else "stdio"

    if args.port is None:
        args.port = 9148

    global _repl_port
    _repl_port = args.repl_port

    if transport in ("sse", "streamable-http"):
        mcp.settings.host = "127.0.0.1"
        mcp.settings.port = args.port
        mcp.run(transport=transport)
    else:
        mcp.run(transport="stdio")

if __name__ == "__main__":
    main()
