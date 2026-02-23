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
    ...
    "ir": {
      "url": "http://localhost:9148/mcp",
    }
    ...
  }
```

"""

import socket
from mcp.server.fastmcp import FastMCP

SENTINEL = "<<DONE>>"

# ---------------------------------------------------------------------------
# TCP client for repl.py
# ---------------------------------------------------------------------------

class ReplClient:
    """Synchronous TCP client for the I/R REPL server."""

    def __init__(self, host: str = "127.0.0.1", port: int = 9147):
        self.host = host
        self.port = port
        self.sock: socket.socket | None = None

    def connect(self, host: str | None = None, port: int | None = None):
        self.disconnect()
        if host is not None:
            self.host = host
        if port is not None:
            self.port = port
        self.sock = socket.create_connection((self.host, self.port))

    def disconnect(self):
        if self.sock is not None:
            try:
                self.sock.close()
            except OSError:
                pass
            self.sock = None

    @property
    def connected(self) -> bool:
        return self.sock is not None

    def send(self, ml_command: str) -> str:
        """Send an ML command and return the output."""
        if self.sock is None:
            raise RuntimeError("Not connected — call the 'connect' tool first")
        self.sock.sendall((ml_command.strip() + "\n").encode())
        buf = b""
        while True:
            chunk = self.sock.recv(4096)
            if not chunk:
                self.sock = None
                raise EOFError("Connection closed by repl.py")
            buf += chunk
            text = buf.decode("utf-8", errors="replace")
            if SENTINEL in text:
                return text[:text.index(SENTINEL)].strip()

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
              "`by`, `definition`, `fun`, `declare`, etc.")

repl = ReplClient()

@mcp.tool(description="Connect to the I/R REPL server. Call this before using any other tool. Can also reconnect after a dropped connection.")
def connect(port: int = 9147, host: str = "127.0.0.1") -> str:
    repl.connect(host, port)
    return f"Connected to {repl.host}:{repl.port}"

@mcp.tool(description="Disconnect from the I/R REPL server.")
def disconnect() -> str:
    if not repl.connected:
        return "Already disconnected"
    repl.disconnect()
    return "Disconnected"

@mcp.tool(description="Create a new REPL session. `theories` is a list of theory specs: [\"TheoryName\"], [\"TheoryName:source_idx\"], or [\"T1\",\"T2\",...] to merge multiple theories. The session starts in the context of those theories — do NOT send a 'theory' command via step.")
def init(id: str, theories: list[str]) -> str:
    ml_list = "[" + ", ".join(ml_str(t) for t in theories) + "]"
    return repl.send(f"Ir.init {ml_str(id)} {ml_list};")

@mcp.tool(description="Fork a sub-REPL from the current REPL at the given state index (0=base, -1=latest).")
def fork(id: str, state_idx: int) -> str:
    return repl.send(f"Ir.fork {ml_str(id)} {ml_int(state_idx)};")

@mcp.tool(description="Switch the current REPL to the one with the given id.")
def focus(id: str) -> str:
    return repl.send(f"Ir.focus {ml_str(id)};")

@mcp.tool(description="Append an Isar command to the current REPL. Examples: 'lemma \"True\"', 'by simp', 'definition ...'. Do NOT use 'theory' commands — the theory context is set by init.")
def step(isar_text: str) -> str:
    return repl.send(f"Ir.step {ml_str(isar_text)};")

@mcp.tool(description="Append a step by reading Isar text from a file path.")
def step_file(path: str) -> str:
    return repl.send(f"Ir.step_file {ml_str(path)};")

@mcp.tool(description="Show the current REPL: origin, steps, and staleness.")
def show() -> str:
    return repl.send("Ir.show ();")

@mcp.tool(description="Print the Toplevel.state at the given index (0=base, 1=after step 0, -1=latest).")
def state(state_idx: int) -> str:
    return repl.send(f"Ir.state {ml_int(state_idx)};")

@mcp.tool(description="Print the concatenated Isar text of all steps in the current REPL.")
def text() -> str:
    return repl.send("Ir.text ();")

@mcp.tool(description="Replace the step at `idx` with new Isar text. Subsequent steps are replayed if auto_replay is on.")
def edit(idx: int, isar_text: str) -> str:
    return repl.send(f"Ir.edit {ml_int(idx)} {ml_str(isar_text)};")

@mcp.tool(description="Re-execute all stale steps in the current REPL.")
def replay() -> str:
    return repl.send("Ir.replay ();")

@mcp.tool(description="Discard all steps after the given index. Use negative indices to count from the end: -1 reverts the last step, -2 the last two, etc.")
def truncate(idx: int) -> str:
    return repl.send(f"Ir.truncate {ml_int(idx)};")

@mcp.tool(description="Revert the last step. Synonym for truncate(-1).")
def back() -> str:
    return repl.send("Ir.back ();")

@mcp.tool(description="Merge the current sub-REPL back into its parent.")
def merge() -> str:
    return repl.send("Ir.merge ();")

@mcp.tool(description="Run Sledgehammer on the current proof state with the given timeout in seconds.")
def sledgehammer(timeout_secs: int) -> str:
    return repl.send(f"Ir.sledgehammer {ml_int(timeout_secs)};")

@mcp.tool(description="Search for theorems matching a query. Uses Isabelle's find_theorems syntax: name patterns (name:\"foo\"), intro/elim/dest/simp rules, or term patterns (e.g. \"_ + _ = _ + _\"). Prefix a criterion with - to negate.")
def find_theorems(query: str, max_results: int = 40) -> str:
    return repl.send(f"Ir.find_theorems {ml_int(max_results)} {ml_str(query)};")

@mcp.tool(description="Set step timeout in seconds (0=unlimited, default 5s).")
def timeout(secs: int) -> str:
    return repl.send(f"Ir.timeout {ml_int(secs)};")

@mcp.tool(description="Remove a REPL and all its sub-REPLs.")
def remove(id: str) -> str:
    return repl.send(f"Ir.remove {ml_str(id)};")

@mcp.tool(description="List all REPL sessions.")
def repls() -> str:
    return repl.send("Ir.repls ();")

@mcp.tool(description="List all loaded Isabelle theories.")
def theories() -> str:
    return repl.send("Ir.theories ();")

@mcp.tool(description="List command spans of a stored theory. Use negative indices to count from the end.")
def source(theory_name: str, start: int, stop: int) -> str:
    return repl.send(f"Ir.source {ml_str(theory_name)} {ml_int(start)} {ml_int(stop)};")

@mcp.tool(description="Update I/R config. Only provided fields are changed; others are left as-is.")
def config(color: bool | None = None, show_ignored: bool | None = None,
           full_spans: bool | None = None, show_theory_in_source: bool | None = None,
           auto_replay: bool | None = None) -> str:
    fields = {"color": color, "show_ignored": show_ignored, "full_spans": full_spans,
              "show_theory_in_source": show_theory_in_source, "auto_replay": auto_replay}
    parts = []
    for name, val in fields.items():
        if val is not None:
            parts.append(f"{name} = {'true' if val else 'false'}")
        else:
            parts.append(f"{name} = #{name} c")
    ml = "fn c => {" + ", ".join(parts) + "}"
    return repl.send(f"Ir.config ({ml});")

@mcp.tool(description="Show the I/R help text.")
def help() -> str:
    return repl.send("Ir.help ();")

@mcp.tool(description="Send a raw ML expression to the Poly/ML console. Use for anything not covered by other tools.")
def raw_ml(ml_code: str) -> str:
    return repl.send(ml_code)

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    import argparse
    p = argparse.ArgumentParser(description="I/R MCP server")
    p.add_argument("--transport", choices=["stdio", "sse", "streamable-http"],
                   default="stdio")
    p.add_argument("--port", type=int, default=9148,
                   help="Port for SSE/streamable-http transport (default: 9148)")
    args = p.parse_args()

    if args.transport in ("sse", "streamable-http"):
        mcp.settings.host = "0.0.0.0"
        mcp.settings.port = args.port
        mcp.run(transport=args.transport)
    else:
        mcp.run(transport="stdio")

if __name__ == "__main__":
    main()
