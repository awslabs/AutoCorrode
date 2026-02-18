# I/R — Isabelle/REPL

I/R provides interactive Isabelle theory exploration outside of jEdit,
from the command line or programmatically via TCP and MCP.

## Overview

I/R consists of three components:

- **`explore.ML`** — Isabelle/ML library providing named, forkable REPL
  sessions rooted at arbitrary theory positions. Supports stepping through
  Isar text, editing and replaying steps, viewing proof state, inspecting
  theory source, and invoking sledgehammer.
- **`repl.py`** — TCP server wrapping a Poly/ML console. Starts an Isabelle
  console process, loads `explore.ML`, and multiplexes client connections
  over a single serialized ML session. Includes an interactive management
  console with tab completion and Unicode-to-Isabelle symbol translation.
- **`explore_mcp.py`** — MCP server exposing each Explore function as an
  MCP tool, allowing LLM agents to drive proof exploration over a
  structured tool interface. Connects to `repl.py` over TCP.

## Quick Start

```bash
# Install Python dependencies
pip install -r ir/requirements.txt

# Start the REPL server (loads HOL + AutoCorrode session)
python3 ir/repl.py --session AutoCorrode --dir .

# In another terminal, connect via netcat or the MCP server
nc localhost 9147
Explore.init "test" "MyTheory";
Explore.step "lemma foo: True";
Explore.step "by simp";
Explore.state ~1;
```

## MCP Integration

```bash
# Start the MCP server (connects to a running repl.py)
python3 ir/explore_mcp.py
```

The MCP server exposes tools for `init`, `fork`, `focus`, `step`, `show`,
`state`, `edit`, `replay`, `sledgehammer`, and more.

## Dependencies

- **Isabelle2025-2** with a built session heap (e.g. HOL or AutoCorrode)
- **Python 3.10+**
- **prompt_toolkit** — interactive console with tab completion and history (`repl.py`)
- **mcp** — Model Context Protocol server framework (`explore_mcp.py`)

Install via `pip install -r requirements.txt`, or in a virtual environment:

```bash
cd ir
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
```
