# I/Q

I/Q -- short for Isabelle/Q -- is an Isabelle/jEdit plugin exposing proof editing/exploration capabilities as an MCP server:
1. Reading and writing theory files through jEdit
2. Querying open documents and document stats (warnings, errors, timing information)
3. Querying command states (e.g. intermediate proof states)
4. Proof search and exploration via sledgehammer, find_theorems, and an overlay-based mechanism for try-running Isar proof steps/scripts without interfering with the user.

The purpose of I/Q is to enable MCP-capable AI agents such as [Amazon Q](https://aws.amazon.com/q/) to autonomously or collaboratively conduct interactive theorem proving using Isabelle.

**NOTE:** I/Q is still a very early prototype. We expect that its mechanisms will need tweaking/expanding. I/Q is mechanism _only_: It needs to be complemented with behavioral guidance and/or additional knowledge to become an effective proof engineer. If you are curious, please try I/Q and let us know about your use cases and ideas for improvement!

## Usage

### Prerequisites

We recommend Isabelle2025-2. We have not tested I/Q with another version of Isabelle.
The build instructions below assume a Unix-like environment (e.g. Linux, macOS).

### Building the plugin

You can build the plugin via `make` and `make install`. This compiles the Scala sources and installs the plugin JAR. By default, the JAR is copied to `~/.isabelle/Isabelle2025-2/jedit/jars/`, but you can inspect and configure various environment variables; see `make help`.

### Registering the plugin

You need to register the plugin with your agentic AI as an MCP server. For Amazon Q, add the following to your mcp.json:

```json
{
  "I/Q": {
    "command": "python3",
    "args": ["{ROOT_DIRECTORY_OF_PLUGIN}/iq_bridge.py"],
    "env": {},
    "autoApprove": [],
    "description": "MCP server to connect to an Isabelle/jEdit instance and inspect/modify Isabelle theory files, proof states, and session information"
  }
}
```

### Starting I/Q

I/Q starts automatically when you start Isabelle, and you should see it as `Plugins` → `I/Q`. If not, the plugin was not successfully registered.

### I/Q UI settings

I/Q now exposes a plugin options panel at **Plugins → Plugin Options → I/Q** for dockable-focused settings:

- Maximum retained log lines for the server-log and PIDE-markup panels
- Maximum retained explore output messages
- Log auto-scroll toggle
- Explore argument auto-fill behavior
- Verbose explore debug logging toggle

### Connecting to I/Q (Raw)

I/Q listens out for MCP clients on port 8765. The provided [iq_bridge.py](iq_bridge.py) provides a bridge to stdin/stdout. For example, either

```
echo '{"jsonrpc": "2.0", "method": "tools/call", "id": "test", "params": {"name": "list_files", "arguments": {}}}' | python3 ./iq_bridge.py
```

or

```
echo '{"jsonrpc": "2.0", "method": "tools/call", "id": "test", "params": {"name": "list_files", "arguments": {}}}' | nc localhost 8765
```

should give you a JSON reply with all tracked. theory files.

## Security configuration

I/Q now defaults to a hardened local-only posture:

- Loopback bind by default (`IQ_MCP_BIND_HOST=127.0.0.1`).
- Remote bind is blocked unless explicitly enabled (`IQ_MCP_ALLOW_REMOTE_BIND=true`).
- Optional request authentication token (`IQ_MCP_AUTH_TOKEN`).
- Read-oriented tools (`list_files`, `read_file`, `get_command_info`, `get_document_info`, `open_file`, `explore`) are restricted to allowed read roots.
- Mutating tools (`open_file` with `create_if_missing=true`, `create_file`, `write_file`, `save_file`) are restricted to allowed mutation roots.
- `get_command_info` with `xml_result_file` is also treated as a mutating operation and must target an allowed mutation root.

Use these environment variables to configure behavior:

- `IQ_MCP_BIND_HOST`: Host/IP to bind to (default: `127.0.0.1`).
- `IQ_MCP_ALLOW_REMOTE_BIND`: Set to `true` to allow non-loopback bind hosts (default: `false`).
- `IQ_MCP_AUTH_TOKEN`: If set, every JSON-RPC request must include top-level `auth_token` matching this value.
- `IQ_MCP_ALLOWED_ROOTS`: Path-list of allowed mutation roots (separator: `:` on Unix). If unset, defaults to the current working directory.
- `IQ_MCP_ALLOWED_READ_ROOTS`: Path-list of allowed read roots (separator: `:` on Unix). If unset, defaults to `IQ_MCP_ALLOWED_ROOTS`.
- `IQ_MCP_MAX_CLIENT_THREADS`: Maximum concurrent MCP client handler threads (default: `16`, minimum `2`).

The bundled `iq_bridge.py` automatically forwards `IQ_MCP_AUTH_TOKEN` as `auth_token` on outgoing requests, enforces socket read timeouts, and supports log-file rotation:

- `IQ_MCP_BRIDGE_RESPONSE_TIMEOUT_SEC` (default: `30`)
- `IQ_MCP_BRIDGE_LOG_MAX_BYTES` (default: `5242880`)
- `IQ_MCP_BRIDGE_LOG_FILE` (default: `iq/bridge_log.txt`)

### Connecting to I/Q via an MCP client

If you connect to I/Q via an MCP-capable AI agent, you should see it learn and use the MCP interface automatically. For example, if you have [Amazon Q](https://aws.amazon.com/q/) installed and the I/Q MCP server registered as above, you should see the following:

```bash
% q chat
✓ iq loaded in 0.36 s
...
🤖 You are chatting with {MODEL}

> List the names of all theory files currently open in Isabelle
...
> I'll list all the theory files currently open in Isabelle using the I/Q MCP interface.

🛠️  Using tool: list_files from mcp server iq
 ⋮
 ● Running list_files with the param:
 ⋮  {
 ⋮    "arguments": {
 ⋮      "filter_open": true,
 ⋮      "filter_theory": true
 ⋮    },
 ⋮    "name": "list_files"
 ⋮  }

Allow this action? Use 't' to trust (always allow) this tool for the session. [y/n/t]:

> t

 ⋮
 ● Completed in 0.167s


> Here are all the theory files currently open in Isabelle:

... LIST ...

You have XXX theory files open in total, ...
```

## MCP Tools

1. **list_files**: List all files tracked by Isabelle with filtering and sorting options
2. **get_command_info**: Get detailed command information including status, errors, and proof states
3. **get_document_info**: Comprehensive theory file status with error/warning details
4. **open_file**: Open or create files in Isabelle/jEdit with optional content initialization
5. **create_file**: Create a new file with content and optionally open it in a view
6. **read_file**: Read file content with line range and pattern search support
7. **write_file**: Write or modify content in theory files with multiple edit modes (str_replace, insert, line replacement)
8. **explore**: Non-invasive proof exploration (sledgehammer, find_theorems, proof attempts)
9. **save_file**: Save one file or all modified open files

## Behavioral Guidance

For effective use with AI assistants, consider developing textual guidance on how to use I/Q.
You find an example in [iq_guidance.md](iq_guidance.md). If you find ways to improve/refine
this guidance, please let us know!
