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
