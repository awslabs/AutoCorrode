# Isabelle/REPL (I/R)

Isabelle/REPL (I/R) provides a REPL as an interactive and programmatic interface to Isabelle/ML. Its primary purpose is
to enable autonomous agentic proof development without Isabelle/Scala in the loop.

I/R manages a set of REPLs, each basically a list of Isar texts; you push/pop Isar to/from a REPL to explore proofs.
REPLs can be rooted in theories, locations within theories (assuming a suitably augmented heap build, see [Recorded
Segments](#recorded-segments-forking-repls-at-arbitrary-theory-points)), or at points within other REPLs (for sub-proof
exploration).

An MCP wrapper ([mcp_server.py](mcp_server.py)) is provided exposing I/R to AI agents. See [Agent Integration](#agent-integration).

## Quick Start

Requires: Isabelle, Python 3, and `pip install -r ir/requirements.txt`.

```bash
python3 ./ir/repl.py \
  --isabelle /path/to/Isabelle/bin/isabelle \
  --session HOL --mcp
```

You should see:

```
Starting Bash.Server...
● Bash.Server ready at 127.0.0.1:64595
Starting Isabelle ML_process (session=HOL)...
  Loading heap + ML_Repl...
● ML_Repl ready on 127.0.0.1:9146
IR_Repl.token: <token>
● REPL ready. Waiting for connections on 127.0.0.1:9147
Starting MCP server...
[MCP] INFO:     Uvicorn running on http://127.0.0.1:9148 (Press CTRL+C to quit)
● MCP server started
```

## Try It

```
%> Ir.theories ();
  ... list of theories in HOL ...

%> Ir.init "R" ["Main"];
Created REPL "R", set as current

%> Ir.step "lemma dummy: True";
proof (prove)
goal (1 subgoal):
 1. True

%> Ir.sledgehammer 5;
simp: Try this: by simp (0.1 ms)
...

%> Ir.step "by simp";
theorem dummy: True

%> Ir.find_theorems 5 "name: conjI";
displaying 4 theorem(s):
HOL.conjI: [| ?P; ?Q |] ==> ?P & ?Q
...
```

## Agent Integration

Point your MCP client at `http://localhost:9148/mcp`. For example,
in a Kiro CLI agent config:

```json
{
  "mcpServers": {
    "i/r": {
      "type": "http",
      "url": "http://localhost:9148/mcp",
      "description": "Isabelle Isar REPL",
      "timeout": 300000
    }
  }
}
```

> **Note:** The `timeout` (in milliseconds) should be set high enough
> for long-running operations like `sledgehammer` (default is 120000 = 2 min;
> 300000 = 5 min is recommended).

When an MCP client connects successfully, you should see:

```
[MCP] Created new transport with session ID: 8794bd96a57a434daabd19c95591782b
[MCP] INFO:     127.0.0.1:64675 - "POST /mcp HTTP/1.1" 200 OK
[MCP] INFO:     127.0.0.1:64676 - "POST /mcp HTTP/1.1" 202 Accepted
[MCP] INFO:     127.0.0.1:64676 - "GET /mcp HTTP/1.1" 200 OK
[MCP] INFO:     127.0.0.1:64677 - "POST /mcp HTTP/1.1" 200 OK
[MCP] Processing request of type ListToolsRequest
[MCP] INFO:     127.0.0.1:64677 - "POST /mcp HTTP/1.1" 200 OK
[MCP] Processing request of type ListPromptsRequest
```

## Security

All TCP listeners bind exclusively to `127.0.0.1` (localhost).

**Token authentication:** TCP clients must send the authentication token as the first line after connecting. The server responds with `OK\n` on success or `ERR: authentication failed\n` on failure. The token is printed to stdout on startup (`IR_Repl.token: <token>`).

Environment variables:

- `IR_AUTH_TOKEN`: Authentication token for the I/R daemon TCP server (default: randomly generated). Clients (including IRClient) must send this as the first line after connecting.
- `IR_REPL_AUTH_TOKEN`: Authentication token for the ML_Repl TCP connection (used with `--expect-ml`).

**MCP server authentication:** The MCP server (port 9148) does not have HTTP-level authentication. Instead, MCP clients must call the `connect` tool with the I/R daemon token (from `IR_AUTH_TOKEN` or printed on startup) before any other tool will function. Tools called before `connect` return an error.

**Threat model:** The security model aims to protect against unauthorized access from remote hosts and from other local OS users. It does not try to protect against malicious processes running as the same OS user.

## Management Console

When running in interactive mode, the operator gets a management console on stdin/stdout.
Lines starting with `/` are management commands; everything else is sent to the REPL directly.

Available commands:

- `/connections` — Show open client connections with stats
- `/info` — Show server status summary (session, ports, uptime, clients, verbosity)
- `/verbosity [N]` — Set verbosity 0–3 (0=off, 1=non-empty, 2=all messages, 3=all+hex). Without argument, cycles through levels.
- `/show_types` — Toggle display of type annotations in output
- `/quit` — Shut down the server
- `/help` — Show available commands

## Daemon Mode

In daemon mode, the management console is served on a Unix socket instead of stdin/stdout,
allowing the server to run in the background:

```bash
python3 ./ir/repl.py --daemon [options]
```

Connect to the management console of a running daemon:

```bash
python3 ./ir/repl.py --attach
```

Stop a running daemon:

```bash
python3 ./ir/repl.py --kill-daemon
```

## Recorded Segments: Forking REPLs at Arbitrary Theory Points

By default, `Ir.init` creates a REPL at the end of a theory.
To fork REPLs at intermediate points (e.g. after a specific lemma,
or within a proof), you need the intermediate proof states recorded
in the heap. This uses the `record_theories` option available in
Isabelle2025-2 or later.

### Setup

Build the heap with `record_theories=true`:

```bash
isabelle build -b -o record_theories=true -d /path/to/session My_Session
```

Note: this increases heap size by approximately 5x (according to Isabelle2025-2 NEWS).

### Usage

Load the session into the REPL:

```bash
python3 ./ir/repl.py \
  --isabelle /path/to/Isabelle/bin/isabelle \
  --session My_Session --dir /path/to/session
```

On startup, you should see `source commands available` instead of
`source commands not available`.

Browse and fork from recorded segments:

```
%> Ir.source "My_Session.My_Theory" 0 ~1;
   0  theory My_Theory imports Main begin
   2  lemma foo: "True"
   4    by simp
   6  lemma bar: "1 + 1 = (2::nat)"
   8    by simp
  10  end

%> Ir.init "R" ["My_Session.My_Theory:6"];
Created REPL "R", set as current
```

The REPL is now rooted at segment 6 (after `lemma bar`), with all
prior definitions and lemmas available.

### I/Q Integration

Here's the high-level overview of the different components coming
together when I/R is integrated into Isabelle/Scala and I/Q:

```
┌──────────────────────────────────────────────────────────────┐
│                  Isabelle/jEdit + Scala                      │
│                                                              │
│  ┌──────────────┐   ┌───────────────────┐                    │
│  │ I/Q Plugin   │   │ I/R Client        │                    │
│  │ (IQPlugin)   │   │ (IRClient, Scala) │                    │
│  └──┬───┬───────┘   └────┬──────────────┘                    │
│     │   │                │                                   │
│     │   │            (5) │ TCP                               │
│     │   │                │ connect                           │
│     │   │                │                                   │
└─────┼───┼────────────────┼───────────────────────────────────┘
      │   │                │
      │   │                │
      │ (1) "IR_Repl.start"│
      │ (8) "IR_Repl.stop" │
      │   │                │
      │   ▼                │
┌─────┼───────────────────────────────────────────────────────────────┐
│     :               Isabelle/ML                                     │
│     :          (Poly/ML session process)                            │
│     :                    :                                          │
│     :                    :  ┌──────────────────────────────────┐    │
│     :                    :  │  Isabelle Prover                 │    │
│     :                    :  │  (HOL, tactics, sledgehammer)    │    │
│     :                    :  └──────────────▲───────────────────┘    │
│     :                    :                 │ (6c) Isar commands     │
│     :                    :                 │      evaluated by      │
│     :                    :                 │      prover kernel     │
│     :                    :  ┌──────────────┴───────────────────┐    │
│     :                    :  │  I/R  (ir.ML)                    │    │
│     :                    :  │  REPL management: init, step,    │    │
│     :                    :  │  fork, merge, state, replay, ... │    │
│     :                    :  └──────────────▲───────────────────┘    │
│     :                    :                 │ (6b) Ir.* commands     │
│     :                    :                 │      dispatched        │
│     :                    :  ┌──────────────┴───────────────────┐    │
│     :                    :  │  ML_Repl (ml_repl.ML)            │    │
│     :                    :  │  TCP listener (token-auth)       │    │
│     :                    :  │  ◄── (1) started by IR_Repl.start│    │
│     :                    :  │  ◄── (8) stopped by IR_Repl.stop │    │
│     :                    :  └──────────────▲───────────────────┘    │
│     :                    :                 │                        │
└─────┼────────────────────┼─────────────────┼────────────────────────┘
      │                    │                 │
      │ (2) spawns         │             (3) │ TCP :9146
      │                    │                 │ daemon connects
      ▼                    ▼                 │
┌───────────────────────────────────────────────────────────────┐
│              I/R REPL Daemon  (repl.py --daemon)              │
│                                                               │
│  ┌──────────────────┐  ┌───────────────┐  ┌───────────────┐   │
│  │ I/R REPL TCP     │  │ Connection    │  │ I/R Mgmt      │   │
│  │ Server           │  │ to ML_Repl    │  │ Console       │   │
│  │ (token-auth)     │  │ (token-auth)  │  │ (Unix socket) │   │
│  └────────┬─────────┘  └───────────────┘  └──────┬────────┘   │
│           │                                      │            │
│       (4) │ spawns                               │            │
│           ▼                                      │            │
│  ┌──────────────────┐                            │            │
│  │ I/R MCP Server   │                            │            │
│  │ (:9148)          │                            │            │
│  └──────────────────┘                            │            │
│           │                                      │            │
└───────────┼──────────────────────────────────────┼────────────┘
            │ MCP                                  │ Unix socket
            ▼                                      ▼
      ┌──────────────────┐               ┌───────────────────┐
      │  I/R MCP Client  │               │     repl.py       │
      │  (e.g. Claude,   │               │ Management console│
      │    Bedrock)      │               │    (Debugging)    │
      └──────────────────┘               └───────────────────┘

Startup:
  (1) I/Q sends "IR_Repl.start" → ML_Repl opens token-authenticated
      TCP REPL (port dynamically assigned)
  (2) I/Q spawns repl.py --daemon, passing ML_Repl token
      via IR_REPL_AUTH_TOKEN env var.  The daemon generates
      its own client-facing token and prints it to stdout.
  (3) repl.py daemon authenticates with ML_Repl via token,
  (4) repl.py daemon multiplexes raw TCP REPL into
      - TCP (token-auth, default port 9147)
      - MCP (optional, via --mcp)
      - Management Console (Unix socket)
  (5) I/Q reads the daemon token from stdout, then IRClient
      authenticates with daemon via token on TCP;
      I/R functionality wrapped in Scala API

Command flow:
  (6a) IRClient sends command to daemon via TCP
       → daemon forwards to ML_Repl
  (6b) ML_Repl dispatches Ir.* commands to I/R module
  (6c) I/R evaluates Isar commands via the prover kernel
  (6d) Output channels (normally directed at Isabelle/Scala)
       redirected to repl.py; still via PIDE
```
