# Isabelle/REPL (I/R)

Isabelle/REPL (I/R) provides a REPL as an interactive and programmatic interface to Isabelle/ML. Its primary purpose is
to enable autonomous agentic proof development without Isabelle/Scala in the loop.

I/R manages a set of REPLs, each basically a list of Isar texts; you push/pop Isar to/from a REPL to explore proofs.
REPLs can be rooted in theories, locations within theories (assuming a suitably augmented heap build, see [Recorded
Segments](#recorded-segments-forking-repls-at-arbitrary-theory-points)), or at points within other REPLs (for sub-proof
exploration).

An MCP wrapper ([mcp_server.py](mcp_server.py)) is provided exposing I/R to AI agents. See [Agent Integration](#agent-integration).

## Quick Start

### Option A: Docker (no prerequisites)

```bash
docker build -t isabelle-repl:standalone -f ir/docker/Dockerfile.standalone .
docker run --rm -it -p 9148:9148 isabelle-repl:standalone
```

### Option B: Local

Requires: Isabelle, Python 3, and `pip install -r ir/requirements.txt`.

```bash
python3 ./ir/repl.py \
  --isabelle /path/to/Isabelle/bin/isabelle \
  --session HOL --mcp
```

Either way, you should see:

```
Starting Bash.Server...
● Bash.Server ready at 127.0.0.1:64595
Starting Isabelle console (session=HOL)...
● Isabelle console ready.
Loading .../ir.ML...
● REPL ready. Waiting for connections on 127.0.0.1:9147
Starting MCP server...
[MCP] INFO:     Started server process [4002]
[MCP] INFO:     Waiting for application startup.
[MCP] StreamableHTTP session manager started
[MCP] INFO:     Application startup complete.
[MCP] INFO:     Uvicorn running on http://0.0.0.0:9148 (Press CTRL+C to quit)
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
│     :                    :  │  TCP listener :9146              │    │
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
│  │ Server (:9147)   │  │ to ML_Repl    │  │ Console       │   │
│  │                  │  │ (:9146)       │  │ (Unix socket) │   │
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
      │  (e.g. Claude,   │               │ Mangement console │
      │    Bedrock)      │               │    (Debugging)    │
      └──────────────────┘               └───────────────────┘

Startup:
  (1) I/Q sends "IR_Repl.start" → ML_Repl opens single TCP REPL at :9146
  (2) I/Q spawns repl.py --daemon
  (3) repl.py daemon connects to ML_Repl on :9146,
  (4) repl.py daemon multiplexes raw TCP REPL into
      - TCP (:9147)
      - MCP (:9148)
      - Management Console (:socket)
  (5) IRClient connects to daemon on :9147 via TCP;
      I/R functionality wrapped in Scala API IRScala

Command flow:
  (6a) IRClient sends command to daemon via :9147
       → daemon forwards to ML_Repl via :9146
  (6b) ML_Repl dispatches Ir.* commands to I/R module
  (6c) I/R evaluates Isar commands via the prover kernel
  (6d) Output channels (normally directed at Isabelle/Scala)
       redirected to repl.py; still via PIDE
```
