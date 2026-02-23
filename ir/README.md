# I/R: Interactive/Remote Isabelle REPL

I/R is a TCP server wrapping an Isabelle/Poly/ML console with the
Explore REPL, plus an MCP server for AI agent integration.

It loads a pre-built Isabelle heap and lets you spawn REPLs rooted at
theories. You then push/pop Isar commands to explore proofs interactively
or via an agent.

If you add a build hook (see `segment_storage.ML`) to store intermediate
proof states in the heap, you can also fork REPLs at arbitrary points
in a theory.

## Quick Start

### Option A: Docker (no prerequisites)

```bash
docker build -t explore-repl:standalone -f ir/docker/Dockerfile.standalone .
docker run --rm -it -p 9148:9148 explore-repl:standalone
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
Loading .../explore.ML...
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
%> Explore.theories ();
  ... list of theories in HOL ...

%> Explore.init "R" ["Main"];
Created REPL "R", set as current

%> Explore.step "lemma dummy: True";
proof (prove)
goal (1 subgoal):
 1. True

%> Explore.sledgehammer 5;
simp: Try this: by simp (0.1 ms)
...

%> Explore.step "by simp";
theorem dummy: True

%> Explore.find_theorems 5 "name: conjI";
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
      "url": "http://localhost:9148/mcp"
    }
  }
}
```

The agent must call `connect` before using any other tool.

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

## Stored Segments: Forking REPLs at Arbitrary Theory Points

By default, `Explore.init` creates a REPL at the end of a theory.
To fork REPLs at intermediate points (e.g. after a specific lemma,
or within a proof), you need to store the intermediate proof states in the heap using
`segment_storage.ML`.

### Setup

1. **Register the option.**
   Add to `$ISABELLE_HOME_USER/etc/options`:

   ```
   option store_segments : bool = false for build
   ```

   See `ir/Segment_Storage_Example/` for a complete working example.

2. **Load `segment_storage.ML` in your session's root theory.**
   It must be loaded with `ML_write_global` enabled:

   ```isabelle
   theory My_Session
   imports Main
   begin
   declare [[ML_write_global = true]]
   ML_file \<open>segment_storage.ML\<close>
   declare [[ML_write_global = false]]
   (* ... rest of your theory ... *)
   end
   ```

3. **Build the heap with `store_segments=true`:**

   ```bash
   isabelle build -b -o store_segments=true -d /path/to/session My_Session
   ```

   You should see lines like:

   ```
   Segment_Storage: My_Session.My_Theory (24 segments) [STORING]
   ```

### Usage

Load the session into the REPL:

```bash
python3 ./ir/repl.py \
  --isabelle /path/to/Isabelle/bin/isabelle \
  --session My_Session --dir /path/to/session
```

On startup, you should see `source commands available` instead of
`source commands not available`.

Browse and fork from stored segments:

```
%> Explore.source "My_Session.My_Theory" 0 ~1;
   0  theory My_Theory imports Main begin
   2  lemma foo: "True"
   4    by simp
   6  lemma bar: "1 + 1 = (2::nat)"
   8    by simp
  10  end

%> Explore.init "R" ["My_Session.My_Theory:6"];
Created REPL "R", set as current
```

The REPL is now rooted at segment 6 (after `lemma bar`), with all
prior definitions and lemmas available.
