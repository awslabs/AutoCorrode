# Explore REPL Docker Image

Docker image running the Isabelle/REPL (I/R) REPL with an MCP server for
agentic AI integration.

## Quick Start

From the repository root:

```bash
# Build and run (finch)
finch build -t autocorrode-ir:latest -f ir/docker/Dockerfile . && \
finch run --rm -it -p 9148:9148 autocorrode-ir:latest

# Build and run (docker)
docker build -t autocorrode-ir:latest -f ir/docker/Dockerfile . && \
docker run --rm -it -p 9148:9148 autocorrode-ir:latest
```

The container starts an interactive REPL on the terminal and an MCP server on port 9148.

## Standalone Image (no checkout needed)

`Dockerfile.standalone` clones from GitHub instead of requiring a local checkout:

```bash
docker build -t explore-repl:latest -f ir/docker/Dockerfile.standalone . && \
docker run --rm -it -p 9148:9148 explore-repl:latest
```

To build from a specific branch:

```bash
docker build --build-arg AUTOCORRODE_BRANCH=my-branch \
  -t explore-repl:latest -f ir/docker/Dockerfile.standalone .
```

## Connecting an MCP Client

Point your MCP client at `http://localhost:9148/mcp` (Streamable HTTP transport).

Example Kiro CLI agent config:

```json
{
  "mcpServers": {
    "explore": {
      "url": "http://localhost:9148/mcp"
    }
  }
}
```

## Environment Variables

| Variable   | Default | Description          |
|------------|---------|----------------------|
| `MCP_PORT` | `9148`  | MCP server port      |

## Dockerfiles

| File                    | Description                              |
|-------------------------|------------------------------------------|
| `Dockerfile`            | Uses local checkout via `COPY`           |
| `Dockerfile.standalone` | Clones `ir/` from GitHub (self-contained)|
