# I/R Docker Images

See [ir/README.md](../README.md) for usage instructions.

## Dockerfiles

| File                    | Description                              |
|-------------------------|------------------------------------------|
| `Dockerfile`            | Uses local checkout via `COPY`           |
| `Dockerfile.standalone` | Clones from GitHub (self-contained)      |

## Build Args (Dockerfile.standalone)

| Arg                    | Default                                          |
|------------------------|--------------------------------------------------|
| `AUTOCORRODE_BRANCH`   | `main`                                           |
| `AUTOCORRODE_REPO`     | `https://github.com/awslabs/autocorrode.git`     |

## Build and Run

```bash
# Local checkout
docker build -t explore-repl:local -f ir/docker/Dockerfile .
docker run --rm -it -p 9148:9148 explore-repl:local

# Standalone
docker build -t explore-repl:standalone -f ir/docker/Dockerfile.standalone .
docker run --rm -it -p 9148:9148 explore-repl:standalone

# From a fork/branch
docker build -t explore-repl:standalone -f ir/docker/Dockerfile.standalone \
  --build-arg AUTOCORRODE_REPO=https://github.com/user/autocorrode.git \
  --build-arg AUTOCORRODE_BRANCH=my-branch .
```
