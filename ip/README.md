# I/P — Isabelle/Proxy

I/P runs the Isabelle ML prover on a remote machine while keeping
Isabelle/jEdit local. No Isabelle source changes are required.

## Overview

I/P consists of three components:

- **`ml_proxy.py`** — PIDE protocol proxy that interposes between the local
  Scala/jEdit and a remote Poly/ML process. Handles path rewriting,
  Bash.Server forwarding, ML statistics monitoring, and PIDE message
  interception.
- **`configure-remote.py`** — Setup and configuration tool. Installs Isabelle
  on the remote, syncs poly binaries and heaps, and generates the jEdit
  flags needed to enable the proxy.
- **`ip_plugin/`** — Isabelle/jEdit plugin providing a status bar widget
  (remote host + throughput) and ML heap monitoring for proxied sessions.

## Quick Start

```bash
# 1. Install Isabelle on the remote and sync heaps
./configure-remote.py setup ubuntu@host --ml-platform aarch64-ubuntu \
  --local-isabelle-home YOUR_ISABELLE_INSTALLATION

# 2. Add the shell helper to .zshrc / .bashrc, replacing AUTOCORRODE_HOME accordingly:

isabelle-remote() {
  local flags
  flags=$($AUTOCORRODE_HOME/ip/configure-remote.py run "$@") || return 1
  ISABELLE_REMOTE="$flags"
  echo ""
  echo "ISABELLE_REMOTE set to the following flags:"
  echo "-------------------------------------------"
  echo "$ISABELLE_REMOTE"
}

# 3. Configure and launch jEdit with the remote prover
isabelle-remote ubuntu@host
isabelle jedit -l HOL $ISABELLE_REMOTE
```

## Setup Scripts

- `setup_ubuntu.sh` — Installs Isabelle on a remote Ubuntu/Debian host (aarch64 or x86_64).
- `setup_al2.sh` — Installs Isabelle on a remote Amazon Linux 2
   host, building Poly/ML from source (to avoid glibc versioning issue).

## Poly/ML Tuning

The proxy supports overriding Poly/ML runtime options:

```bash
isabelle-remote ubuntu@host --minheap 48000 --maxheap 80000 --threads 16
```

See `configure-remote.py --help` and the module docstring of `ml_proxy.py`
for full documentation.
