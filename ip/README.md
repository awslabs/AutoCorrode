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

The `setup` subcommand installs AFP components on the remote by default (`Word_Lib`).
You can override this with the `--components` flag. For example,
`--components Word_Lib Isabelle_C` would install both `Word_Lib` and `Isabelle_C`.
To skip AFP installation entirely, pass `--components` with no arguments.
Note: `--components` is only available on the `setup` subcommand, not `run`.

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

## Heap management

To make effective use of I/P on a single project, you need to maintain multiple
checkouts/worktrees that the difference local/proxied Isabelle instances are run on. However,
multiple worktrees stand in conflicts with the default of a single (ML-platform, session)-indexed
heap storage.

### Changing the heap store

As a remedy, you can consider putting the following in your local `etc/settings`:

```
if [ -n "$ISABELLE_HEAP_BASE" ]; then
  ISABELLE_HEAPS="$ISABELLE_HEAP_BASE/heaps"
fi

if [ -n "$ISABELLE_HEAP_SUFFIX" ]; then
  ISABELLE_HEAPS="$ISABELLE_HEAPS-$ISABELLE_HEAP_SUFFIX"
fi
```

With this, if you set the environment variable `ISABELLE_HEAP_SUFFIX` prior to starting Isabelle,
then the provided suffix will be added to the default heap directory. For example, with
`ISABELLE_HEAP_SUFFIX=A`, heaps will be looked up and stored in `$ISABELLE_HOME_USER/heaps-A`
instead of the default `$ISABELLE_HOME_USER/heaps`.

If you even want to change the base directory to something other than `$ISABELLE_HOME_USER`, the
above would allow you to do so by setting `$ISABELLE_HEAP_BASE`.

This allows you to maintain multiple heap stores and manually switch between them.
In particular, when working with multiple worktrees, you could use different heap stores per
worktree.

### Avoiding absolute file paths in heaps

A downside that remains with the above is that different worktrees cannot _share_ their heaps:
This is because filenames enter the heap largely unmodified, except for symbolic replacement of the
user home directory and Isabelle home directory: For example, a theory with absolute path
`/home/alice/foo.thy` would be stored in the heap DB as `~/foo.thy`.

Luckily, the set of file path contractions is extensible: If you put

```
if [ -n "$ISABELLE_PROJECT_BASE" ]; then
  isabelle_directory '$ISABELLE_PROJECT_BASE'
fi

if [ -n "$AFP_COMPONENT_BASE" ]; then
  isabelle_directory '$AFP_COMPONENT_BASE'
fi
```

in your `settings`, for example, any path starting with the expanded forms of
`$ISABELLE_PROEJCT_HOME` or `$AFP_COMPONENT_BASE` would be contracted to the symbolic file names
starting with `$ISABELLE_PROJECT_HOME/` or `$AFP_COMPONENT_BASE/`, respectively. In particular, if
you set these environment variables to the base directories of your checkouts (and potentially their
individual component directories, in case they are duplicate), then the generated heaps won't have
worktree-specific filenames in them anymore and are therefore amenable for reuse across worktrees.

### Finding a suitable heap

With the above changes to `etc/settings`, you can manage multiple heap stores that can be shared
between worktrees. However, it remains a bit cumbersome to know which heap to use when.

To help this, two scripts are provided:

* [`heap-db-inspect`](heap-db-inspect): This takes the path of of `.db` heap database file, and prints the paths of
  files in the respective image. You can use this to check whether the path contractions have worked
  as intended.

* [`heap-mgr`](heap-mgr): This helps to manage multiple heap directories, and in particular finding
  the heap directory that matches a given `isabelle build ...` or `isabelle jedit ...` command most
  closely.

### TL;DR: Example `etc/settings`

```
if [ -n "$ISABELLE_HEAP_BASE" ]; then
  ISABELLE_HEAPS="$ISABELLE_HEAP_BASE/heaps"
fi

if [ -n "$ISABELLE_HEAP_SUFFIX" ]; then
  ISABELLE_HEAPS="$ISABELLE_HEAPS-$ISABELLE_HEAP_SUFFIX"
fi

if [ -n "$ISABELLE_PROJECT_BASE" ]; then
  isabelle_directory '$ISABELLE_PROJECT_BASE'
fi

if [ -n "$AFP_COMPONENT_BASE" ]; then
  isabelle_directory '$AFP_COMPONENT_BASE'
fi
```
