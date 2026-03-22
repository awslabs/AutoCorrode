# Isabelle/jEdit Proxy Plugin

Status bar widget and log panel for the Isabelle remote ML prover proxy.

## Features

- **Proxy status widget**: shows remote host and PIDE throughput (MB/s)
  in the jEdit status bar. Appears automatically when the proxy connects.
- **ML heap monitoring**: forwards remote Poly/ML runtime statistics to
  the built-in ML heap widget and Monitor panel.

## Architecture

The plugin registers a PIDE protocol handler that recognizes two
message types injected by `ml_proxy.py` into the ML→Scala stream:

- `proxy_ml_stats` — Poly/ML runtime statistics (heap, GC, threads),
  forwarded to `session.runtime_statistics` so the built-in ML heap
  widget and Monitor panel work with the remote prover.
- `proxy_log` — text log messages from the proxy (acknowledged by the handler).

Host and throughput information is obtained by polling a stats file
written by `ml_proxy.py` (not a PIDE protocol message).

The handler is registered from a background thread at plugin startup,
retrying until the PIDE session is available. The status bar widget is
added dynamically when the proxy is detected in the process policy.

## Build

Requires an Isabelle installation with jEdit and Scala.

```
make build                          # Build the JAR
make install                        # Build and install to ~/.isabelle/.../jedit/jars/
make clean                          # Remove build artifacts
make uninstall                      # Remove installed JAR
```

Override paths via environment variables:

```
ISABELLE_HOME=/path/to/Isabelle make install
```

## Files

- `src/ProxyPlugin.scala` — plugin entry point, protocol handler, shared state
- `src/ProxyStatusWidget.scala` — status bar widget with throughput progress bar
- `resources/plugin.props` — jEdit plugin metadata
- `resources/services.xml` — status bar widget factory registration
