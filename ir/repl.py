#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

"""Dispatch shell for the I/R REPL.

This is a thin front door that routes to one of two modules, so a one-shot
client call pays nothing for the server's heavy machinery:

  * `repl.py cli ...`  -> repl_cli.py  — a tiny one-shot TCP client (connect,
                          send one command, print the reply, exit). Imports only
                          stdlib essentials, so it runs near the Python startup
                          floor. `cli help` lists the verbs.

  * anything else      -> repl_srv.py  — the full I/R REPL server + management
                          console (Isabelle/Poly/ML, --daemon, --attach,
                          --show-server, ...). Its heavy imports and class
                          bodies only execute on this path.

The split matters because `cli` is invoked per-call from a shell, paying a fresh
interpreter each time; routing on argv BEFORE importing repl_srv keeps that path
from executing the ~2700-line server module.

Usage:
    python3 repl.py [--port PORT] [--isabelle PATH] [--session SESSION] [--dir DIR]
    python3 repl.py --daemon [...]   Start in daemon mode (mgmt console on Unix socket)
    python3 repl.py --attach         Connect to a running daemon's mgmt console
    python3 repl.py cli VERB [...]   One-shot client: send one command, print the
                                     reply, exit. `cli help` lists the verbs.
"""

import sys


def main():
    if len(sys.argv) >= 2 and sys.argv[1] == "cli":
        import repl_cli
        repl_cli.main(sys.argv[2:])   # always exits
    else:
        import repl_srv
        repl_srv.main()


if __name__ == "__main__":
    main()
