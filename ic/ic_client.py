#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: MIT

"""I/C Client: CLI for checking Isabelle theory files via I/R REPL.

Usage:
    python3 ic_client.py check /path/to/File.thy
    python3 ic_client.py check /path/to/File.thy -j 6 -v
    python3 ic_client.py clean
"""

import argparse
import json
import os
import sys

from ic_repl import ReplClient
from ic_core import DiamondStrategy
from ic_check import check, clean, print_heapdiff, remote_prover
from ic_status import status


def print_response(response: dict | None) -> bool:
    """Pretty-print response. Returns True if there were errors."""
    if not response:
        print("No response", file=sys.stderr)
        return True

    has_errors = False

    if response.get("status") == "error":
        print(f"Error: {response.get('error', 'unknown')}", file=sys.stderr)
        has_errors = True

    if response.get("dry_run"):
        return False

    if "target" in response:
        target = response["target"]
        deps = response.get("dependencies", [])
        # Only print dependencies that have problems
        for dep in deps:
            res = dep.get("resolution", "?")
            name = dep.get("name", "?")
            if res == "from_file" and dep.get("status") == "error":
                path = dep.get("path", name)
                print(f"  ERR  {name}: {dep.get('error', '')}")
                print(f"       try: ic_client.py check {path}")
                has_errors = True
            elif res == "repl" and dep.get("status") == "error":
                line = dep.get("line")
                loc = f":{line}" if line else ""
                print(f"  ERR  {name}{loc}: {dep.get('error', '')}")
                has_errors = True
            elif res == "stale":
                reason = dep.get("reason", "")
                print(f"  ---  {name}  (stale: {reason})")
        # Print target
        t_name = target.get("name", "?")
        t_status = target.get("status", "?")
        if t_status == "ok":
            print(f"  OK   {t_name}")
        elif t_status == "error":
            line = target.get("line")
            loc = f":{line}" if line else ""
            print(f"  ERR  {t_name}{loc}: {target.get('error', '')}")
            has_errors = True
        elif t_status == "stale":
            reason = target.get("reason", "")
            print(f"  ---  {t_name}  (stale: {reason})")
            has_errors = True
        else:
            print(f"  {t_status.upper():>3}  {t_name}")

    elif "message" in response:
        print(response["message"])

    elif response.get("status") == "ok" and len(response) == 1:
        print("OK")

    elif not has_errors:
        print(json.dumps(response, indent=2))

    if response.get("parse_errors"):
        print("\nParse errors:")
        for pe in response["parse_errors"]:
            print(f"  {pe['path']}: {pe['error']}")

    return has_errors


def main():
    p = argparse.ArgumentParser(
        description="I/C: Isabelle/Check — file-oriented proof checking via I/R")
    p.add_argument("--repl-host", default="127.0.0.1",
                   help="I/R REPL host (default: 127.0.0.1)")
    p.add_argument("--repl-port", type=int, default=9147,
                   help="I/R REPL port (default: 9147)")
    p.add_argument("--repl-token",
                   default=os.environ.get("IR_AUTH_TOKEN"),
                   help="I/R REPL auth token (default: $IR_AUTH_TOKEN)")
    p.add_argument("-q", "--quiet", action="store_true",
                   help="Suppress progress output")
    p.add_argument("-v", "--verbose", action="store_true",
                   help="Show extra detail")

    verbose_parent = argparse.ArgumentParser(add_help=False)
    verbose_parent.add_argument("-q", "--quiet", action="store_true",
                                default=argparse.SUPPRESS,
                                help="Suppress progress output")
    verbose_parent.add_argument("-v", "--verbose", action="store_true",
                                default=argparse.SUPPRESS,
                                help="Show extra detail")

    sub = p.add_subparsers(dest="command")

    check_p = sub.add_parser("check", help="Check a .thy file",
                              parents=[verbose_parent])
    check_p.add_argument("path", help="Path to .thy file")
    diamond_group = check_p.add_mutually_exclusive_group()
    diamond_group.add_argument("--resolve-deps-via-reload", dest="diamond_strategy",
                               action="store_const", const="reload",
                               help="Diamond deps: reload REPL'd theories from source")
    diamond_group.add_argument("--resolve-deps-via-repl", dest="diamond_strategy",
                               action="store_const", const="repl",
                               help="Diamond deps: step importing theories via REPL")
    diamond_group.add_argument("--resolve-deps-via-lines-heuristic", dest="diamond_strategy",
                               action="store_const", const="heuristic",
                               help="Diamond deps: choose based on line count (default)")
    check_p.set_defaults(diamond_strategy=None)
    check_p.add_argument("-j", "--jobs", type=int, default=1,
                         help="Number of parallel jobs (default: 1)")
    check_p.add_argument("--timeout", type=int, default=0,
                         help="Per-step timeout in seconds (default: 0 = use I/R default)")
    check_p.add_argument("--always-stepwise", action="store_true",
                         help="Never use Ir.load_theory for file deps (for remote I/R)")
    check_p.add_argument("--dry-run", action="store_true",
                         help="Print plan table without executing")

    sub.add_parser("clean", help="Remove all ic.* REPLs",
                    parents=[verbose_parent])
    sub.add_parser("status", help="Show I/C state (read-only)",
                    parents=[verbose_parent])
    heapdiff_p = sub.add_parser("heapdiff",
                    help="Show heap-vs-disk segment comparison",
                    parents=[verbose_parent])
    heapdiff_p.add_argument("path", help="Path to .thy file")

    args = p.parse_args()

    if not args.command:
        p.print_help()
        sys.exit(1)

    if getattr(args, 'quiet', False):
        verbose = 0
    elif getattr(args, 'verbose', False):
        verbose = 2
    else:
        verbose = 1

    repl = ReplClient(host=args.repl_host, port=args.repl_port,
                      token=args.repl_token)
    try:
        repl.connect()
    except ConnectionRefusedError:
        print(f"Error: no I/R REPL reachable at "
              f"{args.repl_host}:{args.repl_port}.",
              file=sys.stderr)
        sys.exit(1)
    except ConnectionError as e:
        print(f"Error: {e}. Pass the server's token via --repl-token "
              f"or $IR_AUTH_TOKEN (the I/R startup banner prints it as "
              f"'IR_Repl.token: ...').", file=sys.stderr)
        sys.exit(1)

    try:
        if args.command == "check":
            remote = remote_prover(repl)
            if remote and verbose >= 1:
                print(f"Connected to I/R running via I/P on remote: {remote}",
                      file=sys.stderr)
            elif remote is None and os.environ.get("ISABELLE_REMOTE"):
                print("Warning: $ISABELLE_REMOTE is set in this shell but "
                      "the I/R server reports it is running locally. The "
                      "env var has no effect on I/C — it only matters in "
                      "the shell that started I/R.", file=sys.stderr)
            always_stepwise = args.always_stepwise or remote is not None
            if args.diamond_strategy is None:
                diamond_strategy = (DiamondStrategy.REPL if always_stepwise
                                    else DiamondStrategy.HEURISTIC)
            else:
                diamond_strategy = DiamondStrategy(args.diamond_strategy)
                if always_stepwise and diamond_strategy != DiamondStrategy.REPL:
                    print("  --always-stepwise forces diamond strategy "
                          "to REPL", file=sys.stderr)
                    diamond_strategy = DiamondStrategy.REPL
            response = check(
                os.path.realpath(args.path),
                repl,
                diamond_strategy,
                verbose=verbose,
                pool_size=args.jobs,
                timeout=args.timeout,
                interactive=True,
                always_stepwise=always_stepwise,
                dry_run=args.dry_run,
            )
        elif args.command == "clean":
            response = clean(repl)
        elif args.command == "status":
            status(repl, verbose=verbose)
            sys.exit(0)
        elif args.command == "heapdiff":
            print_heapdiff(repl, os.path.realpath(args.path),
                           verbose=verbose)
            sys.exit(0)
        else:
            p.print_help()
            sys.exit(1)
        has_errors = print_response(response)
        sys.exit(1 if has_errors else 0)
    except EOFError as e:
        msg = str(e)
        if "authentication" in msg.lower():
            print(f"Error: I/R REPL rejected the connection "
                  f"({msg}). Pass the server's token via --repl-token "
                  f"or $IR_AUTH_TOKEN (the I/R startup banner prints it "
                  f"as 'IR_Repl.token: ...').", file=sys.stderr)
        else:
            print(f"Error: I/R REPL closed the connection unexpectedly: "
                  f"{msg}", file=sys.stderr)
        sys.exit(1)
    finally:
        repl.close()


if __name__ == "__main__":
    main()
