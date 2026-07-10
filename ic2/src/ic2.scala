/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      ic2/src/ic2.scala

The single `isabelle ic2` tool. Dispatches to command groups:

  ic2 server start|stop|status     manage the headless PIDE daemon
  ic2 check [FILE...|status|attach|cancel]   run / inspect / control a check
  ic2 load-files FILE...           parse .thy files into the session graph
                                   without evaluating them
  ic2 query SUBTOOL ...             read-only diagnostics over the session
  ic2 repl-create FILE:LINE NAME    create an interactive I/R REPL

`server start` lives in Daemon; everything else lives in Client. This file is
just the front door: parse the (possibly nested) subcommand, hand the rest off.
*/

package isabelle.ic2

import isabelle._


object IC2 {

  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool("ic2", "headless PIDE daemon and client",
      Scala_Project.here, { args => run_tool(args) })

  private val usage_text: String = """
Usage: isabelle ic2 COMMAND [ARGS...]

  Headless PIDE daemon + client for iterative Isabelle theory development.
  A long-lived server holds one resident session; short-lived clients submit
  checks and query proof state over a Unix-domain socket.

  ============================== Typical loop ==============================

    1) Start the daemon once, backgrounded:

         isabelle ic2 server start --daemon -l HOL

    2) Type-check a theory against the resident session:

         isabelle ic2 check src/MyThy.thy

       ...or check only up to a specific source line:

         isabelle ic2 check src/MyThy.thy --line 42

    3) Inspect the document/proof state at any position:

         isabelle ic2 query state-at src/MyThy.thy --line 42
         isabelle ic2 query state-at src/MyThy.thy --pattern 'apply simp'

  ============================== Commands =================================

    server ...                 Manage the headless PIDE daemon.
      Variants:
        server start           start it (--daemon to background it)
        server stop            shut a server down
        server status          report a server (-n NAME), or survey all
        server attach          stream a backgrounded server's console log

    check [FILE...]            Type-check .thy files against the running
                               server; first-error stop; exit 0 on success.
      Variants (in place of FILE...):
        check status           report the current/last check's state
        check attach           stream the in-flight check to completion
        check cancel           cancel the in-flight check
      Options:
        --line N               check only the prefix of the (single) FILE
                               up to the command ending on or before source
                               line N; commands after N are left UNPROCESSED
        --detach               submit and return immediately (poll via
                               `check status` / `check attach`)

    query state-at FILE ...    Query document / proof state at a target
                               location. Location is FILE plus one of:
                                 --line N        source line, 1-based
                                 --offset K      character offset (from 0)
                                 --pattern TEXT  unique text pattern
                               If the position falls on whitespace or a
                               blank line, resolves to the last real
                               command ending on or before that position.
                               Reports: goal text + subgoal count, in-scope
                               free variables and constants, whether the
                               position is inside an open proof, and the
                               command's metadata.
                               Examples:
                                 ic2 query state-at Foo.thy --line 42
                                 ic2 query state-at Foo.thy --pattern 'by simp'
                               Use --json for the raw payload.

    repl-create FILE:LINE NAME Create a snapshot of the document / proof
                               state for out-of-document exploration:
                               forks an interactive I/R REPL at the given
                               source location. Prints the exact
                               `repl.py cli` commands to drive it
                               (step/state/text/...).

    query SUBTOOL [FILE] ...   Other read-only diagnostics over the session
                               (list-files, entities, sorry, proof-blocks,
                               diagnostics, command-info, ...).
                               `query help` for the full catalogue.

    load-files FILE...         Parse .thy files into the session's document
                               graph WITHOUT evaluating them. After loading,
                               `query` sees the theory shape (list-files,
                               entities, command-info, ...) at zero ML cost.

  ============================== Concrete flow ============================

    isabelle ic2 server start --daemon -l HOL
    isabelle ic2 check src/MyThy.thy                       # exit 0 = ok
    isabelle ic2 check src/MyThy.thy --line 87             # only up to 87
    isabelle ic2 query state-at src/MyThy.thy --line 87    # inspect goal
    isabelle ic2 server stop

  Run `isabelle ic2 COMMAND --help` for a command's own options.

  Servers are discovered by name via Unix-domain sockets in
  $ISABELLE_HOME_USER/ic2/<name>.sock; -n NAME picks one (default: the
  sole running server, if there is exactly one).
"""

  private def usage(): Nothing = {
    Output.writeln(usage_text, stdout = true)
    sys.exit(2)
  }

  private val server_usage_text: String = """
Usage: isabelle ic2 server SUBCOMMAND [ARGS...]

  Subcommands:
    start    start the headless PIDE daemon (--daemon to background it)
    stop     shut a server down (-n NAME)
    status   report a server's status (-n NAME), or survey all servers
    attach   stream a (backgrounded) server's console log — build progress and
             all — as if it were running in the foreground (-n NAME)

  Run `isabelle ic2 server SUBCOMMAND --help` for a subcommand's own options.
"""

  private def server_usage(): Nothing = {
    Output.writeln(server_usage_text, stdout = true)
    sys.exit(2)
  }

  /** `ic2 server start|stop|status`. */
  private def server(args: List[String]): Unit =
    args match {
      case "start" :: rest => Daemon.start(rest)
      case "stop" :: rest => Client.stop(rest)
      case "status" :: rest => Client.status(rest)
      case "attach" :: rest => Client.server_attach(rest)
      case ("help" | "-h" | "--help") :: _ | Nil => server_usage()
      case cmd :: _ =>
        Output.error_message("unknown `server` subcommand: " + cmd)
        server_usage()
    }

  /** `ic2 check`: a bare `check` (with FILE... and/or option flags) runs a
   *  check; the words `status` / `attach` / `cancel` select a subcommand. A
   *  `.thy` FILE can never collide with those, so the leading word disambiguates. */
  private def check(args: List[String]): Unit =
    args match {
      case "status" :: rest => Client.check_status(rest)
      case "attach" :: rest => Client.check_attach(rest)
      case "cancel" :: rest => Client.check_cancel(rest)
      case _ => Client.check(args)   // FILE... [+ --detach/-n/-P], or its own --help/usage
    }

  private def run_tool(args: List[String]): Unit =
    args match {
      case "server" :: rest => server(rest)
      case "check" :: rest => check(rest)
      case "load-files" :: rest => Client.load_files(rest)
      case "query" :: rest => Client.query(rest)
      case "repl-create" :: rest => Client.repl_create(rest)
      case ("help" | "-h" | "--help") :: _ | Nil => usage()
      case cmd :: _ =>
        Output.error_message("unknown command: " + cmd)
        usage()
    }
}
