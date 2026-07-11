/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      ic2/src/client.scala

Client subcommands for `isabelle ic2`: `check FILE...`, `status`, `stop`.
`check` renders one ANSI progress bar per active theory; it falls back to
plain-text event lines on a non-TTY (or with -P).

Connects to the daemon's Unix-domain socket (discovered by name). There is no
auth handshake — the 0700 socket directory is the access boundary.

On exit (normal exit, exception, JVM shutdown) during a check, the channel
closes and the server's cancel-on-disconnect path interrupts the in-flight
check. There is no explicit cancel op: dropping the connection is the cancel.
*/

package isabelle.ic2

import isabelle._

import java.io.{IOException, PrintStream}
import java.net.UnixDomainSocketAddress
import java.nio.channels.SocketChannel
import java.nio.file.Paths


object Client {

  /** How many active progress bars the ANSI UI shows at once. */
  private val MAX_ACTIVE_BARS: Int = 20

  /** Default threshold (seconds) for the long-running-command list under each
   *  bar. Overridable per-invocation with `check --long-running SECS`. */
  private val DEFAULT_LONG_RUNNING_SECS: Double = 5.0

  /** True if args request help. We intercept `help`/`--help`/`-h` in the
   *  Getopts-based commands before Getopts sees them — Getopts only knows the
   *  Isabelle-wide `-?`, which we don't advertise; this makes `--help` / `help`
   *  work uniformly across every `ic2` command. */
  private def wants_help(args: List[String]): Boolean =
    args.exists(a => a == "help" || a == "--help" || a == "-h")


  /* ---- discovery + connection ---- */

  /** Socket path for `name`, or exit 3 with a hint if no such server exists. */
  private def resolve_socket(name: String): Path = {
    if (Endpoint.exists(name)) Endpoint.socket(name)
    else {
      val others = Endpoint.list_names()
      val hint =
        if (others.isEmpty) "  (no servers found in " + Endpoint.dir.expand.implode + ")"
        else "  available servers: " + others.mkString(", ")
      Output.error_message(
        "No server named " + quote(name) + " (socket " +
        Endpoint.socket(name).expand.implode + " not found)\n" + hint)
      sys.exit(3)
    }
  }

  /** Resolve which server a name-taking command should act on: an explicit
   *  `-n NAME` is honored as-is; without one, auto-select the sole server if
   *  exactly one exists. Errors (exit 3) when there are none, and (exit 2) when
   *  there are several and the choice is ambiguous — so `-n` is optional in the
   *  common single-server case but required when it would be guesswork. */
  private def resolve_name(explicit: Option[String]): String =
    explicit match {
      case Some(n) => n
      case None =>
        Endpoint.list_names() match {
          case Nil =>
            Output.error_message("no ic2 servers found in " + Endpoint.dir.expand.implode +
              " (start one with `isabelle ic2 server start`)")
            sys.exit(3)
          case one :: Nil => one
          case many =>
            Output.error_message("several ic2 servers are running (" + many.mkString(", ") +
              "); pick one with -n NAME")
            sys.exit(2)
        }
    }

  /** Exit code 3 = connection lost / server unreachable. */
  private def connection_lost(msg: String): Nothing = {
    Output.error_message("cannot reach server: " + msg)
    sys.exit(3)
  }

  /** The server's greeting: which logic it serves, and its pid. */
  private case class Ready(session: String, pid: Long)

  /** Connect to the socket and read the `ready` greeting, returning the live
   *  channel + greeting, or None on any failure (no exit — callers decide what
   *  a failure means). */
  private def try_open(socket_path: Path): Option[(JSON_IO, Ready)] = {
    val addr = UnixDomainSocketAddress.of(Paths.get(socket_path.expand.implode))
    val channel =
      try SocketChannel.open(addr)
      catch { case _: IOException => return None }
    val io = JSON_IO(channel)
    io.read() match {
      case Some(t) if JSON.string(t, "event").contains("ready") =>
        Some((io, Ready(
          session = JSON.string(t, "session").getOrElse("?"),
          pid = JSON.long(t, "pid").getOrElse(0L))))
      case _ => io.close(); None
    }
  }

  /** Connect + read greeting; exit 3 if the server can't be reached. */
  private def open_connection(socket_path: Path): JSON_IO =
    try_open(socket_path).map(_._1).getOrElse(connection_lost(
      socket_path.expand.implode + " (server not running, or socket stale?)"))


  /* ============================ check ============================== */

  private val check_usage_text: String = """
Usage: isabelle ic2 check [OPTIONS] FILE...

  Options are:
    -n NAME             server name (default: the sole running server)
    -P                  plain mode (disable ANSI progress bars)
    --detach            submit the check and return immediately, without
                        waiting; track it with `ic2 check status`
    --line N            check only the prefix of the (single) FILE up to
                        and including the command that ends on or before
                        source line N (1-based). Fast partial check for
                        iterative development. Same UI + cancel semantics
                        as a full check; commands after line N are left
                        UNPROCESSED. Requires exactly one FILE.
    --long-running SECS commands running longer than SECS are listed under
                        their theory's progress bar (default 5; 0 disables)

  Type-check the given .thy files against the running server; the first error
  stops the check (exit 1). Ctrl-C closes the connection, which cancels it.
  With --detach the check keeps running after the command returns.

  Examples:
    isabelle ic2 check src/MyThy.thy               # full check
    isabelle ic2 check src/MyThy.thy --line 42     # up to line 42 only
    isabelle ic2 check src/MyThy.thy --detach      # background it

  Subcommands (in place of FILE...): status | attach | cancel — see
  `isabelle ic2 --help`.
"""

  def check(args: List[String]): Unit = {
    if (wants_help(args)) { Output.writeln(check_usage_text, stdout = true); sys.exit(2) }
    var name: Option[String] = None
    var plain: Boolean = false
    // `--detach`, `--long-running`, and `--line` are long options, which
    // Isabelle's single-letter Getopts can't express; strip them ourselves
    // first (same trick as `ic2 server start --daemon`).
    val detach = args.contains("--detach")
    var long_running_secs: Double = DEFAULT_LONG_RUNNING_SECS
    val (long_running_stripped, afterLR) = extract_long_running(args) match {
      case Some((secs, rest)) => long_running_secs = secs; (true, rest)
      case None => (false, args)
    }
    val _ = long_running_stripped
    val (line_opt, afterLine) = extract_line(afterLR)
    val rest_args = afterLine.filterNot(_ == "--detach")
    val getopts = Getopts(check_usage_text,
      "n:" -> (a => name = Some(a)),
      "P"  -> (_ => plain = true))

    val files = getopts(rest_args)
    if (files.isEmpty) {
      Output.error_message("check: at least one FILE required"); sys.exit(2)
    }
    if (line_opt.isDefined && files.length != 1) {
      Output.error_message("check --line: requires exactly one FILE, got " + files.length)
      sys.exit(2)
    }
    val server = resolve_name(name)
    if (detach) do_check_detach(server, files, line_opt)
    else do_check(server, plain, files, long_running_secs, line_opt)
  }

  /** Pull an optional `--line N` from the args: returns (parsed line-or-None,
   *  args with the flag+value removed). Exits(2) if N isn't a positive integer,
   *  so a mistyped value never falls through as a positional FILE. */
  private def extract_line(args: List[String]): (Option[Int], List[String]) = {
    val i = args.indexOf("--line")
    if (i < 0) (None, args)
    else if (i + 1 >= args.length) {
      Output.error_message("check: --line requires a positive integer N")
      sys.exit(2)
    }
    else args(i + 1).toIntOption match {
      case Some(n) if n > 0 => (Some(n), args.take(i) ::: args.drop(i + 2))
      case _ =>
        Output.error_message("check: --line N expects a positive integer, got " + args(i + 1))
        sys.exit(2)
    }
  }

  /** Pull an optional `--long-running SECS` from the args, returning the
   *  parsed threshold + the args with both tokens removed; None if absent. */
  private def extract_long_running(args: List[String]): Option[(Double, List[String])] = {
    val i = args.indexOf("--long-running")
    if (i < 0 || i + 1 >= args.length) None
    else {
      val v = args(i + 1)
      v.toDoubleOption match {
        case Some(secs) if secs >= 0 =>
          Some((secs, args.take(i) ::: args.drop(i + 2)))
        case _ =>
          Output.error_message("check: --long-running SECS expects a non-negative number, got " + v)
          sys.exit(2)
      }
    }
  }

  private def do_check(name: String, plain: Boolean, files: List[String],
                       long_running_secs: Double = DEFAULT_LONG_RUNNING_SECS,
                       line: Option[Int] = None): Unit = {
    // Validate locally first — fail fast with the user's CWD context, before
    // any round-trip. The server re-checks too (defence in depth).
    val abs_files = files.map { f =>
      if (!f.endsWith(".thy")) {
        Output.error_message("not a .thy file: " + f); sys.exit(1)
      }
      val jfile = Path.explode(f).expand.absolute_file
      if (!jfile.isFile) {
        Output.error_message("file not found: " + f); sys.exit(1)
      }
      File.standard_path(jfile)
    }

    val io = open_connection(resolve_socket(name))

    /* Cancel on JVM shutdown (Ctrl-C, etc.): closing the channel is the
     * cancel — the server interrupts the in-flight check on disconnect. */
    val sig_handler = new Thread(new Runnable {
      def run(): Unit = try { io.close() } catch { case _: Throwable => }
    }, "ic2-sigint")
    Runtime.getRuntime.addShutdownHook(sig_handler)

    io.write(JSON.Object("op" -> "check", "files" -> abs_files) ++
      line.map(l => JSON.Object("line" -> l)).getOrElse(JSON.Object()))

    val use_tui = !plain && System.console() != null
    val ui: Progress_UI =
      if (use_tui) new ANSI_UI(MAX_ACTIVE_BARS, long_running_secs = long_running_secs)
      else new Plain_UI(long_running_secs = long_running_secs)

    var ok: Option[Boolean] = None
    var reason: String = ""

    try {
      stream_check_events(io, ui, b => ok = Some(b), r => reason = r)
    } finally {
      ui.close()
      try { Runtime.getRuntime.removeShutdownHook(sig_handler) }
      catch { case _: IllegalStateException => /* shutdown in progress */ }
      try { io.close() } catch { case _: Throwable => }
    }

    ok match {
      case Some(true) => sys.exit(0)
      case Some(false) =>
        if (reason.nonEmpty) Output.error_message("check failed: " + reason)
        sys.exit(1)
      case None =>
        Output.error_message("check: connection lost before completion")
        sys.exit(3)
    }
  }

  /** Read the check event stream from `io`, rendering started/progress/error to
   *  `ui` and reporting the terminal `finished` via setOk/setReason. Shared by
   *  the foreground `check` and `check-attach`. Returns when `finished` or EOF. */
  private def stream_check_events(
    io: JSON_IO, ui: Progress_UI, setOk: Boolean => Unit, setReason: String => Unit
  ): Unit = {
    var done = false
    while (!done) {
      io.read() match {
        case None => done = true
        case Some(t) =>
          JSON.string(t, "event") match {
            case Some("started") =>
              ui.started(JSON.strings(t, "theories").getOrElse(Nil))
            case Some("progress") =>
              ui.progress(JSON.array(t, "nodes").getOrElse(Nil).flatMap(parse_theory_status))
            case Some("error") =>
              ui.error(JSON.string(t, "theory").getOrElse("?"),
                JSON.string(t, "file").getOrElse("?"),
                JSON.int(t, "line").getOrElse(0),
                JSON.string(t, "message").getOrElse(""))
            case Some("finished") =>
              setOk(JSON.bool(t, "ok").getOrElse(false))
              setReason(JSON.string(t, "reason").getOrElse(""))
              done = true
            case Some("server_error") => ui.server_error(JSON.string(t, "message").getOrElse(""))
            case Some("shutting_down") => ui.note("server shutting down")
            case Some(other) => ui.note("(unknown event: " + other + ")")
            case None => ui.note("(event-less: " + JSON.Format(t) + ")")
          }
      }
    }
  }

  /** Submit a detached check: validate locally, send `{op:check, detach:true}`,
   *  report it started, and return (the check keeps running on the server). */
  private def do_check_detach(name: String, files: List[String], line: Option[Int] = None): Unit = {
    val abs_files = files.map { f =>
      if (!f.endsWith(".thy")) { Output.error_message("not a .thy file: " + f); sys.exit(1) }
      val jfile = Path.explode(f).expand.absolute_file
      if (!jfile.isFile) { Output.error_message("file not found: " + f); sys.exit(1) }
      File.standard_path(jfile)
    }
    val reply = request(name, JSON.Object("op" -> "check", "files" -> abs_files, "detach" -> true) ++
      line.map(l => JSON.Object("line" -> l)).getOrElse(JSON.Object()))
    JSON.string(reply, "event") match {
      case Some("submitted") =>
        Output.writeln("submitted (" +
          JSON.strings(reply, "theories").getOrElse(Nil).mkString(", ") + ")\n" +
          "track with: isabelle ic2 check status -n " + name)
        sys.exit(0)
      case _ =>
        Output.error_message("check --detach failed: " +
          JSON.string(reply, "message").getOrElse(JSON.Format(reply)))
        sys.exit(1)
    }
  }

  /** One-shot request/reply on a fresh connection (consumes the `ready`
   *  greeting, writes the op, reads one reply). For the non-streaming ops. */
  private def request(name: String, op: JSON.Object.T): JSON.T = {
    val io = open_connection(resolve_socket(name))
    try { io.write(op); io.read().getOrElse(connection_lost("no reply to " + JSON.string(op, "op").getOrElse("op"))) }
    finally { try { io.close() } catch { case _: Throwable => } }
  }

  /** Default number of per-theory progress bars shown by check status/attach. */
  private val DEFAULT_BARS: Int = MAX_ACTIVE_BARS

  /** Parse `-n NAME` for a check subcommand (there is at most one check, so no
   *  job id); auto-select the sole server when -n is omitted. `desc` is a
   *  one-line summary shown in `--help`. */
  private def name_opt(cmd: String, desc: String, args: List[String]): String = {
    val usage = s"""
Usage: isabelle ic2 $cmd [-n NAME]

  $desc

  -n NAME   server name (default: the sole running server)
"""
    if (wants_help(args)) { Output.writeln(usage, stdout = true); sys.exit(2) }
    var name: Option[String] = None
    val getopts = Getopts(usage, "n:" -> (a => name = Some(a)))
    val rest = getopts(args)
    if (rest.nonEmpty) getopts.usage()
    resolve_name(name)
  }

  /** Parse `-n NAME` and `-c N` (max progress bars; 0 = unlimited) for a check
   *  subcommand. Returns (resolved server, bar limit; a large number for
   *  "unlimited"). `desc` is a one-line summary shown in `--help`. */
  private def name_and_bars_opt(cmd: String, desc: String, args: List[String]): (String, Int) = {
    val usage = s"""
Usage: isabelle ic2 $cmd [-n NAME] [-c N]

  $desc

  -n NAME   server name (default: the sole running server)
  -c N      max per-theory progress bars to show (default $DEFAULT_BARS; 0 = all)
"""
    if (wants_help(args)) { Output.writeln(usage, stdout = true); sys.exit(2) }
    var name: Option[String] = None
    var bars: Int = DEFAULT_BARS
    val getopts = Getopts(usage,
      "n:" -> (a => name = Some(a)),
      "c:" -> (a => bars = Value.Int.parse(a)))
    val rest = getopts(args)
    if (rest.nonEmpty) getopts.usage()
    (resolve_name(name), if (bars <= 0) Int.MaxValue else bars)
  }

  /** `ic2 check status`: print one static frame of the current/last check —
   *  the same "checking N theory/theories" + per-theory bar view that
   *  `check attach` streams, but rendered once and returned. Because it shows
   *  per-theory percentage / finished / running counts (not just elapsed ms),
   *  two successive polls reveal whether the check is advancing or stalled. */
  def check_status(args: List[String]): Unit = {
    val (name, bars) = name_and_bars_opt("check status",
      "Report the current/last check's state (running/ok/failed/idle), elapsed\n" +
      "  time, and per-theory progress. One-shot; does not stream.", args)
    val reply = request(name, JSON.Object("op" -> "check_status"))
    if (!JSON.string(reply, "event").contains("check_status")) {
      print_job_status(reply); sys.exit(3)
    }
    val state = JSON.string(reply, "state").getOrElse("?")
    val thys = JSON.strings(reply, "theories").getOrElse(Nil)
    val el = JSON.long(reply, "elapsed_ms").getOrElse(0L)
    val reason = JSON.string(reply, "reason").map(r => " reason=" + r).getOrElse("")
    val nodes = JSON.array(reply, "nodes").getOrElse(Nil).flatMap(parse_theory_status)

    // Headline: state + elapsed + theories (first line is grep-friendly).
    Output.writeln(state + " " + el + "ms" + reason +
      (if (thys.nonEmpty) "  theories=" + thys.mkString(",") else ""))
    // Per-theory frame — only while running and there is node detail to show
    // (a finished/idle check has nothing in flight to draw).
    if (state == "running" && nodes.nonEmpty)
      render_progress_frame(nodes, bars).foreach(Output.writeln(_))
    sys.exit(0)
  }

  /** `ic2 check cancel`: request cancellation of the in-flight check. */
  def check_cancel(args: List[String]): Unit = {
    val name = name_opt("check cancel",
      "Abort the in-flight check (reason \"cancelled\"). No-op if none is running.", args)
    val reply = request(name, JSON.Object("op" -> "check_cancel"))
    JSON.string(reply, "event") match {
      case Some("check_cancel") =>
        Output.writeln(
          if (JSON.bool(reply, "cancelled").getOrElse(false)) "cancellation requested"
          else "no check running")
        sys.exit(0)
      case _ =>
        Output.error_message(JSON.string(reply, "message").getOrElse("check cancel failed"))
        sys.exit(3)
    }
  }

  /** `ic2 check attach`: stream the in-flight (typically detached) check's
   *  progress to completion, like a foreground check. Does not cancel on
   *  disconnect. */
  def check_attach(args: List[String]): Unit = {
    val (name, bars) = name_and_bars_opt("check attach",
      "Stream the in-flight check's progress to completion, like a foreground\n" +
      "  check. Does NOT cancel the check on disconnect.", args)
    val io = open_connection(resolve_socket(name))
    io.write(JSON.Object("op" -> "check_attach"))
    val use_tui = System.console() != null
    val ui: Progress_UI = if (use_tui) new ANSI_UI(bars) else new Plain_UI(bars)
    var ok: Option[Boolean] = None; var reason = ""
    try { stream_check_events(io, ui, b => ok = Some(b), r => reason = r) }
    finally { ui.close(); try { io.close() } catch { case _: Throwable => } }
    ok match {
      case Some(true) => sys.exit(0)
      case Some(false) => if (reason.nonEmpty) Output.error_message("check failed: " + reason); sys.exit(1)
      case None => Output.error_message("check attach: no check in flight, or connection lost"); sys.exit(3)
    }
  }

  /** Print the check's status line from a check_status reply object. */
  private def print_job_status(j: JSON.T): Unit = {
    val st = JSON.string(j, "state").getOrElse("?")
    val thys = JSON.strings(j, "theories").getOrElse(Nil)
    val el = JSON.long(j, "elapsed_ms").getOrElse(0L)
    val reason = JSON.string(j, "reason").map(r => " reason=" + r).getOrElse("")
    Output.writeln(st + " " + el + "ms" + reason +
      (if (thys.nonEmpty) "  theories=" + thys.mkString(",") else ""))
  }

  private def parse_theory_status(t: JSON.T): Option[Theory_Status] =
    JSON.string(t, "theory").map { th =>
      val long_running =
        JSON.array(t, "long_running").getOrElse(Nil).flatMap { rc =>
          for {
            kw <- JSON.string(rc, "keyword")
            ln <- JSON.int(rc, "line")
          } yield {
            val elapsed =
              JSON.double(rc, "elapsed_s")
                .orElse(JSON.int(rc, "elapsed_s").map(_.toDouble))
                .orElse(JSON.long(rc, "elapsed_s").map(_.toDouble))
                .getOrElse(0.0)
            val preview = JSON.string(rc, "preview").getOrElse("")
            Running_Command(kw, ln, elapsed, preview)
          }
        }
      Theory_Status(
        theory = th,
        percentage = JSON.int(t, "percentage").getOrElse(0),
        unprocessed = JSON.int(t, "unprocessed").getOrElse(0),
        running = JSON.int(t, "running").getOrElse(0),
        finished = JSON.int(t, "finished").getOrElse(0),
        warned = JSON.int(t, "warned").getOrElse(0),
        failed = JSON.int(t, "failed").getOrElse(0),
        consolidated = JSON.bool(t, "consolidated").getOrElse(false),
        updated = JSON.long(t, "update_seq")
          .orElse(JSON.int(t, "update_seq").map(_.toLong)).getOrElse(0L),
        long_running = long_running)
    }


  /* ========================== load-files =========================== */

  private val load_files_usage_text: String = """
Usage: isabelle ic2 load-files [OPTIONS] FILE...

  Options are:
    -n NAME             server name (default: the sole running server)
    --print             after loading, print the parsed command spans of
                        each loaded node (line, offset range, keyword,
                        source) — same output as `ic2 query spans FILE`
    --include-ignored   with --print, include inter-command whitespace/
                        comment spans too (Ignored_Span)

  Parse the given .thy files into the running server's document graph
  WITHOUT evaluating any commands: the Scala side splits each theory into
  its commands (fixing spans, IDs, offsets, line positions), but no ML
  process runs and no proof state is produced. After loading:

    - `ic2 query list-files` lists the newly-loaded nodes.
    - `ic2 query entities|sorry|spans|proof-blocks|command-info|state-at`
      work on the loaded nodes (with proof/status fields empty).

  A subsequent `ic2 check` on the same files will pay only the evaluation
  cost, not the parse cost. Header imports are checked (they must be
  locatable in the session), but their bodies aren't evaluated either.

  Exit codes: 0 (loaded); 1 (bad FILE: not .thy, or does not exist); 2 (usage:
  no FILE, or --include-ignored without --print); 3 (server-side error, e.g.
  header parse failed).
"""

  /** `ic2 load-files FILE...` — parse the given .thy files into the session's
   *  document graph, without evaluating them. Same file-resolution shape as
   *  `ic2 check`. With `--print`, follows up with a `list_spans` query for
   *  every loaded node so the raw parse output is visible without a second
   *  invocation. */
  def load_files(args: List[String]): Unit = {
    if (wants_help(args)) { Output.writeln(load_files_usage_text, stdout = true); sys.exit(2) }
    var name: Option[String] = None
    // `--print` and `--include-ignored` are long options (Getopts is single-
    // letter only); strip them ourselves first.
    val print_spans = args.contains("--print")
    val include_ignored = args.contains("--include-ignored")
    if (include_ignored && !print_spans) {
      Output.error_message("load-files: --include-ignored requires --print")
      sys.exit(2)
    }
    val rest_args = args.filterNot(a => a == "--print" || a == "--include-ignored")
    val getopts = Getopts(load_files_usage_text,
      "n:" -> (a => name = Some(a)))
    val files = getopts(rest_args)
    if (files.isEmpty) {
      Output.error_message("load-files: at least one FILE required"); sys.exit(2)
    }
    // Same local validation as `check`: absolute .thy, exists.
    val abs_files = files.map { f =>
      if (!f.endsWith(".thy")) { Output.error_message("not a .thy file: " + f); sys.exit(1) }
      val jfile = Path.explode(f).expand.absolute_file
      if (!jfile.isFile) { Output.error_message("file not found: " + f); sys.exit(1) }
      File.standard_path(jfile)
    }
    val server = resolve_name(name)
    val reply = request(server, JSON.Object("op" -> "load-files", "files" -> abs_files))
    JSON.string(reply, "event") match {
      case Some("load-files") =>
        val loaded = JSON.strings(reply, "loaded").getOrElse(Nil)
        Output.writeln("loaded " + loaded.length + " theory node(s):")
        for (n <- loaded) Output.writeln("  " + n, stdout = true)
        if (print_spans) print_loaded_spans(server, loaded, include_ignored)
        sys.exit(0)
      case _ =>
        Output.error_message(JSON.string(reply, "message").getOrElse("load-files failed: " + JSON.Format(reply)))
        sys.exit(3)
    }
  }

  /** After `load-files --print`: fetch and render the `list_spans` result for
   *  each loaded node. Uses the SAME query pipeline `ic2 query spans` does —
   *  the wire tool, param map, and human renderer — so its output stays
   *  byte-identical between the two entry points. */
  private def print_loaded_spans(
    server: String, nodes: List[String], include_ignored: Boolean
  ): Unit = {
    for (node <- nodes) {
      qout("")
      val params: List[(String, JSON.T)] =
        ("path" -> (node: JSON.T)) ::
        (if (include_ignored) List(("include_ignored" -> (true: JSON.T))) else Nil)
      val reply = request(server, JSON.Object(
        (("op" -> "query") :: ("tool" -> "list_spans") :: params): _*))
      JSON.value(reply, "result") match {
        case Some(result) => render_query("spans", result)
        case None =>
          Output.error_message("load-files --print: " +
            JSON.string(reply, "message").getOrElse("no result for " + node))
      }
    }
  }


  /* ============================ query ============================= */

  private val QUERY_TOOLS: List[(String, String)] = List(
    "list-files"         -> "loaded theory nodes + each node's processing status",
    "processing-status"  -> "PIDE processing-status counts for a theory (FILE)",
    "document-info"      -> "whole-theory command/error/warning totals (FILE)",
    "diagnostics"        -> "errors or warnings, file or selection scope (FILE)",
    "sorry"              -> "sorry/oops positions with enclosing proof (FILE)",
    "entities"           -> "declared entities: lemma/definition/fun/... (FILE)",
    "proof-blocks"       -> "proof blocks with text and line ranges (FILE)",
    "spans"              -> "flat list of parsed command spans (FILE)",
    "command-info"       -> "command metadata/status/result at a selection (FILE)",
    "state-at"           -> "proof state (goal + context) at a selection (FILE)")

  /** CLI subtool name -> the wire/MCP tool name it maps to. `context-info` is a
    * silent alias for `state-at`; both route to `get_context_info` on the wire. */
  private val QUERY_TOOL_WIRE: Map[String, String] = Map(
    "list-files" -> "list_files",
    "processing-status" -> "get_processing_status",
    "document-info" -> "get_document_info",
    "diagnostics" -> "get_diagnostics",
    "sorry" -> "get_sorry_positions",
    "entities" -> "get_entities",
    "proof-blocks" -> "get_proof_blocks",
    "spans" -> "list_spans",
    "command-info" -> "get_command_info",
    "state-at" -> "get_context_info",
    "context-info" -> "get_context_info")

  private def query_usage(): Nothing = {
    val tools = QUERY_TOOLS.map { case (n, d) => f"    $n%-20s $d" }.mkString("\n")
    Output.writeln(
      "Usage: isabelle ic2 query SUBTOOL [FILE] [OPTIONS]\n\n" +
      "  Read-only diagnostic queries over the resident session (the CLI form of the\n" +
      "  MCP diagnostic tools). Most take a theory FILE (a loaded/checked node;\n" +
      "  partial paths are completed). Output is human-readable; use --json for the\n" +
      "  raw tool JSON.\n\n" +
      "  ***THE key subtool is `state-at`***: reports the proof state (goal,\n" +
      "  subgoal count, in-scope frees + constants) at a source location. Use\n" +
      "  after `check` to see what a proof step left unproved.\n\n" +
      "  Examples:\n" +
      "    isabelle ic2 query state-at Foo.thy --line 42\n" +
      "    isabelle ic2 query state-at Foo.thy --pattern 'apply simp'\n" +
      "    isabelle ic2 query list-files\n" +
      "    isabelle ic2 query sorry Foo.thy\n" +
      "    isabelle ic2 query diagnostics Foo.thy --severity warning\n" +
      "    isabelle ic2 query entities Foo.thy --json\n\n" +
      "  SUBTOOL:\n" + tools + "\n" +
      "    (context-info is a deprecated alias for state-at.)\n\n" +
      "  Options:\n" +
      "    -n NAME          server name (default: the sole running server)\n" +
      "    --json           print the raw tool JSON instead of formatted text\n" +
      "    --theory         (list-files) only theory nodes\n" +
      "    --non-theory     (list-files) only non-theory nodes\n" +
      "    --severity SEV   (diagnostics) 'error' (default) or 'warning'\n" +
      "    --scope SCOPE    (diagnostics) 'file' (default) or 'selection'\n" +
      "    --offset N       (selection) character offset\n" +
      "    --line N         (selection) 1-based source line; resolves to the\n" +
      "                     command that ends on or before this line\n" +
      "    --pattern P      (selection) unique text pattern\n" +
      "    --max N          (entities) max results (default 500)\n" +
      "    --min-chars N    (proof-blocks) minimum block length\n",
      stdout = true)
    sys.exit(2)
  }

  /** `ic2 query SUBTOOL [FILE] [OPTIONS]`: one-shot read-only diagnostic over the
   *  session. Builds a `{op:query, tool, ...}` request, then renders the
   *  result as human text (default) or raw JSON (--json). */
  def query(args: List[String]): Unit = {
    // Manual parse: a mix of long flags (Getopts is single-letter only) and a
    // positional SUBTOOL + optional FILE.
    var name: Option[String] = None
    var json = false
    val req = scala.collection.mutable.LinkedHashMap.empty[String, JSON.T]
    val positional = scala.collection.mutable.ListBuffer.empty[String]

    def need(rest: List[String], flag: String): (String, List[String]) =
      rest match {
        case v :: tl => (v, tl)
        case Nil => Output.error_message("query: " + flag + " needs a value"); query_usage()
      }
    def intArg(rest: List[String], flag: String, key: String): List[String] = {
      val (v, tl) = need(rest, flag)
      v.toIntOption match {
        case Some(n) => req(key) = n.toLong; tl
        case None => Output.error_message("query: " + flag + " expects an integer, got " + v); query_usage()
      }
    }

    @annotation.tailrec
    def loop(rest: List[String]): Unit = rest match {
      case Nil => ()
      case "-n" :: tl => val (v, t2) = need(tl, "-n"); name = Some(v); loop(t2)
      case ("help" | "-h" | "--help") :: _ => query_usage()
      case "--json" :: tl => json = true; loop(tl)
      case "--theory" :: tl => req("filter_theory") = true; loop(tl)
      case "--non-theory" :: tl => req("filter_theory") = false; loop(tl)
      case "--severity" :: tl => val (v, t2) = need(tl, "--severity"); req("severity") = v; loop(t2)
      case "--scope" :: tl => val (v, t2) = need(tl, "--scope"); req("scope") = v; loop(t2)
      case "--pattern" :: tl => val (v, t2) = need(tl, "--pattern"); req("pattern") = v; loop(t2)
      case "--offset" :: tl => loop(intArg(tl, "--offset", "offset"))
      case "--line" :: tl => loop(intArg(tl, "--line", "line"))
      case "--max" :: tl => loop(intArg(tl, "--max", "max_results"))
      case "--min-chars" :: tl => loop(intArg(tl, "--min-chars", "min_chars"))
      case "--include-ignored" :: tl => req("include_ignored") = true; loop(tl)
      case other :: tl =>
        if (other.startsWith("-")) { Output.error_message("query: unknown option " + other); query_usage() }
        positional += other; loop(tl)
    }
    loop(args)

    val subtool = positional.headOption.getOrElse { query_usage() }
    val wireTool = QUERY_TOOL_WIRE.getOrElse(subtool, {
      Output.error_message("query: unknown subtool '" + subtool + "'"); query_usage()
    })
    positional.drop(1).headOption.foreach(f => req("path") = f)
    // Every subtool except list-files needs a FILE.
    if (subtool != "list-files" && !req.contains("path")) {
      Output.error_message("query " + subtool + ": a FILE argument is required"); query_usage()
    }

    val reply = request(resolve_name(name), JSON.Object(("op" -> "query") :: ("tool" -> wireTool) :: req.toList: _*))
    JSON.string(reply, "event") match {
      case Some("query") =>
        val result = JSON.value(reply, "result").getOrElse(JSON.Object())
        if (json) qout(JSON.Format(result))
        else render_query(subtool, result)
        sys.exit(0)
      case _ =>
        Output.error_message(JSON.string(reply, "message").getOrElse("query failed: " + JSON.Format(reply)))
        sys.exit(3)
    }
  }

  /** Write a query-output line to stdout (command output a user pipes / a test
   *  reads), not stderr where Output.writeln defaults. */
  private def qout(line: String): Unit = Output.writeln(line, stdout = true)

  /** Human-readable rendering of each subtool's result map. Falls back to JSON
   *  for any field shape we don't special-case. */
  private def render_query(subtool: String, r: JSON.T): Unit = {
    def i(k: String): Long = JSON.long(r, k).getOrElse(0L)
    def s(k: String): String = JSON.string(r, k).getOrElse("")
    def b(k: String): Boolean = JSON.bool(r, k).getOrElse(false)
    def arr(k: String): List[JSON.T] = JSON.array(r, k).getOrElse(Nil)

    subtool match {
      case "list-files" =>
        qout(s"""${i("count")} node(s):""")
        for (f <- arr("files")) {
          val pct = JSON.int(f, "percentage").getOrElse(0)
          val flags =
            (if (JSON.bool(f, "consolidated").getOrElse(false)) "" else " (unconsolidated)") +
            (JSON.int(f, "failed").filter(_ > 0).map(n => s" $n failed").getOrElse(""))
          qout(f"  ${pct}%3d%%  ${JSON.string(f, "node").getOrElse("?")}%s$flags%s")
        }

      case "processing-status" =>
        qout(s("path") + ": " +
          (if (b("fully_processed")) "fully processed" else "processing") +
          f"  finished=${i("finished")} running=${i("running")} unprocessed=${i("unprocessed")} failed=${i("failed")}" +
          (if (b("consolidated")) "  consolidated" else ""))

      case "document-info" =>
        qout(s("path") + ":" +
          f"  commands=${i("total_commands")} finished=${i("finished")} unprocessed=${i("unprocessed")} failed=${i("failed")}" +
          f"  errors=${i("error_count")} warnings=${i("warning_count")}" +
          (if (b("fully_processed")) "  fully processed" else ""))

      case "diagnostics" =>
        val diags = arr("diagnostics")
        qout(s("severity") + " (" + s("scope") + "): " + diags.length + " found" +
          (if (diags.isEmpty) "" else ":"))
        for (d <- diags)
          qout("  " + s_of(d, "path", s("path")) + ":" + JSON.int(d, "line").getOrElse(0) +
            ": " + one_line(JSON.string(d, "message").getOrElse("")))

      case "sorry" =>
        val ps = arr("positions")
        qout(s"""${ps.length} sorry/oops in ${s("path")}""" + (if (ps.isEmpty) "" else ":"))
        for (p <- ps)
          qout(f"  line ${JSON.int(p, "line").getOrElse(0)}%-5d ${JSON.string(p, "keyword").getOrElse("?")}%s  in ${JSON.string(p, "in_proof").getOrElse("?")}%s")

      case "entities" =>
        val es = arr("entities")
        qout(s"""${i("total_entities")} entit(ies)""" +
          (if (b("truncated")) s""" (showing ${i("returned_entities")})""" else "") +
          (if (es.isEmpty) "" else ":"))
        for (e <- es)
          qout(f"  line ${JSON.int(e, "line").getOrElse(0)}%-5d ${JSON.string(e, "keyword").getOrElse("?")}%-12s ${JSON.string(e, "name").getOrElse("?")}%s")

      case "proof-blocks" =>
        val bs = arr("blocks")
        qout(s"""${bs.length} proof block(s) in ${s("path")}""" + (if (bs.isEmpty) "" else ":"))
        for (blk <- bs)
          qout(f"  lines ${JSON.int(blk, "start_line").getOrElse(0)}-${JSON.int(blk, "end_line").getOrElse(0)}" +
            f" (${JSON.int(blk, "command_count").getOrElse(0)} cmds${if (JSON.bool(blk, "is_apply_style").getOrElse(false)) ", apply-style" else ""}): " +
            one_line(JSON.string(blk, "proof_text").getOrElse("")))

      case "spans" =>
        val ss = arr("spans")
        qout(s"""${ss.length} span(s) in ${s("path")}""" + (if (ss.isEmpty) "" else ":"))
        for (sp <- ss) {
          val kw = JSON.string(sp, "keyword").getOrElse("?")
          val kind = JSON.string(sp, "kind").getOrElse("command")
          val ln = JSON.int(sp, "line").getOrElse(0)
          val start = JSON.int(sp, "start_offset").getOrElse(0)
          val stop = JSON.int(sp, "end_offset").getOrElse(0)
          val marker = if (kind == "ignored") "  (ignored)" else ""
          qout(f"  line $ln%-5d [$start%d..$stop%d] $kw%s$marker%s  ${one_line(JSON.string(sp, "source").getOrElse(""))}%s")
        }

      case "command-info" =>
        qout(JSON.string(r, "keyword").getOrElse("?") + " [" +
          JSON.value(r, "status").flatMap(st => JSON.string(st, "summary")).getOrElse("?") + "]  " +
          one_line(s("source")))
        val txt = s("results_text")
        if (txt.nonEmpty) { qout("  ---"); txt.linesIterator.foreach(l => qout("  " + l)) }

      case "state-at" | "context-info" =>
        qout(JSON.value(r, "command").flatMap(c => JSON.string(c, "keyword")).getOrElse("?") +
          "  in_proof_context=" + b("in_proof_context") + "  has_goal=" + b("has_goal"))
        JSON.value(r, "goal").foreach { g =>
          val gt = JSON.string(g, "goal_text").getOrElse("")
          if (gt.nonEmpty) { qout("  ---"); gt.linesIterator.foreach(l => qout("  " + l)) }
        }

      case _ => qout(JSON.Format(r))
    }
  }

  private def s_of(j: JSON.T, key: String, fallback: String): String =
    JSON.string(j, key).getOrElse(fallback)
  /** Collapse a multi-line snippet to a single trimmed line for list output. */
  private def one_line(text: String): String = {
    val t = text.linesIterator.map(_.trim).filter(_.nonEmpty).mkString(" ")
    if (t.length > 100) t.take(97) + "..." else t
  }


  /* ========================= repl-create ========================== */

  /** `ic2 repl-create FILE:LINE NAME`: create an interactive I/R REPL named NAME
   *  from a source location — the command spanning LINE (1-based) of theory
   *  FILE, in the resident session. The daemon does the resolution (it has the
   *  session + the I/R client); the bare `repl.py cli` cannot, so this is the
   *  way to start a REPL at a `.thy` position. Prints the REPL's initial state
   *  AND the exact `repl.py cli` commands to drive it. FILE must be a loaded
   *  node — check it first. */
  def repl_create(args: List[String]): Unit = {
    def usage(): Nothing = {
      Output.writeln(
        "Usage: isabelle ic2 repl-create FILE:LINE NAME [-n SERVER]\n\n" +
        "  Create an interactive I/R REPL named NAME at a source location: the\n" +
        "  command on LINE (1-based) of the theory FILE (a loaded/checked node).\n" +
        "  Prints the REPL's initial state and the `repl.py cli` commands to\n" +
        "  drive it (step/state/text/...).\n\n" +
        "  -n SERVER   server name (default: the sole running server)\n", stdout = true)
      sys.exit(2)
    }
    // Pull `-n SERVER` from anywhere (so trailing `-n` works — Isabelle's
    // Getopts would stop at the first positional and leave it in `rest`); the
    // two remaining positionals are FILE:LINE and NAME.
    var name: Option[String] = None
    val pos = scala.collection.mutable.ListBuffer.empty[String]
    @annotation.tailrec
    def split(as: List[String]): Unit = as match {
      case Nil => ()
      case "-n" :: v :: tl => name = Some(v); split(tl)
      case ("help" | "-h" | "--help") :: _ => usage()
      case a :: tl => pos += a; split(tl)
    }
    split(args)
    val (loc, repl_name) = pos.toList match {
      case loc :: repl_name :: Nil => (loc, repl_name)
      case _ => usage()
    }
    // Split FILE:LINE on the LAST colon, so absolute Windows-ish or odd paths
    // still work; LINE must be a positive integer.
    val i = loc.lastIndexOf(':')
    if (i <= 0 || i == loc.length - 1) {
      Output.error_message("repl-create: location must be FILE:LINE, got " + quote(loc)); sys.exit(2)
    }
    val file = loc.substring(0, i)
    val line = loc.substring(i + 1).toIntOption.filter(_ > 0).getOrElse {
      Output.error_message("repl-create: LINE must be a positive integer, got " + quote(loc.substring(i + 1)))
      sys.exit(2)
    }
    val reply = request(resolve_name(name), JSON.Object(
      "op" -> "repl", "file" -> file, "line" -> line, "name" -> repl_name))
    JSON.string(reply, "event") match {
      case Some("repl") =>
        qout(JSON.string(reply, "result").getOrElse(""))
        // The driving schema: exact `repl.py cli` command lines for THIS repl,
        // so an agent can act with no further lookup.
        JSON.string(reply, "drive").foreach(d => { qout(""); qout(d) })
        sys.exit(0)
      case _ =>
        Output.error_message(JSON.string(reply, "message").getOrElse("repl-create failed: " + JSON.Format(reply)))
        sys.exit(3)
    }
  }


  /* ============================ status ============================= */

  private val status_usage_text: String = """
Usage: isabelle ic2 server status [OPTIONS]

  Options are:
    -n NAME      report only the named server (exit 3 if unreachable)
    --full       also list every loaded document node with its processing %
                 and error count, followed by the errors themselves

  Without -n, survey every server with a socket in the discovery directory,
  pinging each for its status (one line per server). With --full and no -n, the
  sole running server is used.
"""

  def status(args: List[String]): Unit = {
    if (wants_help(args)) { Output.writeln(status_usage_text, stdout = true); sys.exit(2) }
    var name: Option[String] = None
    val full = args.contains("--full")
    val getopts = Getopts(status_usage_text,
      "n:" -> (a => name = Some(a)))
    val rest = getopts(args.filterNot(_ == "--full"))
    if (rest.nonEmpty) getopts.usage()

    if (full) status_one(resolve_name(name), full = true)
    else name match {
      case Some(n) => status_one(n)
      case None => status_all()
    }
  }

  /** A single named server: print its status or exit 3 if unreachable. With
   *  `full`, also print the full document-node list (per-node % + error counts)
   *  and the errors themselves — via follow-up `query` ops (needs a ready
   *  session; on a still-building server the node list is simply skipped). */
  private def status_one(name: String, full: Boolean = false): Unit =
    Daemon.ping_status(name) match {
      case Some(st) =>
        Output.writeln(format_status(name, st))
        Output.writeln(format_options(st))
        Output.writeln(format_ir(st))
        if (full) print_full_nodes(name, st)
        sys.exit(0)
      case None =>
        if (Endpoint.exists(name))
          Output.error_message(name + ": socket present but not responding (stale node?)")
        else
          Output.error_message("no server named " + quote(name) +
            " (looked in " + Endpoint.dir.expand.implode + ")")
        sys.exit(3)
    }

  /** The `--full` body: list every loaded document node with its processing %,
   *  a bar, and error/warning counts; then, for nodes that have errors, the
   *  errors themselves (file:line + message). Fetched from the daemon via the
   *  same `query` ops the diagnostic CLI uses (list_files + get_diagnostics), so
   *  it reflects the live session. Skipped with a note if the server isn't ready
   *  yet (no session to enumerate). */
  private def print_full_nodes(name: String, st: JSON.T): Unit = {
    val state = JSON.string(st, "state").getOrElse("ready")
    if (state != "ready") {
      Output.writeln("    (node list unavailable: server is " + state + ")")
      return
    }
    val lf = request(name, JSON.Object("op" -> "query", "tool" -> "list_files"))
    if (!JSON.string(lf, "event").contains("query")) {
      Output.writeln("    (could not list nodes: " +
        JSON.string(lf, "message").getOrElse("query failed") + ")")
      return
    }
    val result = JSON.value(lf, "result").getOrElse(JSON.Object())
    val files = JSON.array(result, "files").getOrElse(Nil)
    if (files.isEmpty) { Output.writeln("  no document nodes loaded"); return }

    // Column-aligned node table: name, bar, %, and finished/failed/warned
    // tallies. `unprocessed` is carried too (as tuple position 8) so the
    // heap-node filter below can distinguish a parse-only node (has commands
    // to process) from a fully heap-resident node (nothing tracked).
    val allRows = files.map { f =>
      (JSON.string(f, "theory").orElse(JSON.string(f, "node")).getOrElse("?"),
       JSON.int(f, "percentage").getOrElse(0),
       JSON.int(f, "finished").getOrElse(0),
       JSON.int(f, "failed").getOrElse(0),
       JSON.int(f, "warned").getOrElse(0),
       JSON.bool(f, "consolidated").getOrElse(false),
       JSON.string(f, "node").getOrElse(""),
       JSON.int(f, "unprocessed").getOrElse(0))
    }
    // Omit heap/library nodes: those already resident in the prebuilt heap
    // show up in the document graph but have no PIDE commands tracked in this
    // session — every counter is zero AND `unprocessed == 0` (nothing to do).
    // A parse-only node loaded via `ic2 load-files` has the same zeros for
    // finished/failed/warned/consolidated but `unprocessed > 0` (every command
    // is tracked, none evaluated), so it survives the filter and shows up as
    // a real (0%) row rather than being folded into the "heap omitted" count.
    val rows = allRows.filterNot { case (_, pct, fin, failed, warned, cons, _, unproc) =>
      pct == 0 && fin == 0 && failed == 0 && warned == 0 && !cons && unproc == 0
    }
    val omitted = allRows.length - rows.length
    if (rows.isEmpty) {
      Output.writeln("  no active document nodes" +
        (if (omitted > 0) " (" + omitted + " heap node(s) omitted)" else ""))
      return
    }
    val total = rows.length
    val done = rows.count(_._6)
    val errNodes = rows.filter(_._4 > 0)
    Output.writeln("  " + total + " active node(s), " + done + " consolidated" +
      (if (errNodes.nonEmpty) ", " + errNodes.size + " with errors" else "") +
      (if (omitted > 0) " (" + omitted + " heap node(s) omitted)" else ""))
    val name_w = (term_width - 46).max(20).min(70)
    for ((thy, pct, fin, failed, warned, _, _, unproc) <- rows) {
      val _ = fin
      val nm = if (thy.length > name_w) "..." + thy.substring(thy.length - name_w + 3)
               else thy.padTo(name_w, ' ')
      // Parse-only nodes (0% but with commands still to process) show a
      // `parsed` flag so `--full` distinguishes them from a heap-resident
      // node (which the filter already omits) and from an in-flight check.
      val parseOnly = pct == 0 && failed == 0 && warned == 0 && unproc > 0
      val flags =
        (if (failed > 0) f"  ${failed}%d err" else "") +
        (if (warned > 0) f"  ${warned}%d warn" else "") +
        (if (parseOnly)  "  parsed"           else "")
      Output.writeln(f"  $nm ${progress_bar(pct)} $pct%3d%%$flags")
    }

    // Errors section: for each node with failures, fetch and print its errors.
    if (errNodes.nonEmpty) {
      Output.writeln("")
      Output.writeln("  errors:")
      for ((thy, _, _, _, _, _, node, _) <- errNodes) {
        val dg = request(name, JSON.Object("op" -> "query", "tool" -> "get_diagnostics",
          "path" -> node, "severity" -> "error", "scope" -> "file"))
        val res = JSON.value(dg, "result").getOrElse(JSON.Object())
        val items = JSON.array(res, "diagnostics").getOrElse(JSON.array(res, "messages").getOrElse(Nil))
        if (items.isEmpty) Output.writeln("    " + thy + ": (error reported, no message detail)")
        else for (d <- items) {
          val ln = JSON.int(d, "line").map(":" + _).getOrElse("")
          val msg = JSON.string(d, "message").getOrElse("").trim.replace("\n", "\n        ")
          Output.writeln("    " + thy + ln + "  " + msg)
        }
      }
    }
  }

  /** Every server with a socket node: ping each (summary line + I/R line).
   *  Informational — always exits 0, even with stale nodes present. */
  private def status_all(): Unit = {
    val names = Endpoint.list_names()
    if (names.isEmpty)
      Output.writeln("no ic2 servers (looked in " + Endpoint.dir.expand.implode + ")")
    else
      for (n <- names) {
        Daemon.ping_status(n) match {
          case Some(st) =>
            Output.writeln(format_status(n, st))
            Output.writeln(format_ir(st))
          case None => Output.writeln(n + ": stale socket (no server listening)")
        }
      }
    sys.exit(0)
  }

  /** One-line status summary. Shared with the daemon's --daemon readiness
   *  message, so keep it compact and self-contained. */
  def format_status(name: String, st: JSON.T): String = {
    val session = JSON.string(st, "session").getOrElse("?")
    val pid = JSON.long(st, "pid").getOrElse(0L)
    val up = JSON.long(st, "uptime_s").getOrElse(0L)
    val busy = JSON.bool(st, "busy").getOrElse(false)
    val cif = JSON.int(st, "checks_in_flight").getOrElse(0)
    val conns = JSON.long(st, "connections").getOrElse(0L)
    // A server that isn't yet "ready" is still coming up (heap build / session
    // load) or failed: report the phase + a one-line build readout instead of
    // the idle/busy activity, so a client polling during a cold build sees it.
    val state = JSON.string(st, "state").getOrElse("ready")
    val activity =
      if (state != "ready") state + format_build(st)
      else if (busy) "busy(" + cif + " check" + (if (cif == 1) "" else "s") + ")"
      else "idle"
    name + ": session=" + session + " pid=" + pid + " up=" + up + "s " +
      activity + " conns=" + conns
  }

  /** The compact build readout appended while a server is not yet ready: the
   *  session/theory currently loading and the last build line, e.g.
   *  "(MRS: Registers, last='Building MRS ...', 12s)". Empty if absent. */
  private def format_build(st: JSON.T): String =
    JSON.value(st, "build") match {
      case Some(b) =>
        val sess = JSON.string(b, "session").map("" + _).getOrElse("")
        val thy = JSON.string(b, "theory").map(": " + _).getOrElse("")
        val last = JSON.string(b, "last_message").map(m => " last='" + m + "'").getOrElse("")
        val el = JSON.long(b, "elapsed_s").map(s => " " + s + "s").getOrElse("")
        val reason = JSON.string(b, "reason").map(r => " reason=" + r).getOrElse("")
        val head = (sess + thy).trim
        "(" + (if (head.nonEmpty) head + "," else "") + last + reason + el + ")"
      case None => ""
    }

  /** Second status line: the options the server was started with. */
  private def format_options(st: JSON.T): String = {
    val o = JSON.value(st, "options").getOrElse(JSON.Object())
    val logic = JSON.string(o, "logic").getOrElse("?")
    val dirs = JSON.strings(o, "dirs").getOrElse(Nil)
    val incl = JSON.strings(o, "include_sessions").getOrElse(Nil)
    val opts = JSON.strings(o, "options").getOrElse(Nil)
    val no_build = JSON.bool(o, "no_build").getOrElse(false)
    val no_iq = !JSON.bool(o, "load_iq").getOrElse(true)
    val parts =
      List("logic=" + logic) :::
      (if (dirs.nonEmpty) List("dirs=" + dirs.mkString(",")) else Nil) :::
      (if (incl.nonEmpty) List("include=" + incl.mkString(",")) else Nil) :::
      (if (opts.nonEmpty) List("-o " + opts.mkString(" -o ")) else Nil) :::
      (if (no_build) List("no_build") else Nil) :::
      (if (no_iq) List("no_iq") else Nil)
    "    started with: " + parts.mkString("  ")
  }

  /** I/R status lines, if I/R was brought up: the client-facing repl.py port/token
   *  (raw I/R wire protocol) and, when present, the MCP server port/token (the
   *  repl_* tools). The in-prover ML_Repl is intentionally not advertised —
   *  clients go through the bridge / MCP. "no I/R" when --no-iq was given or
   *  bring-up didn't succeed. */
  private def format_ir(st: JSON.T): String =
    JSON.value(st, "ir") match {
      case Some(ir) =>
        val rp = JSON.int(ir, "repl_port").getOrElse(0)
        val rt = JSON.string(ir, "repl_token").map(" token=" + _).getOrElse("")
        val replLine = "    I/R repl.py: port=" + rp + rt + "  (raw I/R protocol)"
        val mcpLine =
          JSON.int(ir, "mcp_port") match {
            case Some(mp) =>
              val mt = JSON.string(ir, "mcp_token").map(" token=" + _).getOrElse("")
              "\n    I/R MCP:     port=" + mp + mt + "  (connect MCP repl_* here)"
            case None => ""
          }
        // The ready-to-paste one-shot client command (token shown inline here,
        // since `ic2 server status` is the sanctioned place tokens surface).
        val cliLine =
          JSON.string(ir, "repl_cli").map(c => "\n    I/R cli:     " + c).getOrElse("")
        replLine + mcpLine + cliLine
      case None => "    no I/R"
    }


  /* ============================= stop ============================== */

  private val stop_usage_text: String = """
Usage: isabelle ic2 server stop [OPTIONS]

  Options are:
    -n NAME      server name (default: the sole running server)
    --all        stop every running server

  Shut a server down (sends the `shutdown` op and waits for the connection to
  close). With no -n and a single server running, that server is stopped; with
  --all, every server is stopped.
"""

  def stop(args: List[String]): Unit = {
    if (wants_help(args)) { Output.writeln(stop_usage_text, stdout = true); sys.exit(2) }
    var name: Option[String] = None
    // --all is a long option (Getopts is single-letter only): strip it first.
    val all = args.contains("--all")
    val getopts = Getopts(stop_usage_text,
      "n:" -> (a => name = Some(a)))
    val rest = getopts(args.filterNot(_ == "--all"))
    if (rest.nonEmpty) getopts.usage()

    if (all) {
      if (name.isDefined) { Output.error_message("server stop: -n and --all are mutually exclusive"); sys.exit(2) }
      stop_all()
    } else stop_one(resolve_name(name))
  }

  /** Send `shutdown` to one server and wait for the connection to close;
   *  exit 3 if it can't be reached. For the single-target `stop`. */
  private def stop_one(name: String): Unit = {
    val io = open_connection(resolve_socket(name))
    try { drain_shutdown(io); Output.writeln("server " + quote(name) + " shut down") }
    finally io.close()
  }

  /** Write `shutdown` and read until the connection closes. */
  private def drain_shutdown(io: JSON_IO): Unit = {
    io.write(JSON.Object("op" -> "shutdown"))
    var done = false
    while (!done) io.read() match { case None => done = true; case Some(_) => }
  }

  /** `server stop --all`: stop every discovered server, best-effort — a server
   *  that can't be reached (e.g. a stale socket node) is reported and its node
   *  reclaimed, without aborting the rest. Exit 0 if all handled cleanly, 1 if
   *  any genuinely failed; a plain note (exit 0) when there were none. */
  private def stop_all(): Unit = {
    val names = Endpoint.list_names()
    if (names.isEmpty) {
      Output.writeln("no ic2 servers to stop (looked in " + Endpoint.dir.expand.implode + ")")
      sys.exit(0)
    }
    var failures = 0
    for (n <- names) {
      try_open(resolve_socket_quiet(n)) match {
        case Some((io, _)) =>
          try { drain_shutdown(io); Output.writeln("server " + quote(n) + " shut down") }
          catch { case _: Throwable => failures += 1; Output.error_message(n + ": failed to stop") }
          finally io.close()
        case None =>
          // No listener: a stale node. Reclaim it so it stops showing up.
          Output.writeln(n + ": not running (reclaiming stale socket)")
          Endpoint.remove(n)
      }
    }
    sys.exit(if (failures == 0) 0 else 1)
  }

  /** Socket path for `name` without the exit-on-missing behavior of
   *  `resolve_socket` — for `stop --all`, which iterates known names. */
  private def resolve_socket_quiet(name: String): Path = Endpoint.socket(name)


  /* ---- server attach (follow the console log) ---- */

  private val server_attach_usage_text: String = """
Usage: isabelle ic2 server attach [OPTIONS]

  Options are:
    -n NAME      server name (default: the sole running server)
    -c N         print the last N lines of existing log for context before
                 streaming (default: 40); -c 0 shows only new output
    --from-start replay the whole current log first, then stream

  Follow a backgrounded server's console log — the same output you would see
  had you run `server start` in the foreground, INCLUDING heap-build progress.
  Streams until the server shuts down (its socket disappears) or Ctrl-C.

  Reads $ISABELLE_HOME_USER/ic2/<name>.log; if the server was started with
  -L FILE, that is where its output went, so pass the same path via -L here.
"""

  /** `ic2 server attach`: tail -f the daemon's console log, so a backgrounded
   *  server's output (build progress and all) can be watched as if it ran in the
   *  foreground. Purely a log follower — no socket op — so it works in every
   *  phase, including during the heap build. Stops when the server's socket
   *  disappears (shutdown) or on Ctrl-C/EOF. */
  def server_attach(args: List[String]): Unit = {
    if (wants_help(args)) { Output.writeln(server_attach_usage_text, stdout = true); sys.exit(2) }
    var name: Option[String] = None
    var context = 40
    var from_start = false
    val plain = args.filterNot(a => a == "--from-start")
    from_start = args.contains("--from-start")
    val getopts = Getopts(server_attach_usage_text,
      "n:" -> (a => name = Some(a)),
      "L:" -> (a => log_override = Some(Path.explode(a))),
      "c:" -> (a => context = Value.Int.parse(a)))
    val rest = getopts(plain)
    if (rest.nonEmpty) getopts.usage()

    val server = resolve_name(name)
    val log = log_override.getOrElse(Endpoint.log_file(server))
    val jlog = Paths.get(log.expand.implode)

    // A server must exist (running or coming up) for attach to mean anything;
    // if neither socket nor log is present, there is nothing to follow.
    if (!Endpoint.exists(server) && !java.nio.file.Files.exists(jlog)) {
      Output.error_message("no server named " + quote(server) +
        " (no socket or log in " + Endpoint.dir.expand.implode + ")")
      sys.exit(3)
    }

    Output.writeln("attaching to " + quote(server) + " — following " +
      log.expand.implode + " (Ctrl-C to detach; the server keeps running)")
    follow_log(server, jlog, context, from_start)
  }

  /** A -L override for `server attach` (the server's log path if it was started
   *  with -L). Module-level rather than threaded through, mirroring how the
   *  other subcommands keep their parse simple. */
  private var log_override: Option[Path] = None

  /** Tail `jlog`, printing appended bytes as they arrive. Prints `context`
   *  trailing lines (or the whole file if `from_start`) before streaming. Exits
   *  when the server's socket node disappears (shutdown) or the process is
   *  interrupted. Waits for the file to appear if the server just launched. */
  private def follow_log(
    name: String, jlog: java.nio.file.Path, context: Int, from_start: Boolean
  ): Unit = {
    import java.io.RandomAccessFile
    // Wait briefly for the log to exist (server may have just launched).
    var waited = 0
    while (!java.nio.file.Files.exists(jlog) && waited < 20 && Endpoint.exists(name)) {
      Time.seconds(0.25).sleep(); waited += 1
    }
    if (!java.nio.file.Files.exists(jlog)) {
      Output.error_message("log file not found: " + jlog.toString); sys.exit(3)
    }

    val raf = new RandomAccessFile(jlog.toFile, "r")
    try {
      // Starting offset: whole file (from_start), else `context` lines back from
      // the end (0 -> only new output). We scan backwards for line starts.
      val len = raf.length()
      val start =
        if (from_start) 0L
        else if (context <= 0) len
        else {
          var pos = len
          var newlines = 0
          val buf = new Array[Byte](1)
          while (pos > 0 && newlines <= context) {
            pos -= 1
            raf.seek(pos)
            if (raf.read(buf) == 1 && buf(0) == '\n') newlines += 1
          }
          if (pos > 0) pos + 1 else 0L
        }
      raf.seek(start)

      val chunk = new Array[Byte](8192)
      var running = true
      // Detach cleanly on Ctrl-C (the server is unaffected — this only follows).
      val hook = new Thread(() => { running = false }, "ic2-attach-detach")
      Runtime.getRuntime.addShutdownHook(hook)

      var missing_socket_ticks = 0
      while (running) {
        val n = raf.read(chunk)
        if (n > 0) System.out.write(chunk, 0, n)
        else {
          System.out.flush()
          // No new data: stop once the server's socket is gone (shutdown). Give
          // it a couple of ticks so we drain the final lines written at exit.
          if (!Endpoint.exists(name)) {
            missing_socket_ticks += 1
            if (missing_socket_ticks >= 2) running = false
          } else missing_socket_ticks = 0
          if (running) Time.seconds(0.3).sleep()
        }
      }
      System.out.flush()
      try { Runtime.getRuntime.removeShutdownHook(hook) } catch { case _: Throwable => }
      if (!Endpoint.exists(name)) Output.writeln("\n[server " + quote(name) + " stopped]")
    } finally raf.close()
  }


  /* ---- progress UI ---- */

  /** A single running command reported alongside its theory in a progress
    *  event. Rendered indented under that theory's bar when its `elapsed_s`
    *  clears the client's --long-running threshold. `preview` is a single-line
    *  trimmed excerpt of the command source (empty when the daemon couldn't
    *  produce one, e.g. batch/pro-forma theory nodes), used to disambiguate
    *  otherwise-identical entries (two `by (…)` proofs on different lines). */
  case class Running_Command(
    keyword: String, line: Int, elapsed_s: Double, preview: String = "")

  case class Theory_Status(
    theory: String,
    percentage: Int,
    unprocessed: Int,
    running: Int,
    finished: Int,
    warned: Int,
    failed: Int,
    consolidated: Boolean,
    /** Server-side monotonic "last updated" stamp (0 if the server didn't
      * report one). The display sorts shown theories by this so it tracks
      * where the check is actively working. */
    updated: Long = 0L,
    long_running: List[Running_Command] = Nil
  ) {
    /** "Done" for display purposes: every command has completed, so the
      * server-side finished-based percentage reached 100 (see
      * SessionTools.progressPercentage). A theory merely pending
      * consolidation is already 100 here, so it drops from the in-flight
      * list rather than lingering at 99%. */
    def done: Boolean = percentage >= 100
  }

  trait Progress_UI {
    def started(theories: List[String]): Unit
    def progress(nodes: List[Theory_Status]): Unit
    def error(theory: String, file: String, line: Int, msg: String): Unit
    def server_error(msg: String): Unit
    def note(msg: String): Unit
    def close(): Unit
  }

  /** Terminal width from $COLUMNS, default 100. Shared by the live UI and the
   *  one-shot `check status` frame so they lay out identically. */
  private def term_width: Int = {
    val s = Isabelle_System.getenv("COLUMNS")
    if (s.nonEmpty) try Integer.parseInt(s) catch { case _: NumberFormatException => 100 }
    else 100
  }

  /** A 20-cell progress bar for a percentage. */
  private def progress_bar(percent: Int, w: Int = 20): String = {
    val p = percent.max(0).min(100)
    val filled = (p * w + 50) / 100
    "[" + ("█" * filled) + ("░" * (w - filled)) + "]"
  }

  /** Long-running commands under a bar, one indented line each. Format:
   *      "      by (line 42)  12.3s   by (spin 30; simp)"
   *  where the trailing text is a single-line source preview (when available)
   *  so two similarly-named commands on different lines are readable at a
   *  glance. Filtered by threshold; sorted longest-elapsed first; `<= 0`
   *  disables. Empty result if no command clears the threshold. */
  private def render_long_running(
    long_running: List[Running_Command], threshold_secs: Double
  ): List[String] = {
    if (threshold_secs <= 0) Nil
    else long_running.filter(_.elapsed_s >= threshold_secs)
      .sortBy(-_.elapsed_s)
      .map { rc =>
        val head = f"      ${rc.keyword}%s (line ${rc.line}%d)  ${rc.elapsed_s}%.1fs"
        if (rc.preview.isEmpty) head else head + "   " + rc.preview
      }
  }

  /** Render a check's per-theory status as a static frame: a summary header
   *  followed by one bar line per in-flight (not-yet-consolidated) theory,
   *  each optionally followed by an indented list of commands running longer
   *  than `long_running_secs`. This is the SAME layout the live ANSI_UI
   *  repaints, so `ic2 check status` prints exactly one frame of what
   *  `ic2 check attach` shows continuously. `max_rows` bounds the bar lines
   *  (with a "+N more" tail); pass all nodes. */
  def render_progress_frame(
    nodes: List[Theory_Status], max_rows: Int,
    long_running_secs: Double = DEFAULT_LONG_RUNNING_SECS
  ): List[String] = {
    val finished = nodes.count(_.done)
    val total = nodes.length
    val total_running = nodes.map(_.running).sum
    val total_unproc = nodes.map(_.unprocessed).sum
    val total_failed = nodes.map(_.failed).sum

    val header =
      f"  $finished%d/$total%d done   running=$total_running%d   unprocessed=$total_unproc%d" +
      (if (total_failed > 0) f"   FAILED=$total_failed%d" else "")

    // In-flight theories, most-recently-updated first (alphabetical tiebreak
    // among same-tick updates), bounded to max_rows. This is a one-shot frame
    // with no cross-tick state, so it can't do the live UI's sticky ordering —
    // it just shows the current last-updated bucket.
    val active = nodes.filter(n => !n.done).sortBy(n => (-n.updated, n.theory))
    val shown = active.take(max_rows)
    val name_w = (term_width - 50).max(20).min(60)
    val rows = shown.flatMap { n =>
      val name1 =
        if (n.theory.length > name_w) "..." + n.theory.substring(n.theory.length - name_w + 3)
        else n.theory.padTo(name_w, ' ')
      val running = if (n.running > 0) f"  ${n.running}%d running" else ""
      val bar = f"  $name1 ${progress_bar(n.percentage)} ${n.percentage}%3d%%$running"
      bar :: render_long_running(n.long_running, long_running_secs)
    }
    val more = if (active.size > shown.size) List(s"  ... +${active.size - shown.size} more in flight") else Nil
    header :: rows ::: more
  }

  /** No fancy UI: one event per line. `max_active` bounds how many in-flight
   *  theories appear in each progress line (Int.MaxValue = all). Commands
   *  running longer than `long_running_secs` are printed indented under the
   *  progress line for their theory. */
  class Plain_UI(
    max_active: Int = 20,
    long_running_secs: Double = DEFAULT_LONG_RUNNING_SECS
  ) extends Progress_UI {
    def started(theories: List[String]): Unit =
      Output.writeln("checking " + theories.length + " theory/theories: " +
        theories.mkString(", "))
    def progress(nodes: List[Theory_Status]): Unit = {
      // Most-recently-updated first, alphabetical tiebreak among same-tick.
      val active = nodes.filter(n => !n.done).sortBy(n => (-n.updated, n.theory))
      val (done, total) = (nodes.count(_.done), nodes.length)
      val shown = active.take(max_active)
      Output.writeln(s"[$done/$total done] " + shown.map(n =>
        s"${n.theory} ${n.percentage}%").mkString("; "))
      // Under each shown theory, indent its long-running commands.
      for (n <- shown; ln <- render_long_running(n.long_running, long_running_secs))
        Output.writeln("  [" + n.theory + "]" + ln.stripPrefix("     "))
    }
    def error(theory: String, file: String, line: Int, msg: String): Unit =
      Output.error_message(s"ERROR in $theory at $file:$line\n$msg")
    def server_error(msg: String): Unit = Output.error_message("server: " + msg)
    def note(msg: String): Unit = Output.writeln(msg)
    def close(): Unit = ()
  }

  /** ANSI live UI: shows the N in-flight theories the check most recently
   *  worked on, repainted in place. Consolidated theories drop off the list but
   *  are still counted in the header. Under each theory's bar, commands running
   *  longer than `long_running_secs` are listed indented, longest elapsed first.
   *
   *  The shown set is kept STABLE across ticks to avoid flicker: the bucket of
   *  the N most-recently-updated in-flight theories is computed each tick, but
   *  their on-screen order is preserved — survivors keep their previous slots,
   *  theories that fell out of the bucket are removed, and freshly-entering
   *  theories are added at the top. So a run touching a steady set of <N
   *  theories does not reshuffle them every tick (see `stable_order`). */
  class ANSI_UI(
    max_active: Int,
    out: PrintStream = System.out,
    long_running_secs: Double = DEFAULT_LONG_RUNNING_SECS
  ) extends Progress_UI {
    private var lines_drawn: Int = 0
    /** ASCII ESC = 0x1B, the CSI introducer. Written as a unicode escape
     *  (not a literal control byte) so it survives source tooling. */
    private val ESC: String = "\u001b"

    /** for each theory we've ever seen: last known status. */
    private val last_state =
      scala.collection.mutable.Map.empty[String, Theory_Status]

    /** Theory names currently on screen, in display order — carried across
      * ticks so the shown set only changes at the edges (drop-outs removed,
      * newcomers prepended) rather than being re-sorted every repaint. */
    private var displayed: List[String] = Nil

    private val width: Int = term_width

    private def clear_drawn(): Unit = {
      if (lines_drawn > 0) {
        // move up to the first drawn line, then clear from cursor to end of
        // screen in one shot (ESC[0J) — leaves the cursor where we redraw.
        out.print(ESC + "[" + lines_drawn + "A")
        out.print(ESC + "[0J")
        lines_drawn = 0
        out.flush()
      }
    }

    private def bar(percent: Int): String = progress_bar(percent)

    def started(theories: List[String]): Unit = synchronized {
      out.println("checking " + theories.length + " theory/theories")
      out.flush()
    }

    def progress(nodes: List[Theory_Status]): Unit = synchronized {
      clear_drawn()

      // Update last_state for every reported node.
      for (n <- nodes) last_state(n.theory) = n

      val finished = nodes.count(_.done)
      val total = nodes.length
      val total_running = nodes.map(_.running).sum
      val total_unproc = nodes.map(_.unprocessed).sum
      val total_failed = nodes.map(_.failed).sum

      val header =
        f"  $finished%d/$total%d done   running=$total_running%d   " +
        f"unprocessed=$total_unproc%d" +
        (if (total_failed > 0) f"   FAILED=$total_failed%d" else "")
      out.println(header)
      lines_drawn = 1

      // The bucket: the N in-flight theories the check most recently touched
      // (highest update stamp; alphabetical tiebreak among same-tick updates).
      val inflight = last_state.values.iterator.filter(!_.done).toList
      val bucket =
        inflight.sortBy(n => (-n.updated, n.theory)).take(max_active).map(_.theory)
      // Keep the display STABLE: survivors stay in their old relative order,
      // drop-outs are removed, and theories new to the bucket are prepended
      // (most-recently-updated first). This is (a)+(b)+(c) from the spec.
      val bucketSet = bucket.toSet
      val survivors = displayed.filter(bucketSet.contains)
      val survivorSet = survivors.toSet
      val newcomers = bucket.filterNot(survivorSet.contains)
      displayed = newcomers ::: survivors
      val active = displayed.flatMap(last_state.get)

      val name_w = (width - 50).max(20).min(60)
      for (n <- active) {
        val name1 =
          if (n.theory.length > name_w)
            "..." + n.theory.substring(n.theory.length - name_w + 3)
          else n.theory.padTo(name_w, ' ')
        val running = if (n.running > 0) f"  ${n.running}%d running" else ""
        val line = f"  $name1 ${bar(n.percentage)} ${n.percentage}%3d%%$running"
        out.println(line)
        lines_drawn += 1
        // Under this bar: commands running longer than the threshold, indented.
        for (row <- render_long_running(n.long_running, long_running_secs)) {
          out.println(row)
          lines_drawn += 1
        }
      }

      val total_active = last_state.values.count(!_.done)
      if (total_active > active.size) {
        out.println(s"  ... +${total_active - active.size} more in flight")
        lines_drawn += 1
      }
      out.flush()
    }

    def error(theory: String, file: String, line: Int, msg: String): Unit = synchronized {
      clear_drawn()
      Output.error_message(s"ERROR in $theory at $file:$line\n$msg")
    }

    def server_error(msg: String): Unit = synchronized {
      clear_drawn()
      Output.error_message("server: " + msg)
    }

    def note(msg: String): Unit = synchronized {
      clear_drawn()
      out.println(msg)
      out.flush()
    }

    def close(): Unit = synchronized {
      clear_drawn()
    }
  }
}
