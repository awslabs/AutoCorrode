/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      ic2/src/daemon.scala

Headless PIDE daemon — the `ic2 server start` subcommand. A persistent
`Headless.Session` driven over JSON-over-a-Unix-domain-socket.

Differences from `isabelle server`:
  - One process holds exactly one Headless.Session for its entire lifetime.
  - Live progress events are emitted continuously per `commands_changed` tick.
  - First-error stop: a `failed > 0` reading on any theory aborts the check
    and emits a single error event with file:line.
  - Cancel-on-disconnect: closing the client channel interrupts an in-flight
    use_theories.

Run modes:
  - Foreground (default): the process is the daemon; Ctrl-C terminates it.
  - --daemon: re-exec ourselves detached, poll for readiness, then return —
    leaving the server running in the background. Logs go to <name>.log (or
    the -L file). Stop it with `ic2 server stop`.

Access control is the socket's parent directory (mode 0700), not a token — see
endpoint.scala. There is no auth handshake.

Wire protocol: see ic2/README.md ("Wire protocol").
*/

package isabelle.ic2

import isabelle._

import java.io.IOException
import java.net.{StandardProtocolFamily, UnixDomainSocketAddress}
import java.nio.channels.{ServerSocketChannel, SocketChannel}
import java.nio.file.Paths
import java.util.concurrent.atomic.{AtomicBoolean, AtomicLong, AtomicReference}


object Daemon {

  /* ---- options as parsed from `ic2 server start` flags ---- */

  /** Everything the daemon was started with — echoed back by the `status`
   *  op so a client can see how a running server was configured. */
  case class Start_Options(
    logic: String,
    dirs: List[Path],
    include_sessions: List[String],
    option_specs: List[String],
    no_build: Boolean,
    load_iq: Boolean,
    load_mcp: Boolean
  ) {
    def json: JSON.Object.T =
      JSON.Object(
        "logic" -> logic,
        "dirs" -> dirs.map(_.implode),
        "include_sessions" -> include_sessions,
        "options" -> option_specs,
        "no_build" -> no_build,
        "load_iq" -> load_iq,
        "load_mcp" -> load_mcp)
  }


  /* ---- `ic2 server start` entry point ---- */

  val usage_text: String = """
Usage: isabelle ic2 server start [OPTIONS]

  Options are:
    --daemon     run in the background and return once the server is ready
                 (default: run in the foreground until Ctrl-C)
    --no-iq      do not bring up AutoCorrode's I/R interactive REPL against the
                 session (default: bring it up and spawn the repl.py bridge)
    --mcp        also stand up the MCP server in front of the I/R bridge
                 (default: off; the repl.py bridge + `repl.py cli` +
                 `ic2 repl-create` work without it)
    -L FILE      logging on FILE (in addition to stderr; default for --daemon
                 is $ISABELLE_HOME_USER/ic2/<name>.log)
    -d DIR       include session directory (repeatable)
    -i NAME      include session for theory namespace (repeatable)
    -l NAME      logic session name (default ISABELLE_LOGIC)
    -n NAME      server name (default: "default") -- chooses socket slot
    -o OPTION    override Isabelle option (NAME=VAL or NAME) (repeatable)
    -N           no build: assume the heap is up-to-date
    -v           verbose: log connection lifecycle to stderr (repeat -vv to
                 also dump events that arrived after a client disconnected,
                 confirming use_theories was aborted)

  Start the headless PIDE daemon. Same option-handling shape as
  `isabelle jedit`: the merged Options flow into `Headless.Resources` and
  `Build.build`, so `-o process_policy=...` also wraps the underlying ML
  process (cf. I/P).

  Unless --no-iq is given, the daemon also brings up AutoCorrode's I/R
  interactive REPL against the resident session (loading the I/R ML, opening the
  in-prover ML_Repl, and spawning the ir/repl.py bridge); the resulting
  client-facing repl.py port and token are shown by `isabelle ic2 server status`.

  The daemon listens on a Unix-domain socket at
  $ISABELLE_HOME_USER/ic2/<name>.sock; the parent directory is created mode
  0700, which is the access boundary. Stop it with `isabelle ic2 server stop`.
"""

  def start(args: List[String]): Unit = {
    // Help intercept before Getopts (which only knows Isabelle's `-?`): make
    // `help` / `--help` / `-h` print usage uniformly, as the other commands do.
    if (args.exists(a => a == "help" || a == "--help" || a == "-h")) {
      Output.writeln(usage_text, stdout = true); sys.exit(2)
    }
    // `--daemon` / `--no-iq` are long options, which Isabelle's single-letter
    // Getopts can't express (and `--` is its end-of-options marker). Strip them
    // ourselves, then hand the remaining single-letter flags to Getopts.
    val daemon = args.contains("--daemon")
    val load_iq = !args.contains("--no-iq")
    val load_mcp = args.contains("--mcp")
    val rest_args = args.filterNot(a => a == "--daemon" || a == "--no-iq" || a == "--mcp")

    var logic = Isabelle_System.getenv("ISABELLE_LOGIC")
    if (logic.isEmpty) logic = "HOL"
    var dirs: List[Path] = Nil
    var include_sessions: List[String] = Nil
    var option_specs: List[String] = Nil
    var no_build: Boolean = false
    var name: String = "default"
    var verbose_level: Int = 0
    var log_file: Option[Path] = None

    val getopts = Getopts(usage_text,
      "L:" -> (a => log_file = Some(Path.explode(a))),
      "d:" -> (a => dirs ::= Path.explode(a)),
      "i:" -> (a => include_sessions ::= a),
      "l:" -> (a => logic = a),
      "n:" -> (a => name = a),
      "o:" -> (a => option_specs ::= a),
      "N"  -> (_ => no_build = true),
      "v"  -> (_ => verbose_level = verbose_level + 1))

    val leftover = getopts(rest_args)
    if (leftover.nonEmpty) getopts.usage()

    val start_options =
      Start_Options(logic, dirs.reverse, include_sessions.reverse,
        option_specs.reverse, no_build, load_iq, load_mcp)

    if (daemon) launch_daemon(name, log_file, args)
    else {
      val verbose: Boolean = verbose_level >= 1
      val trace_dead_events: Boolean = verbose_level >= 2
      val progress: Progress = log_file match {
        case Some(p) => new Combined_Progress(verbose, p)
        case None => new Console_Progress(verbose = verbose, stderr = true)
      }
      // Default `show_states` on so per-command proof STATE messages land in the
      // snapshot for get_context_info / get_command_info to read. It emits
      // Output.state from the toplevel transition (Isar/toplevel.ML), so it fires
      // for every evaluated command even headless — unlike `print_state`, a print
      // function gated on a visible perspective (which Headless.Session leaves
      // empty). editor_output_state stays on for parity with jEdit/VSCode. Listed
      // FIRST so an explicit `-o show_states=...` still overrides.
      val options = Options.init(specs =
        (Options.Spec.make("show_states=true") ::
          Options.Spec.make("editor_output_state=true") ::
          option_specs.reverse.map(Options.Spec.make)))
      run(options, name, start_options, trace_dead_events, progress)
    }
  }


  /* ---- --daemon: detach, poll for readiness, report, return ---- */

  /** Background-launch `ic2 server start` (minus --daemon), redirecting its output to
   *  the log, then poll the socket until the server greets us — or the child
   *  dies, or we give up waiting on a slow heap build. */
  private def launch_daemon(
    name: String, log_file: Option[Path], orig_args: List[String]
  ): Unit = {
    Endpoint.secure_dir()

    // Fast clash check before spawning, so `--daemon` on a busy name fails
    // immediately rather than spawning a child that races to the same error.
    if (Endpoint.exists(name) && socket_alive(name)) {
      Output.error_message("server " + quote(name) +
        " already running; stop it (isabelle ic2 server stop -n " + name +
        ") or choose a different -n NAME")
      sys.exit(1)
    }

    // Where the background server's output lands. With -L the child's own
    // File_Progress already writes there, so we send its console stream to
    // /dev/null to avoid duplicating every line; otherwise the console stream
    // IS the log.
    val log = log_file.getOrElse(Endpoint.log_file(name))
    val redirect = log_file match {
      case Some(_) => "/dev/null"
      case None => log.expand.implode
    }

    val isabelle = Path.explode("$ISABELLE_HOME/bin/isabelle")
    val child_args = orig_args.filterNot(_ == "--daemon")
    // nohup + stdin from /dev/null + detaching `&` so the child outlives this
    // process and its controlling terminal. `echo $!` hands us the child pid.
    val script =
      "nohup " + File.bash_path(isabelle) + " ic2 server start " + Bash.strings(child_args) +
      " < /dev/null >> " + Bash.string(redirect) + " 2>&1 & echo $!"
    val res = Isabelle_System.bash(script)
    if (res.rc != 0) {
      Output.error_message("failed to launch daemon: " + res.err)
      sys.exit(1)
    }
    val child_pid: Option[Long] = Value.Long.unapply(res.out.trim)

    Output.writeln("starting daemon " + quote(name) + " (logging to " +
      log.expand.implode + ") ...")

    // Poll the socket (now bound before the heap build, so it answers during
    // bring-up): `state:ready` wins, `state:failed` loses, a dead child loses
    // fast; a still-building/loading server keeps us waiting until the deadline,
    // then we return success and point at the log rather than block on a cold
    // heap build. The poll is silent — follow the build with `server attach` or
    // `server status`; only the terminal ready/failed/timeout line is printed.
    val deadline = System.currentTimeMillis() + 30000
    // outcome: Some(Right(())) ready, Some(Left(msg)) failed/died, None timed out.
    val deadline_msg = "daemon still starting (building the heap?); follow " +
      log.expand.implode + " or run: isabelle ic2 server status -n " + name
    var outcome: Option[Either[String, Unit]] = None
    while (outcome.isEmpty && System.currentTimeMillis() < deadline) {
      ping_status(name) match {
        case Some(st) =>
          JSON.string(st, "state").getOrElse("ready") match {
            case "ready" =>
              Output.writeln("daemon ready: " + Client.format_status(name, st))
              outcome = Some(Right(()))
            case "failed" =>
              outcome = Some(Left("daemon startup failed: " +
                Client.format_status(name, st) + "; see " + log.expand.implode))
            case _ =>
              Time.seconds(0.5).sleep()   // still coming up — wait quietly
          }
        case None =>
          val child_dead = child_pid.exists(p => !ProcessHandle.of(p).isPresent)
          if (child_dead) outcome = Some(Left("daemon exited during startup; see " + log.expand.implode))
          else Time.seconds(0.5).sleep()
      }
    }

    outcome match {
      case Some(Right(())) => sys.exit(0)
      case Some(Left(msg)) => Output.error_message(msg); sys.exit(1)
      case None => Output.writeln(deadline_msg); sys.exit(0)
    }
  }

  /** Connect, read the `ready` greeting, send `status`, return the reply —
   *  or None if the server isn't reachable / didn't answer. Shared by the
   *  --daemon readiness poll and `ic2 server status`. */
  def ping_status(name: String): Option[JSON.T] = {
    val addr = UnixDomainSocketAddress.of(Paths.get(Endpoint.socket(name).expand.implode))
    val channel =
      try SocketChannel.open(addr)
      catch { case _: IOException => return None }
    val io = JSON_IO(channel)
    try {
      io.read(15000) match {
        case JSON_IO.Value(t) if JSON.string(t, "event").contains("ready") =>
          io.write(JSON.Object("op" -> "status"))
          io.read(15000) match {
            case JSON_IO.Value(s) if JSON.string(s, "event").contains("status") => Some(s)
            case _ => None
          }
        case _ => None
      }
    } finally io.close()
  }


  /* progress wrapper that also writes to a log file */

  private class Combined_Progress(verbose0: Boolean, log: Path) extends Progress {
    private val console = new Console_Progress(verbose = verbose0, stderr = true)
    private val file = new File_Progress(log, verbose = true)
    override def verbose: Boolean = verbose0
    override def output(msgs: Progress.Output): Unit = {
      console.output(msgs); file.output(msgs)
    }
    override def nodes_status(ns: Progress.Nodes_Status): Unit = {
      console.nodes_status(ns); file.nodes_status(ns)
    }
    override def stop(): Unit = { super.stop(); console.stop(); file.stop() }
  }


  /* ---- startup lifecycle phase (for the status op during a heap build) ---- */

  /** Where the daemon is in its bring-up. The socket is bound while still in
   *  `Building`, so `status`/`shutdown` work throughout; session-dependent ops
   *  (check/query/repl) are refused until `Ready`. */
  object Phase extends Enumeration {
    val Building, Loading, StartingSession, StartingIR, Ready, ShuttingDown, Failed = Value
  }

  /** Live startup state, shared between the bring-up worker (which advances the
   *  phase and records build progress) and connection handlers (which report it
   *  via `status`). All access is through the synchronized methods. */
  private class Build_Status {
    private var phase: Phase.Value = Phase.Building
    // Latest human-readable build line (e.g. "Building MRS ...", "Finished HOL")
    // and the theory currently loading, for a live "what is it doing" readout.
    private var last_message: String = "starting"
    private var current_session: String = ""
    private var current_theory: String = ""
    private var fail_reason: String = ""
    private val start_ms: Long = System.currentTimeMillis()

    def set_phase(p: Phase.Value): Unit = synchronized { phase = p }
    def get_phase: Phase.Value = synchronized { phase }
    def is_ready: Boolean = synchronized { phase == Phase.Ready }
    def fail(reason: String): Unit = synchronized { phase = Phase.Failed; fail_reason = reason }

    def note_message(msg: String): Unit = synchronized {
      val trimmed = msg.trim
      if (trimmed.nonEmpty) last_message = trimmed
    }
    def note_theory(session: String, theory: String): Unit = synchronized {
      if (session.nonEmpty) current_session = session
      if (theory.nonEmpty) current_theory = theory
    }

    /** Phase as the wire/CLI token used in the status JSON `state` field. */
    def phase_token: String = synchronized {
      phase match {
        case Phase.Building => "building"
        case Phase.Loading => "loading"
        case Phase.StartingSession => "starting_session"
        case Phase.StartingIR => "starting_ir"
        case Phase.Ready => "ready"
        case Phase.ShuttingDown => "shutting_down"
        case Phase.Failed => "failed"
      }
    }

    /** The `build` sub-object for status_json while not yet ready (the details a
     *  human wants while waiting on a cold heap): elapsed, last line, theory. */
    def json: JSON.Object.T = synchronized {
      JSON.Object(
        "phase" -> phase_token,
        "elapsed_s" -> ((System.currentTimeMillis() - start_ms) / 1000),
        "last_message" -> last_message) ++
      (if (current_session.nonEmpty) JSON.Object("session" -> current_session) else JSON.Object()) ++
      (if (current_theory.nonEmpty) JSON.Object("theory" -> current_theory) else JSON.Object()) ++
      (if (fail_reason.nonEmpty) JSON.Object("reason" -> fail_reason) else JSON.Object())
    }
  }

  /** Progress decorator that records build activity into a Build_Status while
   *  forwarding everything to the underlying (console+file) progress. Captures
   *  the writeln/warning/error lines ("Building MRS ...") and per-theory
   *  `Theory` messages (session + theory being loaded) so the status op can
   *  report what the heap build is doing. */
  private class Capturing_Progress(under: Progress, status: Build_Status) extends Progress {
    override def verbose: Boolean = under.verbose
    override def output(msgs: Progress.Output): Unit = {
      for (msg <- msgs) msg match {
        case thy: Progress.Theory => status.note_theory(thy.session, thy.theory)
        case _ =>
      }
      msgs.lastOption.foreach(m => status.note_message(m.message.text))
      under.output(msgs)
    }
    override def nodes_status(ns: Progress.Nodes_Status): Unit = under.nodes_status(ns)
    // stopped is what Build.build polls to cancel: forward to the shared flag so
    // `stop()` on this wrapper (invoked on shutdown) aborts an in-flight build.
    override def stop(): Unit = { super.stop(); under.stop() }
    override def stopped: Boolean = super.stopped || under.stopped
  }


  /** Best-effort liveness probe: does something accept a connection on this
   *  socket path right now? A leftover socket node from a crashed server has
   *  no listener, so `connect` fails — telling us the node is stale and safe
   *  to reclaim. */
  private def socket_alive(name: String): Boolean = {
    val addr = UnixDomainSocketAddress.of(Paths.get(Endpoint.socket(name).expand.implode))
    try { val c = SocketChannel.open(addr); c.close(); true }
    catch { case _: IOException => false }
  }


  /* ---- server-wide live state (for the status op) ---- */

  /** Counters + late-bound session shared across all connections of one running
   *  daemon. The socket is bound (and this state created) BEFORE the heap build,
   *  so `session`/`resources`/`ir` start empty and are filled in by the bring-up
   *  worker once ready; `build` tracks the meanwhile phase. `status`/`shutdown`
   *  work in every phase; session-dependent ops guard on `session_ready`. */
  private class Server_State(
    val opts: Start_Options, val pid: Long, val build: Build_Status
  ) {
    private val start_ms: Long = System.currentTimeMillis()
    /** Working directory of the server process at start — reported by `status`
     *  so a user staring at several servers can tell which is which. Captured
     *  eagerly so it reflects the launch environment even if `user.dir` mutates
     *  later. */
    private val cwd: String =
      try new java.io.File(".").getCanonicalPath
      catch { case _: Throwable =>
        val ud = System.getProperty("user.dir"); if (ud == null) "?" else ud
      }
    /** Wall-clock of the last real client interaction (any op other than
     *  status/shutdown probes). Used by `ic2 server status` to spot stale
     *  servers. Initialised to start_ms so a freshly-started server that has
     *  never been touched still reads as "recent" until the first status poll. */
    private val last_activity_ms = new AtomicLong(start_ms)
    val active_connections = new AtomicLong(0L)

    /** Note that the server was just interfaced with (called for every non-poll
     *  op). status/shutdown are deliberately NOT counted so that a monitor
     *  polling `status` doesn't mask an otherwise idle server. */
    def note_activity(): Unit = last_activity_ms.set(System.currentTimeMillis())

    // Filled in when the bring-up worker completes each stage. Volatile: written
    // by the worker thread, read by connection-handler threads.
    @volatile private var session_opt: Option[Headless.Session] = None
    @volatile private var resources_opt: Option[Headless.Resources] = None
    @volatile private var ir_opt: Option[IQ.IR_Endpoint] = None
    @volatile private var ir_client_opt: Option[IRClient] = None

    def bind_session(s: Headless.Session, r: Headless.Resources): Unit = {
      session_opt = Some(s); resources_opt = Some(r)
    }
    def bind_ir(ep: Option[IQ.IR_Endpoint], client: Option[IRClient]): Unit = {
      ir_opt = ep; ir_client_opt = client
    }
    def session: Option[Headless.Session] = session_opt
    def resources: Option[Headless.Resources] = resources_opt
    def ir: Option[IQ.IR_Endpoint] = ir_opt
    def ir_client: Option[IRClient] = ir_client_opt
    /** True once the session is up: session-dependent ops may proceed. */
    def session_ready: Boolean = build.is_ready && session_opt.isDefined

    private def uptime_s: Long = (System.currentTimeMillis() - start_ms) / 1000

    // busy reflects the single in-flight check, set on EITHER the wire op or the
    // MCP `check` tool (at most one check runs server-wide).
    def status_json: JSON.Object.T =
      JSON.Object(
        "event" -> "status",
        "session" -> opts.logic,
        // The lifecycle phase: "building"/"loading"/"starting_session"/
        // "starting_ir" while coming up, "ready" once serving, "failed" if
        // bring-up errored. A client can wait on this instead of a blank socket.
        "state" -> build.phase_token,
        "pid" -> pid,
        "uptime_s" -> uptime_s,
        // Absolute wall-clock (ms since the epoch) of server start and of the
        // last real client interaction, plus the server's CWD at launch. Reported
        // as ms rather than pre-formatted strings so the client controls locale
        // / timezone / relative rendering.
        "started_ms" -> start_ms,
        "last_activity_ms" -> last_activity_ms.get,
        "cwd" -> cwd,
        "busy" -> Check.busy,
        "checks_in_flight" -> (if (Check.busy) 1 else 0),
        // Active connections include the one issuing this status query.
        "connections" -> active_connections.get,
        "options" -> opts.json) ++
      // While not yet ready, a `build` sub-object with the heap-build readout.
      (if (build.is_ready) JSON.Object() else JSON.Object("build" -> build.json)) ++
      // The I/R bridge endpoint, if I/Q was loaded and brought one up.
      (ir_opt match { case Some(ep) => JSON.Object("ir" -> ep.json); case None => JSON.Object() })
  }


  /* run the daemon (foreground) */

  def run(
    options: Options,
    name: String,
    start_options: Start_Options,
    trace_dead_events: Boolean,
    progress: Progress
  ): Unit = {
    val logic = start_options.logic
    val dirs = start_options.dirs
    val no_build = start_options.no_build

    /* prepare the heap + session background. Any startup failure (undefined
     * session, missing heap, failed build) exits 1 — exit 2 is reserved for
     * flag-parse / usage errors. */

    def startup_failed(msg: String): Nothing = {
      progress.echo_error_message(msg)
      sys.exit(1)
    }

    // Fail fast — before the (slow) heap build — on the two things we can
    // check from the name alone: an over-long socket path (the OS caps AF_UNIX
    // paths at ~104 bytes, and a raw BindException later would be cryptic), and
    // an obvious clash with a live server of the same name. The authoritative
    // reclaim/clobber check happens at bind time below.
    Endpoint.secure_dir()
    val socket_path_len = Endpoint.socket(name).expand.implode.getBytes("UTF-8").length
    if (socket_path_len > 100)
      startup_failed("server name " + quote(name) + " makes the socket path too long (" +
        socket_path_len + " bytes; the OS limit is ~104). Choose a shorter -n NAME.")
    if (Endpoint.exists(name) && socket_alive(name))
      startup_failed("server " + quote(name) +
        " already running; stop it or choose a different -n NAME")

    /* shared state + idempotent shutdown
     *
     * Register the shutdown hook up front, so that if anything in the bring-up
     * worker below throws, the hook still tears down whatever was created.
     * session/IR/repl.py/MCP are filled in by the worker once they exist; the
     * hook only touches what is present, and only removes the socket node if WE
     * bound it (so a failed start can't delete another server's slot). */

    val shutdown_initiated = new AtomicBoolean(false)
    @volatile var socket_opt: Option[ServerSocketChannel] = None
    @volatile var socket_bound: Boolean = false
    @volatile var session_opt: Option[Headless.Session] = None
    @volatile var repl_py_opt: Option[Process] = None
    @volatile var mcp_opt: Option[McpServer] = None
    val build_status = new Build_Status
    // The build/session progress is captured into build_status so `status` can
    // report what the heap build is doing, while still logging as before.
    val cap_progress = new Capturing_Progress(progress, build_status)

    def stop_session_bounded(s: Headless.Session, timeout_ms: Long = 10000): Unit = {
      val t = new Thread(new Runnable {
        def run(): Unit = try { s.stop() } catch { case _: Throwable => }
      }, "ic2-session-stop")
      t.setDaemon(true)
      t.start()
      t.join(timeout_ms)
      if (t.isAlive)
        progress.echo_error_message(
          "session.stop() did not complete within " + timeout_ms +
          "ms; ML process may be orphaned")
    }

    def shutdown(): Unit = {
      // CAS gate: first caller runs the body; later callers return at once
      // rather than blocking behind a lock while session.stop() drains.
      if (shutdown_initiated.compareAndSet(false, true)) {
        build_status.set_phase(Phase.ShuttingDown)
        progress.echo("Shutting down ...")
        // Cancel an in-flight heap build (Build.build polls progress.stopped)
        // and any running check, so `stop` during bring-up returns promptly.
        cap_progress.stop()
        Check.current.foreach(j => try { j.cancel("shutdown") } catch { case _: Throwable => })
        socket_opt.foreach(s => try { s.close() } catch { case _: IOException => })
        if (socket_bound) Endpoint.remove(name)
        // Stop the MCP server (closes its listener + worker pool) before the
        // bridge/session it talks to.
        mcp_opt.foreach(s => try { s.stop() } catch { case _: Throwable => })
        // Tear down the I/R bridge (repl.py) before the session: it holds a TCP
        // connection into the ML_Repl that session.stop() would otherwise drop.
        repl_py_opt.foreach { p =>
          try { p.destroy(); if (!p.waitFor(5, java.util.concurrent.TimeUnit.SECONDS)) p.destroyForcibly() }
          catch { case _: Throwable => }
        }
        session_opt.foreach(stop_session_bounded(_))
      }
    }

    val shutdown_thread = new Thread(new Runnable {
      def run(): Unit = shutdown()
    }, "ic2-shutdown-hook")
    Runtime.getRuntime.addShutdownHook(shutdown_thread)

    /* Unix-domain socket — bind FIRST, before the (slow) heap build, so the
     * server is discoverable via `status` and stoppable via `stop` from the
     * moment it starts, even while a heap is still building. Reclaim a stale
     * node first: the JVM does not unlink the socket file on close, so a crashed
     * predecessor can leave one behind, and bind() refuses to overwrite it. */

    val socket_path = Endpoint.socket(name)
    val jpath = Paths.get(socket_path.expand.implode)
    if (Endpoint.exists(name)) {
      if (socket_alive(name))
        startup_failed("server " + quote(name) +
          " already running; stop it or choose a different -n NAME")
      progress.echo("Reclaiming stale socket node " + socket_path.expand.implode)
      Endpoint.remove(name)
    }

    val socket = ServerSocketChannel.open(StandardProtocolFamily.UNIX)
    socket.bind(UnixDomainSocketAddress.of(jpath), 50)
    socket_opt = Some(socket)
    socket_bound = true
    val pid = ProcessHandle.current().pid()
    val state = new Server_State(start_options, pid, build_status)
    progress.echo("Listening on " + socket_path.expand.implode + " (pid " + pid + ")")

    /* bring-up worker: build the heap, load the session, bring up I/R — all the
     * slow work — off the accept loop so the socket serves `status`/`shutdown`
     * throughout. Advances build_status through its phases; on ready, publishes
     * the session into `state`. A failure records Phase.Failed (visible via
     * status) and leaves the socket up so a client still learns the outcome and
     * can `stop`. */
    // Run the bring-up on an Isabelle_Thread (Build.build / start_session need an
    // Isabelle-managed thread — a plain java.lang.Thread fails with
    // "Isabelle-specific thread required"). Daemon so it never blocks JVM exit.
    Isabelle_Thread.fork(name = "ic2-bringup", daemon = true) {
        // Aborted if `stop` arrives mid-bring-up: each stage checks this and
        // skips the rest (no non-local returns — those are illegal in a lambda).
        def live: Boolean = !shutdown_initiated.get
        try {
          // Failures here `error(...)` rather than sys.exit: the catch below
          // records Phase.Failed and leaves the socket up, so a client still
          // learns the outcome (and can `stop`) instead of hitting a dead node.
          if (no_build) {
            if (Store(options).get_session(logic).heap.isEmpty)
              error("No heap image for " + logic + " (and -N was given). " +
                "Rerun without -N, or run: isabelle build -b " + logic)
          }
          else if (live) {
            build_status.set_phase(Phase.Building)
            progress.echo("Building " + logic + " (and ancestors) ...")
            val results =
              Build.build(options,
                selection = Sessions.Selection.session(logic),
                progress = cap_progress,
                build_heap = true,
                dirs = dirs)
            if (live && !results.ok)   // a stopped build reports !ok; don't misreport
              error("Heap build failed (rc=" + results.rc + ")")
          }

          if (live) {
            build_status.set_phase(Phase.Loading)
            progress.echo("Loading session background for " + logic + " ...")
            val session_background =
              Sessions.background(options, logic, progress = cap_progress,
                dirs = dirs, include_sessions = start_options.include_sessions).check_errors
            val resources = Headless.Resources(options, session_background)

            if (live) {
              build_status.set_phase(Phase.StartingSession)
              progress.echo("Starting Headless.Session ...")
              val session = resources.start_session(progress = cap_progress)
              session_opt = Some(session)
              state.bind_session(session, resources)
              progress.echo("Session ready: " + logic)

              // Feed the raw `command_timing` protocol stream into the
              // session-global timing tracker, which is what drives the
              // "long-running commands under each bar" display. Subscribed
              // once, for the session's lifetime; see Check.Timing_Tracker.
              val tracker = new Check.Timing_Tracker
              Check.bindTimingTracker(tracker)
              session.command_timings +=
                isabelle.Session.Consumer[isabelle.Session.Command_Timing](
                  "ic2-timing-tracker")(tracker.note)

              /* I/R (unless --no-iq): bring up the interactive REPL against the
               * resident session via the session-generic IRLauncher — load the I/R
               * ML, open the in-prover ML_Repl, spawn the repl.py bridge. The MCP
               * server in front of it is stood up only with --mcp. Best-effort:
               * failures only disable I/R+MCP, never checking. The repl.py child
               * and any MCP server are owned by us (shutdown() tears them down). */
              if (live && start_options.load_iq) {
                build_status.set_phase(Phase.StartingIR)
                IQ.start(session, resources, progress, loadMcp = start_options.load_mcp) match {
                  case Some(started) =>
                    repl_py_opt = Some(started.repl_py)
                    mcp_opt = started.mcp
                    // Publish the endpoint AND the connected I/R client (the
                    // client backs the `repl` op, which resolves a source
                    // location to a command id server-side and creates a REPL).
                    state.bind_ir(Some(started.endpoint), Some(started.client))
                  case None => state.bind_ir(None, None)
                }
              }
              if (live) {
                build_status.set_phase(Phase.Ready)
                // Count reaching Ready as an activity so `last=` doesn't
                // display the whole heap-build wall-clock as "inactivity" the
                // moment the server first becomes usable — until a real op
                // arrives, "last" is the readiness transition, not launch.
                state.note_activity()
                progress.echo("Ready.")
              }
            }
          }
        }
        catch {
          case ERROR(msg) =>
            build_status.fail(msg)
            progress.echo_error_message(msg)
          case _: InterruptedException => // shutting down
        }
    }

    /* accept loop — runs immediately, serving `status`/`shutdown` (and, once
     * ready, the session-dependent ops) from the moment the socket is bound. */

    val next_conn_id = new AtomicLong(0L)

    try {
      while (!shutdown_initiated.get) {
        val client =
          try { socket.accept() }
          catch {
            case _: IOException if shutdown_initiated.get || !socket.isOpen => null
            case e: IOException =>
              progress.echo_error_message("accept: " + e.getMessage)
              null
          }
        if (client != null) {
          val conn_id = next_conn_id.incrementAndGet()
          progress.echo("[conn " + conn_id + "] accepted", verbose = true)
          val handler = new Connection_Handler(state, progress,
            conn_id = conn_id, trace_dead_events = trace_dead_events,
            close_server = () => shutdown())
          val t = new Thread(new Runnable {
            def run(): Unit = handler.run(client)
          }, "ic2-conn-" + conn_id)
          t.setDaemon(true)
          t.start()
        }
      }
    }
    finally {
      shutdown()
    }
  }


  /* -------------------------------------------------------------------
   * Connection handler — runs in its own thread, owns one client channel.
   * ------------------------------------------------------------------- */

  private class Connection_Handler(
    state: Server_State,
    server_progress: Progress,
    conn_id: Long,
    trace_dead_events: Boolean,
    close_server: () => Unit
  ) {

    /** The foreground check this connection started (None when idle or after it
     *  detached). Set when a foreground `check` starts, cleared when it finishes;
     *  on disconnect we cancel exactly this job, so the session isn't left held.
     *  A DETACHED check is never stored here — it outlives the connection. */
    private val attached = new AtomicReference[Option[Check.Job]](None)

    /** The session+resources if the daemon is ready, else None. */
    private def ready_session: Option[(Headless.Session, Headless.Resources)] =
      (state.session, state.resources) match {
        case (Some(s), Some(r)) if state.session_ready => Some((s, r))
        case _ => None
      }

    private def not_ready_msg: String =
      "server not ready (" + state.build.phase_token +
        "): the session is still coming up — check `ic2 server status`"

    /** Run `body` with the session + resources, or reply with a "still
     *  starting" error if the daemon is not yet ready (heap still building,
     *  session loading, or bring-up failed). The query / repl ops funnel through
     *  this so they never touch a null session; `check` uses `ready_session`
     *  directly so its not-ready path can also emit a terminal `finished`. */
    private def with_session(io: JSON_IO)(body: (Headless.Session, Headless.Resources) => Unit): Unit =
      ready_session match {
        case Some((s, r)) => body(s, r)
        case None => io.write(server_error(not_ready_msg))
      }

    /** Verbose-only log line, prefixed with this connection's id. */
    private def vlog(msg: String): Unit =
      server_progress.echo("[conn " + conn_id + "] " + msg, verbose = true)

    /** Always-shown log line (conn-prefixed), for high-level check boundaries —
     *  a check arriving and how it terminated. The chatty per-event trace stays
     *  on vlog (verbose only). */
    private def clog(msg: String): Unit =
      server_progress.echo("[conn " + conn_id + "] " + msg)

    def run(client: SocketChannel): Unit = {
      val sink: JSON_IO.Sink =
        if (trace_dead_events) new JSON_IO.Stderr_Sink("conn " + conn_id)
        else JSON_IO.Drop_Sink
      val io = JSON_IO(client, sink)
      state.active_connections.incrementAndGet()
      try {
        // No auth: the 0700 socket directory is the access boundary. Greet the
        // client so it knows the daemon is live and which logic it serves.
        io.write(JSON.Object("event" -> "ready", "session" -> state.opts.logic,
          "pid" -> state.pid))

        var done = false
        while (!done) {
          io.read() match {
            case None =>
              vlog("client closed connection (EOF)")
              done = true
            case Some(t) =>
              JSON.string(t, "op") match {
                case Some("check") =>
                  state.note_activity()
                  val files = JSON.strings(t, "files").getOrElse(Nil)
                  val detach = JSON.bool(t, "detach").getOrElse(false)
                  val line = JSON.int(t, "line")
                  clog("check requested: " + files.length + " file(s)" +
                    line.map(l => " up to line " + l).getOrElse("") +
                    (if (detach) " [detached]" else "") + ": " + files.mkString(", "))
                  ready_session match {
                    case Some((session, resources)) =>
                      if (detach) start_check_detached(io, session, resources, files, line)
                      else start_check_blocking(io, session, resources, files, line)
                    // Not ready: fail_check emits server_error AND a terminal
                    // `finished`, so a streaming foreground check client exits
                    // rather than hanging waiting for events that never come.
                    case None => fail_check(io, not_ready_msg)
                  }
                case Some("check_status") =>
                  state.note_activity()
                  vlog("op=check_status")
                  io.write(check_status_reply())
                case Some("check_attach") =>
                  state.note_activity()
                  vlog("op=check_attach")
                  check_attach(io)
                case Some("check_cancel") =>
                  state.note_activity()
                  vlog("op=check_cancel")
                  io.write(check_cancel_reply())
                case Some("query") =>
                  state.note_activity()
                  vlog("op=query tool=" + JSON.string(t, "tool").getOrElse("<missing>"))
                  with_session(io) { (session, _) => io.write(query_reply(session, t)) }
                case Some("repl") =>
                  state.note_activity()
                  vlog("op=repl")
                  with_session(io) { (session, _) => io.write(repl_reply(session, t)) }
                case Some("load-files") =>
                  state.note_activity()
                  val files = JSON.strings(t, "files").getOrElse(Nil)
                  vlog("op=load-files: " + files.length + " file(s): " + files.mkString(", "))
                  with_session(io) { (session, resources) =>
                    io.write(load_files_reply(session, resources, files)) }
                case Some("status") =>
                  // Deliberately NOT counted as activity: a monitor polling
                  // `status` shouldn't hide an otherwise idle server.
                  vlog("op=status")
                  io.write(state.status_json)
                case Some("shutdown") =>
                  // Also not counted: shutdown is the end of activity, not a use.
                  vlog("op=shutdown")
                  io.write(JSON.Object("event" -> "shutting_down"))
                  done = true
                  close_server()
                case Some(other) =>
                  vlog("op=unknown: " + other)
                  io.write(server_error("unknown op: " + other))
                case None =>
                  vlog("op=<missing>")
                  io.write(server_error("missing op"))
              }
          }
        }
      } catch {
        case e: Throwable =>
          // Log the full detail server-side; send the client an opaque
          // message so absolute paths / internal class names don't leak.
          server_progress.echo_error_message("[conn " + conn_id +
            "] handler exception: " + e.getClass.getName + ": " + e.getMessage)
          try { io.write(server_error("internal server error")) }
          catch { case _: Throwable => }
      } finally {
        // Cancel the BLOCKING check this connection is attached to (if any) on
        // disconnect: the reader just exited because the client closed the
        // channel, so its caller is gone. Wait briefly for the job to unwind so
        // the session isn't left held. A DETACHED check is not in `attached`, so
        // it is deliberately untouched — it outlives the connection by design.
        attached.get.foreach { job =>
          if (job.isRunning) {
            clog("client disconnected — aborting attached check")
            job.cancel("disconnect")
          }
          if (!job.await(5000))
            server_progress.echo_error_message("[conn " + conn_id +
              "] check still running 5s after disconnect; session held until it returns")
        }
        io.close()
        state.active_connections.decrementAndGet()
        vlog("connection closed")
      }
    }

    private def server_error(msg: String): JSON.Object.T =
      JSON.Object("event" -> "server_error", "message" -> msg)

    /** Reject an invalid `check` request: tell the client what was wrong AND
     *  emit `finished` so its read loop terminates (it only stops on
     *  `finished` or EOF). */
    private def fail_check(io: JSON_IO, msg: String): Unit = {
      clog("check rejected — invalid request: " + msg)
      io.write(server_error(msg))
      io.write(JSON.Object("event" -> "finished",
        "ok" -> false, "reason" -> "invalid request"))
    }

    /** Render a job Event to this connection's wire JSON
     *  (started / progress[nodes] / error / finished). */
    private def wireEvent(io: JSON_IO)(e: Check.Event): Unit = e match {
      case Check.Event.Started(theories) =>
        io.write(JSON.Object("event" -> "started", "theories" -> theories))
      case Check.Event.Progress(nodes, runningCommands, updateSeqs) =>
        io.write(JSON.Object("event" -> "progress",
          "nodes" -> nodes.map { case (n, st) =>
            Check.nodeStatusJson(n, st, runningCommands.getOrElse(n, Nil), updateSeqs.getOrElse(n, 0L)) }))
      case Check.Event.Error(theory, file, line, message) =>
        io.write(JSON.Object("event" -> "error", "theory" -> theory) ++
          file.map(f => JSON.Object("file" -> f)).getOrElse(JSON.Object()) ++
          line.map(l => JSON.Object("line" -> l)).getOrElse(JSON.Object()) ++
          JSON.Object("message" -> message))
      case Check.Event.Finished(ok, reason) =>
        if (ok) io.write(JSON.Object("event" -> "finished", "ok" -> true))
        else io.write(JSON.Object("event" -> "finished", "ok" -> false, "reason" -> reason))
    }

    /** Submit either a full (`line=None`) or partial (`line=Some(N)`) check.
     *  Small dispatcher: full checks go through `Check.submit`, partial through
     *  `Check.submitPartial`. Same return type — the caller doesn't care which
     *  flavor the Job is, because both stream the same Event set. */
    private def submit_by_mode(
      session: Headless.Session, resources: Headless.Resources,
      files: List[String], line: Option[Int]
    ): Either[String, Check.Job] =
      line match {
        case Some(l) => Check.submitPartial(session, resources, files, l)
        case None => Check.submit(session, resources, files)
      }

    /* ---- check (foreground): submit the Job, stream its events to io, and
     *  wait, cancelling it if THIS connection drops. The standard check. */

    private def start_check_blocking(io: JSON_IO, session: Headless.Session,
      resources: Headless.Resources, files: List[String],
      line: Option[Int] = None): Unit =
      submit_by_mode(session, resources, files, line) match {
        case Left(msg) => fail_check(io, "check: " + msg)
        case Right(job) =>
          // Remember the job so a disconnect cancels exactly it. (Check.submit
          // already enforces at-most-one-in-flight server-wide.)
          attached.set(Some(job))
          Check.logStart(server_progress, "conn " + conn_id, job.theories)
          io.write(JSON.Object("event" -> "started", "theories" -> job.theories))
          // Stream the job's live progress/error events. Drop the streamed
          // Finished — we emit the terminal `finished` from the awaited outcome
          // (reliable even if a fast check finished before we subscribed).
          val unsubscribe = job.subscribe {
            case _: Check.Event.Finished => ()
            case e => wireEvent(io)(e)
          }
          // Wait on a RELAY thread, not the connection thread: the connection
          // thread must return to its read loop so a client disconnect is
          // detected (its `finally` then cancels this job).
          val relay = new Thread(new Runnable {
            def run(): Unit =
              try {
                val out = job.await()
                // Final progress snapshot (the awaited recorded status) so the
                // client UI ends on a settled per-theory state, then finished.
                wireEvent(io)(Check.Event.Progress(job.finalNodes))
                wireEvent(io)(Check.Event.Finished(out.ok, out.reason))
                Check.logFinish(server_progress, "conn " + conn_id, job.elapsedMs, out.ok, out.reason)
              } finally { unsubscribe(); attached.set(None) }
          }, "ic2-check-relay-" + conn_id)
          relay.setDaemon(true)
          relay.start()
      }

    /* ---- check (detached): submit the Job and ack; it outlives this
     *  connection. The client polls check_status / aborts via check_cancel. */

    private def start_check_detached(io: JSON_IO, session: Headless.Session,
      resources: Headless.Resources, files: List[String],
      line: Option[Int] = None): Unit =
      submit_by_mode(session, resources, files, line) match {
        case Left(msg) => fail_check(io, "check: " + msg)
        case Right(job) =>
          Check.logStart(server_progress, "conn " + conn_id + " detached", job.theories)
          // Log the boundary when the detached check ends (no caller is waiting).
          val _ = job.subscribe {
            case Check.Event.Finished(ok, reason) =>
              Check.logFinish(server_progress, "detached", job.elapsedMs, ok, reason)
            case _ =>
          }
          io.write(JSON.Object("event" -> "submitted") ++ job.statusJson)
      }

    private def check_status_reply(): JSON.Object.T =
      Check.current match {
        case Some(job) => JSON.Object("event" -> "check_status") ++ job.statusJson
        case None => JSON.Object("event" -> "check_status", "state" -> "idle")
      }

    /** Attach to the in-flight (typically detached) check: emit a snapshot now,
     *  then stream live events until it finishes. Read-only — disconnecting from
     *  an attach does NOT cancel the check (only the foreground caller cancels). */
    private def check_attach(io: JSON_IO): Unit =
      Check.current match {
        case None => io.write(server_error("no check in flight"))
        case Some(job) =>
          io.write(JSON.Object("event" -> "started", "theories" -> job.theories))
          // Subscribe BEFORE awaiting (and drop the streamed Finished): this is
          // race-free for a job that finishes right now — we emit the terminal
          // `finished` from the awaited record, never depending on whether the
          // live Finished arrived before or after we subscribed. await() returns
          // immediately if the job is already done.
          val unsubscribe = job.subscribe {
            case _: Check.Event.Finished => ()
            case e => wireEvent(io)(e)
          }
          // Paint the current per-theory state immediately (after subscribing, so
          // no live tick is missed): a check wedged inside one long-running command
          // emits no nodes_status ticks, so without this the client would sit on a
          // bare `started` line until that command finishes. finalNodes is the live
          // cached snapshot while running (the same source check_status reports); a
          // duplicate render vs the first live tick is harmless (each Progress is a
          // full per-node repaint). Empty for a job whose theory hasn't parsed yet.
          val snapshot = job.finalNodes
          if (snapshot.nonEmpty) wireEvent(io)(Check.Event.Progress(snapshot))
          try {
            val out = job.await()
            wireEvent(io)(Check.Event.Progress(job.finalNodes))
            wireEvent(io)(Check.Event.Finished(out.ok, out.reason))
          } finally unsubscribe()
      }

    private def check_cancel_reply(): JSON.Object.T = {
      val running = Check.current.exists(_.isRunning)
      if (running) Check.current.foreach(_.cancel("cancelled"))
      JSON.Object("event" -> "check_cancel", "cancelled" -> running)
    }

    /** Parse-only load: parse the given .thy files into the session's
     *  document graph WITHOUT evaluating any commands. Delegates to the
     *  shared `SessionTools.parseFiles`. On success returns the list of
     *  loaded node paths; on failure returns a server_error. */
    private def load_files_reply(
      session: Headless.Session, resources: Headless.Resources, files: List[String]
    ): JSON.Object.T =
      SessionTools.parseFiles(session, resources, files) match {
        case Right(names) =>
          JSON.Object("event" -> "load-files",
            "loaded" -> names.map(_.node),
            "count" -> names.length)
        case Left(msg) => server_error("load-files: " + msg)
      }

    /** One-shot read-only diagnostic query — the wire counterpart of the MCP
     *  diagnostic tools. Routes `{op:query, tool, ...}` through the SAME
     *  SessionTools.dispatch the MCP SessionClient uses (so the two surfaces
     *  can't drift), wrapping the tool's JSON result. The request's own fields
     *  (minus `op`) are the tool params. */
    private def query_reply(session: Headless.Session, t: JSON.T): JSON.Object.T =
      JSON.string(t, "tool") match {
        case None => server_error("query: missing 'tool'")
        case Some(tool) =>
          val params = (t match { case JSON.Object(m) => m; case _ => Map.empty[String, Any] }) - "op"
          SessionTools.dispatch(session, tool, params) match {
            case Right(result) => JSON.Object("event" -> "query", "tool" -> tool, "result" -> result)
            case Left(msg) => server_error("query: " + msg)
          }
      }

    /** Create an I/R REPL from a source location: `{op:repl, file, line, name}`.
     *  The daemon has both halves the bare `repl.py cli` lacks — the resident
     *  session (to map file+line -> command id) and the connected I/R client —
     *  so it resolves server-side and creates the REPL via IQ.replFromSource.
     *  The reply carries the REPL's initial state AND the concrete `repl.py cli`
     *  command schema to drive THIS repl, so an agent can act with no further
     *  lookup (`drive` field; also folded into `result` for plain-text clients). */
    private def repl_reply(session: Headless.Session, t: JSON.T): JSON.Object.T =
      (JSON.string(t, "file"), JSON.int(t, "line"), JSON.string(t, "name")) match {
        case (Some(file), Some(line), Some(name)) =>
          state.ir_client match {
            case None => server_error("repl: I/R is not available on this server (started with --no-iq, or bring-up failed)")
            case Some(client) =>
              IQ.replFromSource(session, client, file, line, name) match {
                case Right(reply) =>
                  val drive = state.ir.flatMap(_.repl_py).map { replPy =>
                    val dir = Path.explode(replPy).expand.dir.implode
                    IQ.repl_drive_schema(dir, state.ir.get.repl_port, state.ir.flatMap(_.repl_token), name)
                  }
                  JSON.Object("event" -> "repl", "name" -> name, "result" -> reply) ++
                    drive.map(d => JSON.Object("drive" -> d)).getOrElse(JSON.Object())
                case Left(msg) => server_error("repl: " + msg)
              }
          }
        case _ => server_error("repl: requires 'file', 'line', and 'name'")
      }
  }
}
