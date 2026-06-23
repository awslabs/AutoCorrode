/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle.{Session, Prover, Value, Output, Isabelle_System,
  Document, Document_Status, Text, Scan, Sessions, Date}

import java.io.{BufferedReader, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.net.Socket
import scala.util.Using

/** Ephemeral TCP client for the I/R REPL server (repl.py).
  *
  * Opens a fresh TCP connection per send() call — desync is structurally
  * impossible since there is no persistent pipe for stale responses.
  * Provides both a raw send method and typed Scala methods for each
  * Ir.* command.
  *
  * Protocol: send "command;\n", read lines until "<<DONE>>\n".
  */
class IRClient(host: String = "127.0.0.1", port: Int = 9147, token: String = "") {

  private val Sentinel = "<<DONE>>"

  /** Verify reachability (called by IQExploreDockable on startup). */
  def connect(): Unit = {
    val sock = new Socket(host, port)
    sock.close()
  }

  /** Check server reachability. */
  def isConnected: Boolean = {
    try {
      val sock = new Socket(host, port)
      sock.close()
      true
    } catch { case _: Exception => false }
  }

  /** No-op: connections are per-call. */
  def close(): Unit = {}

  /** Send a raw ML expression and return the output. Opens a fresh TCP
    * connection, authenticates, sends the command, reads until the sentinel,
    * and closes. The trailing semicolon is added automatically if missing. */
  def send(command: String): String = {
    val sock = new Socket(host, port)
    try {
      val out = new PrintWriter(new OutputStreamWriter(sock.getOutputStream, "UTF-8"), true)
      val in = new BufferedReader(new InputStreamReader(sock.getInputStream, "UTF-8"))
      if (token.nonEmpty) {
        out.println(token)
        out.flush()
        val response = in.readLine()
        if (response == null || !response.startsWith("OK"))
          throw new java.io.IOException("REPL authentication failed")
      }
      val cmd = if (command.trim.endsWith(";")) command.trim else command.trim + ";"
      out.println(cmd)
      out.flush()
      val sb = new StringBuilder
      var line = in.readLine()
      while (line != null && line != Sentinel) {
        if (sb.nonEmpty) sb.append('\n')
        sb.append(line)
        line = in.readLine()
      }
      if (line == null)
        throw new java.io.IOException("Connection closed by server")
      val result = sb.toString
      if (result.startsWith("ERR\n"))
        throw new java.io.IOException(result.drop(4))
      result
    } finally {
      sock.close()
    }
  }

  // -- Helpers for ML argument quoting --

  private def q(s: String): String = "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"") + "\""
  private def ql(ss: List[String]): String = "[" + ss.map(q).mkString(", ") + "]"
  private def mlInt(n: Int): String = if (n < 0) "~" + (-n).toString else n.toString

  // -- Typed API: all REPL operations take an explicit repl id --

  /** Create a new REPL importing the given theories. */
  def init(repl: String, theories: List[String] = Nil): String =
    send(s"Ir.init ${q(repl)} ${ql(theories)}")

  /** Create a REPL from a PIDE document state (node + command id via I/Q). */
  def initFromDocument(repl: String, node: String, commandId: Int): String =
    send(s"Ir.init_from_document ${q(repl)} ${q(node)} ${mlInt(commandId)}")

  /** Create a REPL from a source location, resolving to node + command id via IQUtils. */
  def initFromSourceLocation(
    repl: String,
    file: String,
    offset: Option[Int] = None,
    pattern: Option[String] = None
  ): String = {
    val resolvedPath = IQUtils.autoCompleteFilePath(file) match {
      case Right(p) => p
      case Left(err) => throw new IllegalArgumentException(err)
    }
    val (target, oOpt, pOpt) =
      if (offset.isDefined) (CommandSelectionTarget.FileOffset, offset, None)
      else if (pattern.isDefined) (CommandSelectionTarget.FilePattern, None, pattern)
      else throw new IllegalArgumentException("specify either offset or pattern")
    IQUtils.resolveCommandSelection(target, Some(resolvedPath), oOpt, pOpt) match {
      case Right(resolved) =>
        val node = resolved.command.node_name.node
        val cmdId = resolved.command.id.toInt
        initFromDocument(repl, node, cmdId)
      case Left(err) => throw new IllegalArgumentException(err)
    }
  }

  /** Fork a new REPL from repl at the given state index. */
  def fork(repl: String, newRepl: String, stateIdx: Int): String =
    send(s"Ir.fork ${q(repl)} ${q(newRepl)} ${mlInt(stateIdx)}")

  /** Execute Isar text as the next step. */
  def step(repl: String, isarText: String): String =
    send(s"Ir.step ${q(repl)} ${q(isarText)}")

  /** Show REPL: origin, steps, staleness. */
  def show(repl: String): String = send(s"Ir.show ${q(repl)}")

  /** Show proof state at step idx (0=base, ~1=latest). */
  def state(repl: String, idx: Int): String =
    send(s"Ir.state ${q(repl)} ${mlInt(idx)}")

  /** Print concatenated Isar text. */
  def text(repl: String): String = send(s"Ir.text ${q(repl)}")

  /** Replace step idx, mark later steps stale. */
  def edit(repl: String, idx: Int, isarText: String): String =
    send(s"Ir.edit ${q(repl)} ${mlInt(idx)} ${q(isarText)}")

  /** Re-execute all stale steps. */
  def replay(repl: String): String = send(s"Ir.replay ${q(repl)}")

  /** Keep steps 0..idx, discard the rest. */
  def truncate(repl: String, idx: Int): String =
    send(s"Ir.truncate ${q(repl)} ${mlInt(idx)}")

  /** Revert last step. */
  def back(repl: String): String = send(s"Ir.back ${q(repl)}")

  /** Inline sub-REPL back into its parent. */
  def merge(repl: String): String = send(s"Ir.merge ${q(repl)}")

  /** Delete REPL and all its sub-REPLs. */
  def remove(repl: String): String = send(s"Ir.remove ${q(repl)}")

  /** List all REPLs with step counts and origins. */
  def repls(): String = send("Ir.repls ()")

  /** List all theories loaded in the session. */
  def theories(): String = send("Ir.theories ()")

  /** Load a theory by name. */
  def loadTheory(name: String): String = send(s"Ir.load_theory ${q(name)}")

  /** List theory commands (start/stop are 0-based, ~N from end). */
  def source(thy: String, start: Int, stop: Int): String =
    send(s"Ir.source ${q(thy)} ${mlInt(start)} ${mlInt(stop)}")

  /** Run sledgehammer with the given timeout in seconds. */
  def sledgehammer(repl: String, secs: Int): String =
    send(s"Ir.sledgehammer ${q(repl)} ${mlInt(secs)}")

  /** Set step timeout for a specific REPL (0=unlimited). */
  def timeout(repl: String, secs: Int): String = send(s"Ir.timeout ${q(repl)} ${mlInt(secs)}")

  /** Search theorems (n=max results, 0=unlimited). */
  def findTheorems(repl: String, n: Int, query: String): String =
    send(s"Ir.find_theorems ${q(repl)} ${mlInt(n)} ${q(query)}")

  /** Update config. */
  def config(f: String): String = send(s"Ir.config $f")

  /** Show full ML-side help text. */
  def mlHelp(): String = send("Ir.help ()")

  /** Show IRClient API help. */
  def help(): String =
    """IRClient API — Scala interface to the I/R REPL (repl.py on port 9147)
      |
      |Connection:
      |  connect()                          Open TCP connection
      |  close()                            Close connection
      |  isConnected                        Check connection status
      |
      |Raw:
      |  send("Ir.help ();")                Send any ML expression (auto-appends ;)
      |
      |REPL lifecycle:
      |  init("r", List("Main"))            Create REPL importing theories
      |  initFromDocument("r", node, cid)   Create REPL from PIDE document state
      |  initFromSourceLocation("r",        Create REPL from source location:
      |    file="Foo.thy", offset=42)         by file + character offset, or
      |    file="Foo.thy",                    by file + unique text pattern
      |    pattern="lemma foo")
      |  fork("r", "s", stateIdx)           Fork new REPL from r at state index
      |  remove("r")                        Delete REPL and sub-REPLs
      |  repls()                            List all REPLs
      |
      |Stepping (failed steps leave REPL unchanged — don't call back() after a failure):
      |  step("r", "lemma \"True\"")        Execute Isar text as next step
      |  back("r")                          Revert last successful step
      |  edit("r", idx, "new text")         Replace step at index
      |  replay("r")                        Re-execute stale steps
      |  truncate("r", idx)                 Keep steps 0..idx
      |  merge("r")                         Inline sub-REPL into parent
      |
      |Inspection:
      |  show("r")                          REPL info
      |  state("r", idx)                    Proof state at step (~1 = latest)
      |  text("r")                          Concatenated Isar text
      |
      |Theories:
      |  theories()                         List loaded theories
      |  loadTheory("HOL-Library.Multiset") Load theory by name
      |  source("thy", start, stop)         List theory commands
      |
      |Proof tools:
      |  sledgehammer("r", 30)              Run sledgehammer (timeout in secs)
      |  findTheorems("r", 10, "name: *")   Search theorems
      |  timeout("r", 10)                   Set step timeout for REPL (0 = unlimited)
      |
      |Config:
      |  config("(fn c => ...)")            Update ML config record
      |  mlHelp()                           Show ML-side Ir.help text
      |""".stripMargin
}


/** Brings up the full I/R stack against an Isabelle session and returns a
  * connected IRClient. Works for ANY `isabelle.Session` — the live PIDE session
  * (jEdit) or a headless `Headless.Session` — since the handshake uses only the
  * generic Session protocol API.
  *
  * Steps:
  *   1. register an IR_Repl.port protocol handler on the session;
  *   2. send the `IR_Repl.start` protocol command and wait for the ML_Repl to
  *      report its port/token/max_connections (the rendezvous below);
  *   3. spawn `python3 repl.py --daemon --expect-ml --poly-ml-port <p> ...`,
  *      passing the ML_Repl token via IR_REPL_AUTH_TOKEN;
  *   4. scrape repl.py's own port/token from its stdout and connect an IRClient.
  *
  * The IR_Repl.port rendezvous lives on the session-registered Port_Handler (below). */
object IRLauncher {
  /** repl.py endpoint + the spawned process, returned to the caller for
    * lifecycle management (kill on shutdown) and status display. */
  final case class Launched(client: IRClient, replPort: Int, replToken: Option[String],
                            process: Process, irDir: String)

  /** Protocol handler for `IR_Repl.port`, storing the rendezvous on itself.
    * Session-generic (no jEdit). Because Isabelle keys handlers by class name,
    * exactly one instance is registered per session and every IR_Repl.port
    * message dispatches to it; launch() resolves that instance via
    * get_protocol_handler rather than trusting the copy it constructed. */
  final class Port_Handler extends Session.Protocol_Handler {
    @volatile var port: Option[Int] = None
    @volatile var token: Option[String] = None
    @volatile var maxConn: Option[Int] = None

    /** Clear stale rendezvous before re-issuing IR_Repl.start. Safe because the
      * ML side re-reports its port even when the server is already running. */
    def reset(): Unit = { port = None; token = None; maxConn = None }

    private def handle_port(msg: Prover.Protocol_Output): Boolean =
      msg.properties match {
        case List(_, ("port", Value.Int(p)), ("token", tok),
                  ("max_connections", Value.Int(mc))) =>
          port = Some(p); token = Some(tok); maxConn = Some(mc); true
        case List(_, ("port", Value.Int(p)), ("token", tok)) =>
          port = Some(p); token = Some(tok); true
        case List(_, ("port", Value.Int(p))) =>
          port = Some(p); true
        case _ => false
      }
    override val functions: Session.Protocol_Functions =
      List("IR_Repl.port" -> handle_port)
  }

  /** Protocol handler for `IR_Repl.status`, the side-effect-free readiness probe.
    * `replied` flips true once any status message arrives (proving ir.ML is
    * loaded — an undefined protocol command is silently dropped, so no reply
    * means not loaded). `running`/`port`/`token`/`maxConn` mirror the ML_Repl's
    * current TCP-listener state. */
  final class Status_Handler extends Session.Protocol_Handler {
    @volatile var replied: Boolean = false
    @volatile var running: Boolean = false
    @volatile var port: Option[Int] = None
    @volatile var token: Option[String] = None
    @volatile var maxConn: Option[Int] = None

    def reset(): Unit = {
      replied = false; running = false; port = None; token = None; maxConn = None
    }

    private def handle_status(msg: Prover.Protocol_Output): Boolean = {
      // properties: function marker, then ("running", bool), then optionally
      // ("port", int), ("token", str), ("max_connections", int).
      val props = msg.properties
      props.collectFirst { case ("running", v) => v } match {
        case Some(r) =>
          running = (r == "true")
          props.collectFirst { case ("port", Value.Int(p)) => p }.foreach(p => port = Some(p))
          props.collectFirst { case ("token", t) => t }.foreach(t => token = Some(t))
          props.collectFirst { case ("max_connections", Value.Int(mc)) => mc }
            .foreach(mc => maxConn = Some(mc))
          replied = true
          true
        case None => false
      }
    }
    override val functions: Session.Protocol_Functions =
      List("IR_Repl.status" -> handle_status)
  }
}

final class IRLauncher(
  session: Session,
  onStatus: String => Unit = msg => Output.writeln("I/R: " + msg)
) {
  import IRLauncher.{Launched, Port_Handler, Status_Handler}

  /** Resolve (registering once) a protocol handler instance on the session.
    * Isabelle keys handlers by class, so exactly one instance handles every
    * matching message; we trust the registered instance, not a local copy. */
  private def handlerOf[H <: Session.Protocol_Handler](cls: Class[H], make: => H): Option[H] = {
    if (session.get_protocol_handler(cls).isEmpty) session.init_protocol_handler(make)
    session.get_protocol_handler(cls)
  }

  /** Ensure the I/R ML (ir.ML / tcp_handler.ML / ml_repl.ML, which define the
    * IR_Repl.* protocol commands) is loaded into the prover, by introducing an
    * in-memory `ir` theory node whose body inlines those ML files. Portable: it
    * uses only the generic Session/Resources API, so it works for the live PIDE
    * session (jEdit) and a headless session alike. The node is named from the
    * real `irDir`, so if `ir.thy` is ALSO loaded normally the theory graph
    * dedupes (no double ML evaluation).
    *
    * Returns the node name on success. `session.update` only ENQUEUES the edit
    * and the node is processed asynchronously, so the caller must
    * awaitConsolidated before the IR_Repl.* commands exist. */
  private def ensureLoaded(irDir: String): Either[String, Document.Node.Name] = {
    def read(name: String): Either[String, String] = {
      val f = new java.io.File(irDir, name)
      if (!f.isFile) Left(s"I/R ML source not found: ${f.getPath}")
      else Right(Using.resource(scala.io.Source.fromFile(f, "UTF-8"))(_.mkString))
    }
    for {
      irML <- read("ir.ML")
      tcpML <- read("tcp_handler.ML")
      mlReplML <- read("ml_repl.ML")
    } yield {
      // Inline the three ML files as ML<...> blocks (cartouche-delimited), in
      // dependency order, bracketed by ML_write_global so the structures and
      // protocol commands become Poly/ML globals (as ir.thy does).
      def ml(src: String): String = "ML‹" + src + "›"
      val text =
        "theory ir\n  imports Main\nbegin\n" +
        "declare [[ML_write_global = true]]\n" +
        ml(irML) + "\n" + ml(tcpML) + "\n" + ml(mlReplML) + "\n" +
        "declare [[ML_write_global = false]]\n" +
        "end\n"

      val resources = session.resources
      val node = resources.import_name(Sessions.DRAFT, irDir, "ir")
      val header = resources.check_thy(node, Scan.char_reader(text))
      // Perspective.required = true so the prover processes the node even though
      // nothing is "visible"; awaitConsolidated then blocks until it settles.
      val edits: List[Document.Edit_Text] = List(
        node -> Document.Node.Deps(header),
        node -> Document.Node.Edits(Text.Edit.inserts(0, text)),
        node -> Document.Node.Perspective(true, Text.Perspective.empty, Document.Node.Overlays.empty)
      )
      onStatus("Loading I/R ML into the prover (node " + node.theory + ") ...")
      session.update(Document.Blobs.empty, edits)
      node
    }
  }

  /** Block until the I/R ML node has CONSOLIDATED (settled), or `timeoutMs`
    * elapses. Event-driven: subscribe to commands_changed and recompute the node
    * status on each event. Session-generic (commands_changed + snapshot +
    * Node_Status), no jEdit.
    *
    * We key on `consolidated`, NOT on terminated/failed: `terminated` only means
    * "every command in THIS version reached a terminal state", and a failed
    * command is still terminated. While a busy prover reprocesses the node
    * (e.g. an import not yet resolvable in an intermediate version), it can show
    * terminated+failed transiently and then reprocess clean. `consolidated` is
    * the monotonic CONSOLIDATED rung of the theory-status ladder — once reached
    * it does not revert — so `failed` read AFTER it is a stable verdict.
    *
    * Left on timeout or if the settled node has failed commands; Right once it
    * consolidates clean. */
  private def awaitConsolidated(node: Document.Node.Name, timeoutMs: Long): Either[String, Unit] = {
    def status(): Document_Status.Node_Status = {
      val snap = session.snapshot(node_name = node)
      Document_Status.Node_Status.make(Date.now(), snap.state, snap.version, node)
    }
    val latch = new java.util.concurrent.CountDownLatch(1)
    val consumer = Session.Consumer[Session.Commands_Changed]("IRLauncher.awaitConsolidated") {
      case Session.Commands_Changed(_, nodes, _) if nodes.contains(node) =>
        if (status().consolidated) latch.countDown()
      case _ =>
    }
    session.commands_changed += consumer
    try {
      // Re-check after subscribing: the node may have consolidated between the
      // subscription and now (TOCTOU).
      if (status().consolidated) latch.countDown()
      val settled = latch.await(timeoutMs, java.util.concurrent.TimeUnit.MILLISECONDS) || status().consolidated
      if (!settled)
        Left(s"I/R ML did not load within ${timeoutMs / 1000}s — the prover may be busy")
      else if (status().failed > 0)
        Left("I/R ML failed to load — error while evaluating the inlined ML")
      else Right(())
    } finally {
      session.commands_changed -= consumer
    }
  }

  /** Run the full bring-up. `irDir` is the directory containing repl.py and the
    * I/R ML sources (already resolved by the caller). Blocking; returns
    * Left(reason) on failure.
    *
    * Probes IR_Repl.status first (side-effect-free): no reply within the window
    * => the ML isn't loaded, so load it and wait until the node consolidates,
    * then start; reply but not running => start; reply and running => reuse the
    * reported ML_Repl port/token. Then in all cases (re)spawn repl.py against
    * the ML_Repl. */
  def launch(irDir: String): Either[String, Launched] = {
    val replPy = new java.io.File(irDir, "repl.py").getPath

    val portH = handlerOf(classOf[Port_Handler], new Port_Handler) match {
      case Some(h) => h
      case None => return Left("Failed to register the IR_Repl.port protocol handler")
    }
    val statusH = handlerOf(classOf[Status_Handler], new Status_Handler) match {
      case Some(h) => h
      case None => return Left("Failed to register the IR_Repl.status protocol handler")
    }

    // ---- Tier probe: is the ML loaded, and is the ML_Repl already running? ----
    statusH.reset()
    session.protocol_command("IR_Repl.status")
    onStatus("Probing IR_Repl.status ...")
    var probe = 0
    while (!statusH.replied && probe < 10) { Thread.sleep(500); probe += 1 } // ~5s

    // Decide what bring-up the ML_Repl needs, and (when already running) the
    // port/token to reuse without a fresh IR_Repl.start.
    val reuse: Option[(Int, Option[String], Option[Int])] =
      if (statusH.replied && statusH.running)
        statusH.port.map(p => (p, statusH.token, statusH.maxConn))
      else None

    if (!statusH.replied) {
      // (a) no reply: ML not loaded -> load it and wait until the node has
      // CONSOLIDATED, so the IR_Repl.* commands are defined before we use them.
      // Without this wait a busy prover may not reach the node in time.
      onStatus("IR_Repl.status: no reply — loading I/R ML ad-hoc")
      ensureLoaded(irDir) match {
        case Right(node) =>
          onStatus("Waiting for the I/R ML node to consolidate ...")
          awaitConsolidated(node, 120000) match {
            case Right(()) => onStatus("I/R ML node consolidated")
            case Left(msg) => return Left(msg)
          }
        case Left(msg) => return Left(msg)
      }
    } else if (statusH.running) {
      // (c) loaded and running: nothing to start on the prover side.
      onStatus("IR_Repl: ML_Repl already running on port " + statusH.port.getOrElse(0))
    } else {
      // (b) loaded but not running: fall through to IR_Repl.start.
      onStatus("IR_Repl: ML loaded but ML_Repl not running")
    }

    // ---- Obtain the ML_Repl port/token: reuse, or send IR_Repl.start ----
    // We only reach the start path once the ir node is loaded AND processed
    // (path (a) waited above; paths (b)/(c) got a status reply, which proves it
    // was already loaded), so IR_Repl.start is defined — send it once. The reply
    // (IR_Repl.port) is still asynchronous, so poll for it. is_running makes the
    // command idempotent regardless.
    val (mlPort, mlToken, mlMaxConn): (Int, Option[String], Option[Int]) =
      reuse match {
        case Some((p, t, mc)) => (p, t, mc)
        case None =>
          portH.reset()
          session.protocol_command("IR_Repl.start")
          onStatus("Sent IR_Repl.start")
          val deadline = System.currentTimeMillis() + 15000
          while (portH.port.isEmpty && System.currentTimeMillis() < deadline)
            Thread.sleep(100)
          portH.port match {
            case Some(p) => onStatus("ML_Repl reported port " + p); (p, portH.token, portH.maxConn)
            case None => return Left("ML_Repl did not report a port within 15s — cannot start repl.py")
          }
      }

    // 3) launch repl.py --daemon against the ML_Repl.
    val isabellePath = Isabelle_System.getenv("ISABELLE_HOME")
    val pb = new ProcessBuilder("python3", replPy, "--daemon", "--expect-ml",
      "--poly-ml-port", mlPort.toString,
      "--isabelle", isabellePath,
      "--no-heap-db")
    mlMaxConn.foreach { mc =>
      val _ = pb.command().addAll(java.util.List.of("--pool-size", mc.toString))
    }
    mlToken.foreach { tok => val _ = pb.environment().put("IR_REPL_AUTH_TOKEN", tok) }
    pb.redirectErrorStream(true)
    onStatus("Executing: " + pb.command().toArray.mkString(" "))
    val proc = pb.start()

    // 4) scrape repl.py's own port + token from stdout, then connect IRClient.
    def stripAnsi(s: String): String = s.replaceAll("\u001b\\[[0-9;]*m", "")
    val reader = new java.io.BufferedReader(new java.io.InputStreamReader(proc.getInputStream))
    val portPattern = """Waiting for connections on \S+:(\d+)""".r
    val tokenPattern = """IR_Repl\.token: (\S+)""".r
    var replPort: Option[Int] = None
    var replToken: String = ""
    var line: String = null
    var eof = false
    var extraLines = 0
    while ((replPort.isEmpty || (replToken.isEmpty && extraLines < 5)) && !eof) {
      line = reader.readLine()
      if (line == null) { eof = true; onStatus("repl.py: EOF on stdout") }
      else {
        val clean = stripAnsi(line)
        onStatus("repl.py: " + clean)
        portPattern.findFirstMatchIn(clean).foreach(m => replPort = Some(m.group(1).toInt))
        tokenPattern.findFirstMatchIn(clean).foreach(m => replToken = m.group(1))
        if (replPort.isDefined && replToken.isEmpty) extraLines += 1
      }
    }
    replPort match {
      case Some(port) =>
        onStatus("repl.py listening on port " + port)
        try {
          val client = new IRClient(port = port, token = replToken)
          client.connect()
          onStatus("IRClient connected on port " + port)
          Right(Launched(client, port,
            if (replToken.nonEmpty) Some(replToken) else None, proc, irDir))
        } catch {
          case e: Exception => Left("IRClient failed to connect: " + e.getMessage)
        }
      case None => Left("repl.py did not report port")
    }
  }
}
