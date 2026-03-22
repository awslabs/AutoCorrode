/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.io.{BufferedReader, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.net.Socket

/** Persistent TCP client for the I/R REPL server (repl.py).
  *
  * Maintains a single TCP connection and provides both a raw send method
  * and typed Scala methods for each Ir.* command. Commands are serialized
  * (not thread-safe; callers must synchronize if sharing across threads).
  *
  * Protocol: send "command;\n", read lines until "<<DONE>>\n".
  */
class IRClient(host: String = "127.0.0.1", port: Int = 9147, token: String = "") {

  private val Sentinel = "<<DONE>>"

  private var socket: Socket = _
  private var out: PrintWriter = _
  private var in: BufferedReader = _

  def connect(): Unit = {
    socket = new Socket(host, port)
    out = new PrintWriter(new OutputStreamWriter(socket.getOutputStream, "UTF-8"), true)
    in = new BufferedReader(new InputStreamReader(socket.getInputStream, "UTF-8"))
    if (token.nonEmpty) {
      out.println(token)
      out.flush()
      val response = in.readLine()
      if (response == null || !response.startsWith("OK"))
        throw new java.io.IOException("REPL authentication failed")
    }
  }

  def isConnected: Boolean = socket != null && !socket.isClosed

  def close(): Unit = {
    if (socket != null) {
      try { socket.close() } catch { case _: Exception => }
      socket = null
    }
  }

  /** Send a raw ML expression and return the output. The trailing semicolon
    * is added automatically if missing. */
  def send(command: String): String = {
    if (!isConnected) throw new IllegalStateException("Not connected — call connect() first")
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
    if (line == null) {
      close()
      throw new java.io.IOException("Connection closed by server")
    }
    sb.toString
  }

  // -- Helpers for ML argument quoting --

  private def q(s: String): String = "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"") + "\""
  private def ql(ss: List[String]): String = "[" + ss.map(q).mkString(", ") + "]"
  private def mlInt(n: Int): String = if (n < 0) "~" + (-n).toString else n.toString

  // -- Typed API --

  /** Create a new REPL importing the given theories. */
  def init(id: String, theories: List[String] = Nil): String =
    send(s"Ir.init ${q(id)} ${ql(theories)}")

  /** Create a REPL from a PIDE document state (node + command id via I/Q). */
  def initFromDocument(id: String, node: String, commandId: Int): String =
    send(s"Ir.init_from_document ${q(id)} ${q(node)} ${mlInt(commandId)}")

  /** Create a REPL from a source location, resolving to node + command id via IQUtils.
    *
    * Supports the same selection modes as I/Q:
    *   - File + offset: {{{ initFromSourceLocation("r", file="/path/to/Foo.thy", offset=42) }}}
    *   - File + pattern: {{{ initFromSourceLocation("r", file="Foo.thy", pattern="lemma foo") }}}
    *
    * File paths are auto-completed against open documents in Isabelle/jEdit.
    */
  def initFromSourceLocation(
    id: String,
    file: String,
    offset: Option[Int] = None,
    pattern: Option[String] = None
  ): String = {
    val resolvedPath = IQUtils.autoCompleteFilePath(file) match {
      case Right(p) => p
      case Left(err) => return s"Error: $err"
    }
    val (target, oOpt, pOpt) =
      if (offset.isDefined) (CommandSelectionTarget.FileOffset, offset, None)
      else if (pattern.isDefined) (CommandSelectionTarget.FilePattern, None, pattern)
      else return "Error: specify either offset or pattern"
    IQUtils.resolveCommandSelection(target, Some(resolvedPath), oOpt, pOpt) match {
      case Right(resolved) =>
        val node = resolved.command.node_name.node
        val cmdId = resolved.command.id.toInt
        initFromDocument(id, node, cmdId)
      case Left(err) => s"Error: $err"
    }
  }

  /** Fork a new REPL from the current one at the given state index. */
  def fork(id: String, stateIdx: Int): String =
    send(s"Ir.fork ${q(id)} ${mlInt(stateIdx)}")

  /** Switch to the REPL with the given id. */
  def focus(id: String): String =
    send(s"Ir.focus ${q(id)}")

  /** Execute Isar text as the next step in the current REPL. */
  def step(isarText: String): String =
    send(s"Ir.step ${q(isarText)}")

  /** Execute Isar text from a file as the next step. */
  def stepFile(path: String): String =
    send(s"Ir.step_file ${q(path)}")

  /** Show current REPL: origin, steps, staleness. */
  def show(): String = send("Ir.show ()")

  /** Show proof state at step idx (0=base, ~1=latest). */
  def state(idx: Int): String = send(s"Ir.state ${mlInt(idx)}")

  /** Print concatenated Isar text of current REPL. */
  def text(): String = send("Ir.text ()")

  /** Replace step idx, mark later steps stale. */
  def edit(idx: Int, isarText: String): String =
    send(s"Ir.edit ${mlInt(idx)} ${q(isarText)}")

  /** Re-execute all stale steps. */
  def replay(): String = send("Ir.replay ()")

  /** Keep steps 0..idx, discard the rest. */
  def truncate(idx: Int): String = send(s"Ir.truncate ${mlInt(idx)}")

  /** Inline current sub-REPL back into its parent. */
  def merge(): String = send("Ir.merge ()")

  /** Delete REPL and all its sub-REPLs. */
  def remove(id: String): String = send(s"Ir.remove ${q(id)}")

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
  def sledgehammer(secs: Int): String = send(s"Ir.sledgehammer ${mlInt(secs)}")

  /** Set step timeout (0=unlimited). */
  def timeout(secs: Int): String = send(s"Ir.timeout ${mlInt(secs)}")

  /** Split multi-command step idx into individual steps. */
  def explode(idx: Int): String = send(s"Ir.explode ${mlInt(idx)}")

  /** Search theorems (n=max results, 0=unlimited). */
  def findTheorems(n: Int, query: String): String =
    send(s"Ir.find_theorems ${mlInt(n)} ${q(query)}")

  /** Revert last step. */
  def back(): String = send("Ir.back ()")

  /** Update config. The argument is an ML record update function, e.g.
    * {{{ irClient.config("(fn c => {c with color = false})") }}} */
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
      |  init("id", List("thy1"))           Create REPL importing theories
      |  initFromDocument("id", node, cid)  Create REPL from PIDE document state
      |  initFromSourceLocation("id",       Create REPL from source location:
      |    file="Foo.thy", offset=42)         by file + character offset, or
      |    file="Foo.thy",                    by file + unique text pattern
      |    pattern="lemma foo")
      |  fork("id", stateIdx)               Fork from current REPL at state index
      |  focus("id")                        Switch to REPL
      |  remove("id")                       Delete REPL and sub-REPLs
      |  repls()                            List all REPLs
      |
      |Stepping (failed steps leave REPL unchanged — don't call back() after a failure):
      |  step("lemma \"True\" by simp")     Execute Isar text as next step
      |  stepFile("/path/to/file")          Execute Isar from file
      |  back()                             Revert last successful step
      |  edit(idx, "new text")              Replace step at index
      |  replay()                           Re-execute stale steps
      |  truncate(idx)                      Keep steps 0..idx
      |  explode(idx)                       Split multi-command step
      |  merge()                            Inline sub-REPL into parent
      |
      |Inspection:
      |  show()                             Current REPL info
      |  state(idx)                         Proof state at step (~1 = latest)
      |  text()                             Concatenated Isar text
      |
      |Theories:
      |  theories()                         List loaded theories
      |  loadTheory("HOL-Library.Multiset") Load theory by name
      |  source("thy", start, stop)         List theory commands
      |
      |Proof tools:
      |  sledgehammer(30)                   Run sledgehammer (timeout in secs)
      |  findTheorems(10, "name: *map*")    Search theorems
      |  timeout(10)                        Set step timeout (0 = unlimited)
      |
      |Config:
      |  config("(fn c => ...)")            Update ML config record
      |  mlHelp()                           Show ML-side Ir.help text
      |""".stripMargin
}
