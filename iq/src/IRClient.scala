/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.io.{BufferedReader, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.net.Socket

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

  /** Set step timeout (0=unlimited). */
  def timeout(secs: Int): String = send(s"Ir.timeout ${mlInt(secs)}")

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
      |  timeout(10)                        Set step timeout (0 = unlimited)
      |
      |Config:
      |  config("(fn c => ...)")            Update ML config record
      |  mlHelp()                           Show ML-side Ir.help text
      |""".stripMargin
}
