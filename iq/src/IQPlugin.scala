/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

import org.gjt.sp.jedit.{EBMessage, EBPlugin, jEdit}

object IQPlugin {
  /** System property key used to communicate the actual bound port to other
    * plugins (e.g. Isabelle Assistant) running in the same JVM. Non-persistent:
    * cleared on JVM exit and on plugin stop. */
  val PORT_PROPERTY = "iq.mcp.port"
  val AUTH_TOKEN_PROPERTY = "iq.mcp.auth.token"

  private val DEFAULT_PORT = 8765
  private val MAX_PORT_SCAN = 100

  @volatile private var instance: Option[IQPlugin] = None

  /** Port reported by ML_Repl via PIDE protocol message. */
  @volatile var mlReplPort: Option[Int] = None

  /** Token reported by ML_Repl via PIDE protocol message. */
  @volatile var mlReplToken: Option[String] = None

  /** Port of the I/R REPL (repl.py), set by IQExploreDockable on connect. */
  @volatile var irReplPort: Option[Int] = None

  /** Auth token of the I/R REPL (repl.py), set by IQExploreDockable on connect. */
  @volatile var irReplToken: Option[String] = None

  /** Actual bound port of the I/Q MCP server, set after successful start. */
  @volatile var mcpPort: Option[Int] = None

  private def register(plugin: IQPlugin): Unit = {
    instance = Some(plugin)
  }

  private def unregister(plugin: IQPlugin): Unit = {
    if (instance.contains(plugin)) instance = None
  }

  def restartServerFromSettings(): Unit = {
    instance.foreach(_.restartServerFromSettings())
  }

  /** Number of TCP clients currently connected to the I/Q MCP server. */
  def activeClientCount: Int =
    instance.flatMap(_.currentServer).map(_.getActiveClientCount).getOrElse(0)

  /** Number of clients that have completed the auth handshake. */
  def authenticatedClientCount: Int =
    instance.flatMap(_.currentServer).map(_.getAuthenticatedClientCount).getOrElse(0)

  /** Append a status widget name to the status bar if not already present. */
  def activateWidget(name: String): Unit = {
    GUI_Thread.later {
      val key = "view.status"
      var current = jEdit.getProperty(key, "")
      if (!current.contains(name)) {
        current = current + " " + name
        jEdit.setProperty(key, current)
        var view = jEdit.getFirstView()
        while (view != null) {
          view.getStatus.propertiesChanged()
          view = view.getNext
        }
      }
    }
  }

  /** PIDE protocol handler: receives IR_Repl.port messages from ML. */
  class IR_Repl_Handler extends Session.Protocol_Handler {
    private def handle_port(msg: Prover.Protocol_Output): Boolean = {
      msg.properties match {
        case List(_, ("port", isabelle.Value.Int(port)), ("token", tok)) =>
          mlReplPort = Some(port)
          mlReplToken = Some(tok)
          Output.writeln("IQPlugin: ML_Repl port = " + port)
          true
        case List(_, ("port", isabelle.Value.Int(port))) =>
          mlReplPort = Some(port)
          Output.writeln("IQPlugin: ML_Repl port = " + port)
          true
        case _ => false
      }
    }

    override val functions: Session.Protocol_Functions =
      List("IR_Repl.port" -> handle_port)
  }
}

class IQPlugin extends EBPlugin {
  private var iqServer: Option[IQServer] = None
  def currentServer: Option[IQServer] = iqServer

  override def start(): Unit = {
    // Plugin initialization
    Output.writeln("Isabelle/Q Plugin with MCP Server starting...")
    IQPlugin.register(this)
    startServer()
  }

  private def buildSecurityConfig(): IQServerSecurityConfig = {
    val uiSettings = IQUISettings.current
    IQSecurity.fromEnvironment(
      readEnv = key => Option(Isabelle_System.getenv(key)),
      readUiMutationRoots = () =>
        Option(uiSettings.allowedMutationRoots).map(_.trim).filter(_.nonEmpty),
      readUiReadRoots = () =>
        Option(uiSettings.allowedReadRoots).map(_.trim).filter(_.nonEmpty)
    )
  }

  private def startServer(): Unit = {
    val securityConfig = buildSecurityConfig()
    var tryPort = IQPlugin.DEFAULT_PORT
    val maxPort = tryPort + IQPlugin.MAX_PORT_SCAN
    var started = false
    while (!started && tryPort < maxPort) {
      try {
        iqServer = Some(new IQServer(port = tryPort, securityConfig = securityConfig))
        iqServer.foreach(_.start())
        System.setProperty(IQPlugin.PORT_PROPERTY, tryPort.toString)
        System.setProperty(IQPlugin.AUTH_TOKEN_PROPERTY, securityConfig.authToken)
        started = true
        IQPlugin.mcpPort = Some(tryPort)
        Output.writeln(s"Isabelle/Q Server started successfully on port $tryPort")
        IQPlugin.activateWidget("iq-mcp-status")
      } catch {
        case _: java.net.BindException =>
          iqServer = None
          tryPort += 1
        case ex: Exception =>
          iqServer = None
          Output.writeln(s"Failed to start Isabelle/Q Server: ${ex.getMessage}")
          ex.printStackTrace()
          return
      }
    }
    if (!started) {
      Output.writeln(
        s"Failed to start Isabelle/Q Server: no free port in range ${IQPlugin.DEFAULT_PORT}–${maxPort - 1}"
      )
    }
  }

  override def stop(): Unit = {
    // Plugin cleanup
    Output.writeln("Isabelle/Q Plugin with MCP Server stopping...")

    // Remove status bar widgets
    val key = "view.status"
    val current = jEdit.getProperty(key, "")
    val cleaned = current.replace("iq-mcp-status", "").replace("ir-repl-status", "")
      .replaceAll("  +", " ").trim
    jEdit.setProperty(key, cleaned)

    // Stop MCP server
    iqServer.foreach(_.stop())
    iqServer = None
    IQPlugin.mcpPort = None
    System.clearProperty(IQPlugin.PORT_PROPERTY)
    System.clearProperty(IQPlugin.AUTH_TOKEN_PROPERTY)

    // Stop I/R daemon
    IQExploreDockable.shutdown()

    // Stop ML_Repl TCP server so Poly/ML can exit cleanly
    try { PIDE.session.protocol_command("IR_Repl.stop") }
    catch { case _: Exception => }

    Output.writeln("Isabelle/Q Plugin stopped")
    IQPlugin.unregister(this)
  }

  def restartServerFromSettings(): Unit = synchronized {
    Output.writeln(
      "I/Q settings changed: restarting MCP server to apply security root updates..."
    )
    iqServer.foreach(_.stop())
    iqServer = None
    startServer()
  }

  override def handleMessage(message: EBMessage): Unit = {
    message match {
      case msg: org.gjt.sp.jedit.msg.ViewUpdate
        if msg.getWhat == org.gjt.sp.jedit.msg.ViewUpdate.CLOSED
          && jEdit.getViewCount() == 0 =>
        // Last window closed — shut down I/R like a full quit
        IQExploreDockable.shutdown()
        try { PIDE.session.protocol_command("IR_Repl.stop") }
        catch { case _: Exception => }
      case _ =>
    }
  }
}
