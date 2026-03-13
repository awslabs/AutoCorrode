/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

import org.gjt.sp.jedit.{EBMessage, EBPlugin, jEdit}

object IQPlugin {
  @volatile private var instance: Option[IQPlugin] = None

  /** Port reported by ML_Repl via PIDE protocol message. */
  @volatile var mlReplPort: Option[Int] = None

  private def register(plugin: IQPlugin): Unit = {
    instance = Some(plugin)
  }

  private def unregister(plugin: IQPlugin): Unit = {
    if (instance.contains(plugin)) instance = None
  }

  def restartServerFromSettings(): Unit = {
    instance.foreach(_.restartServerFromSettings())
  }

  /** PIDE protocol handler: receives IR_Repl.port messages from ML. */
  class IR_Repl_Handler extends Session.Protocol_Handler {
    private def handle_port(msg: Prover.Protocol_Output): Boolean = {
      msg.properties match {
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
    // Start MCP server
    try {
      val securityConfig = buildSecurityConfig()
      iqServer = Some(new IQServer(port = 8765, securityConfig = securityConfig))
      iqServer.foreach(_.start())
      Output.writeln("Isabelle/Q Server started successfully on port 8765")
    } catch {
      case ex: Exception =>
        iqServer = None
        Output.writeln(s"Failed to start Isabelle/Q Server: ${ex.getMessage}")
        ex.printStackTrace()
    }
  }

  override def stop(): Unit = {
    // Plugin cleanup
    Output.writeln("Isabelle/Q Plugin with MCP Server stopping...")

    // Stop MCP server
    iqServer.foreach(_.stop())
    iqServer = None

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
