/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._

import org.gjt.sp.jedit.{EBMessage, EBPlugin}

object IQPlugin {
  @volatile private var instance: Option[IQPlugin] = None

  private def register(plugin: IQPlugin): Unit = {
    instance = Some(plugin)
  }

  private def unregister(plugin: IQPlugin): Unit = {
    if (instance.contains(plugin)) instance = None
  }

  def restartServerFromSettings(): Unit = {
    instance.foreach(_.restartServerFromSettings())
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
    // Handle jEdit messages if needed
  }
}
