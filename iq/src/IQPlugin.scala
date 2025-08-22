/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._

import org.gjt.sp.jedit.{EBMessage, EBPlugin}

class IQPlugin extends EBPlugin {
  private var iqServer: Option[IQServer] = None

  override def start(): Unit = {
    // Plugin initialization
    Output.writeln("Isabelle/Q Plugin with MCP Server starting...")

    // Start MCP server
    try {
      iqServer = Some(new IQServer(port = 8765))
      iqServer.foreach(_.start())
      Output.writeln("Isabelle/Q Server started successfully on port 8765")
    } catch {
      case ex: Exception =>
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
  }

  override def handleMessage(message: EBMessage): Unit = {
    // Handle jEdit messages if needed
  }
}
