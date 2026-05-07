/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.{EBMessage, EBPlugin}

/** jEdit plugin lifecycle: starts/stops Assistant services and cleans up resources. */
class AssistantPlugin extends EBPlugin {
  override def start(): Unit = {
    Output.writeln("Isabelle Assistant starting…")
    IQAvailable.startHeartbeat()
  }

  override def stop(): Unit = {
    Output.writeln("Isabelle Assistant stopping…")
    IQAvailable.stopHeartbeat()
    AssistantDockable.shutdown()
    ToolPermissions.clearSession()
    BedrockClient.cleanup()
    IQMcpClient.closePool()
    ErrorHandler.cleanupAll()
    VerificationCache.clear()
    PromptLoader.clearCache()
    LLMResponseCache.clear()
  }

  override def handleMessage(message: EBMessage): Unit = {}
}
