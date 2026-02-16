/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.{EBMessage, EBPlugin}

/** jEdit plugin lifecycle: starts/stops Assistant services and cleans up resources. */
class AssistantPlugin extends EBPlugin {
  override def start(): Unit = {
    Output.writeln("Isabelle Assistant starting...")
    IQAvailable.logStatus()
  }

  override def stop(): Unit = {
    Output.writeln("Isabelle Assistant stopping...")
    AssistantDockable.shutdown()
    BedrockClient.cleanup()
    ErrorHandler.cleanupAll()
    VerificationCache.clear()
    PromptLoader.clearCache()
    LLMResponseCache.clear()
  }

  override def handleMessage(message: EBMessage): Unit = {}
}
