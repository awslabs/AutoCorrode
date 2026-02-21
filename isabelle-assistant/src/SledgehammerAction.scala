/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/** Runs Sledgehammer via I/Q and displays found proof methods with insert links. */
object SledgehammerAction {
  def run(view: View): Unit = {
    ChatAction.addMessage(ChatAction.User, ":sledgehammer")
    AssistantDockable.showConversation(ChatAction.getHistory)
    
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)

    commandOpt match {
      case None =>
        GUI.warning_dialog(view, "Isabelle Assistant", "No command at cursor")
      case Some(command) =>
        AssistantDockable.setStatus("Running sledgehammer...")
        val timeout = AssistantOptions.getSledgehammerTimeout

        GUI_Thread.later {
          IQIntegration.runSledgehammerAsync(view, command, timeout, {
            case Right(results) if results.nonEmpty =>
              displayResults(view, results)
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            case Right(_) =>
              AssistantDockable.respondInChat("Sledgehammer found no proofs.")
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            case Left(error) =>
              AssistantDockable.respondInChat(s"Sledgehammer error: $error")
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          })
        }
    }
  }

  private def displayResults(view: View, results: List[IQIntegration.SledgehammerResult]): Unit = {
    val sb = new StringBuilder(s"Sledgehammer found ${results.length} proofs:\n\n")
    for (r <- results) {
      val id = AssistantDockable.registerAction(() => {
        val offset = view.getTextArea.getCaretPosition
        view.getBuffer.insert(offset, r.proofMethod)
      })
      sb.append(s"[sledgehammer] `${r.proofMethod}` (${r.timeMs}ms) {{INSERT:$id}}\n")
    }
    ChatAction.addMessage(ChatAction.Assistant, sb.toString)
    AssistantDockable.showConversation(ChatAction.getHistory)
  }
}
