/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import java.util.concurrent.{ConcurrentHashMap, CountDownLatch, TimeUnit}

/** Tries common proof methods (simp, auto, blast, force, fastforce) in parallel via I/Q. */
object TryMethodsAction {
  private val methods = List("by simp", "by auto", "by blast", "by force", "by fastforce")

  def run(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)

    commandOpt match {
      case None =>
        GUI.warning_dialog(view, "Isabelle Assistant", "No command at cursor")
      case Some(command) =>
        AssistantDockable.setStatus("Trying methods...")
        val timeout = AssistantOptions.getVerificationTimeout

        val results =
          new ConcurrentHashMap[String, IQIntegration.VerificationResult]()
        val latch = new CountDownLatch(methods.length)

        for (method <- methods) {
          GUI_Thread.later {
            IQIntegration.verifyProofAsync(
              view,
              command,
              method,
              timeout, { result =>
                results.put(method, result)
                latch.countDown()
              }
            )
          }
        }

        Isabelle_Thread.fork(name = "try-methods-wait") {
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          GUI_Thread.later {
            displayResults(view, methods.map(m => (m, Option(results.get(m)))))
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
        }
    }
  }

  private def displayResults(view: View, results: List[(String, Option[IQIntegration.VerificationResult])]): Unit = {
    val sb = new StringBuilder("Try Methods Results:\n\n")
    for ((method, resultOpt) <- results) {
      resultOpt match {
        case Some(IQIntegration.ProofSuccess(ms, _)) =>
          val id = AssistantDockable.registerAction(() => {
            view.getBuffer.insert(view.getTextArea.getCaretPosition, method)
          })
          sb.append(s"[ok] `$method` (${ms}ms) {{INSERT:$id}}\n")
        case Some(IQIntegration.ProofFailure(_)) =>
          sb.append(s"[FAIL] `$method` (failed)\n")
        case Some(IQIntegration.ProofTimeout) =>
          sb.append(s"[FAIL] `$method` (timeout)\n")
        case _ =>
          sb.append(s"? `$method`\n")
      }
    }
    ChatAction.addMessage(ChatAction.Assistant, sb.toString)
    AssistantDockable.showConversation(ChatAction.getHistory)
  }
}
