/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/** Displays proof context (local facts) at cursor via I/Q print_context query. */
object PrintContextAction {
  
  /** Get context facts as string for use in prompts.
    * Must be called from a background thread (not the GUI thread).
    * Returns None safely if called from EDT to avoid deadlock. */
  def getContextString(view: View): Option[String] = {
    if (javax.swing.SwingUtilities.isEventDispatchThread) {
      Output.warning("[Assistant] PrintContextAction.getContextString called from GUI thread — returning None to avoid deadlock")
      return None
    }

    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
    
    commandOpt.flatMap { command =>
      var result: Option[String] = None
      val latch = new java.util.concurrent.CountDownLatch(1)
      
      GUI_Thread.later {
        runPrintContextAsync(view, command, 5000, { response =>
          response match {
            case Right(output) if output.trim.nonEmpty && !output.contains("No local facts") =>
              result = Some(output.trim)
            case _ =>
              result = None
          }
          latch.countDown()
        })
      }
      
      latch.await(6000, java.util.concurrent.TimeUnit.MILLISECONDS)
      result
    }
  }

  def run(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)

    commandOpt match {
      case None =>
        GUI.warning_dialog(view, "Isabelle Assistant", "No command at cursor")
      case Some(command) =>
        AssistantDockable.setStatus("Getting context...")

        GUI_Thread.later {
          runPrintContextAsync(view, command, 5000, { result =>
            GUI_Thread.later {
              displayResult(result)
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            }
          })
        }
    }
  }

  /** Run print_context query via I/Q. MUST be called from the GUI thread. */
  def runPrintContextAsync(
    view: View,
    command: Command,
    timeoutMs: Long,
    callback: Either[String, String] => Unit
  ): Unit = {
    IQIntegration.runQueryAsync(view, command, List("print_context"), timeoutMs, callback)
  }

  private def displayResult(result: Either[String, String]): Unit = {
    result match {
      case Right(output) if output.trim.nonEmpty =>
        AssistantDockable.respondInChat(s"Context:\n\n```\n${output.trim}\n```")
      case Right(_) =>
        AssistantDockable.respondInChat("No local facts in scope.")
      case Left(error) =>
        AssistantDockable.respondInChat(s"Error: $error")
    }
  }
}
