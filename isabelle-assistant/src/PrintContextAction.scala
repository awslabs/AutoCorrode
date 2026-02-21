/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import scala.annotation.unused

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

    var result: Option[String] = None
    val latch = new java.util.concurrent.CountDownLatch(1)

    IQIntegration.getProofContextAsync(view, 5000, {
      case Right(ctx) if ctx.success && ctx.hasContext && ctx.context.trim.nonEmpty =>
        result = Some(ctx.context.trim)
        latch.countDown()
      case _ =>
        result = None
        latch.countDown()
    })

    val _ = latch.await(6000, java.util.concurrent.TimeUnit.MILLISECONDS)
    result
  }

  def run(view: View): Unit = {
    AssistantDockable.setStatus("Getting context...")
    runPrintContextAsync(view, command = null, 5000, { result =>
      GUI_Thread.later {
        displayResult(result)
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      }
    })
  }

  /** Run print_context query via I/Q MCP typed adapter. */
  def runPrintContextAsync(
    view: View,
    @unused command: Command,
    timeoutMs: Long,
    callback: Either[String, String] => Unit
  ): Unit = {
    IQIntegration.getProofContextAsync(view, timeoutMs, {
      case Right(ctx) if ctx.success =>
        callback(Right(ctx.context))
      case Right(ctx) if ctx.timedOut =>
        callback(Left("query timed out"))
      case Right(ctx) =>
        val msg = Option(ctx.error).flatten.getOrElse(ctx.message).trim
        callback(Left(if (msg.nonEmpty) msg else "proof context query failed"))
      case Left(err) =>
        callback(Left(err))
    })
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
