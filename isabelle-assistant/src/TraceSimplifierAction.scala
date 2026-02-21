/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Traces simplifier (simp/auto) via I/Q and explains the trace output using
  * LLM.
  */
object TraceSimplifierAction {

  def trace(view: View, method: String = "simp"): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition

    (GoalExtractor.getGoalState(buffer, offset),
     IQIntegration.getCommandAtOffset(buffer, offset),
     IQAvailable.isAvailable) match {
      case (None, _, _) =>
        GUI.warning_dialog(view, "Isabelle Assistant", "No goal at cursor")
      case (_, _, false) =>
        GUI.warning_dialog(view, "Isabelle Assistant", "I/Q required for tracing")
      case (Some(goal), Some(command), true) =>
        AssistantDockable.setStatus(s"Running $method with trace...")
        GUI_Thread.later {
          runSimpTrace(view, command, goal, method)
        }
      case (Some(_), None, true) =>
        GUI.warning_dialog(
          view,
          "Isabelle Assistant",
          "No command at cursor"
        )
    }
  }

  private def runSimpTrace(
      view: View,
      command: Command,
      goal: String,
      method: String
  ): Unit = {
    val timeout = AssistantOptions.getTraceTimeout
    val depth = AssistantOptions.getTraceDepth
    val queryTimeoutMs = timeout * 1000L + AssistantConstants.TIMEOUT_BUFFER_MS

    IQIntegration.runQueryAsync(
      view,
      command,
      List(s"simp_trace $method $timeout $depth"),
      queryTimeoutMs,
      {
        case Right(output) => processTrace(goal, output, method)
        case Left(error)   => processTrace(goal, s"Error: $error", method)
      }
    )
  }

  private def processTrace(
      goal: String,
      traceOutput: String,
      method: String
  ): Unit = {
    if (traceOutput.trim.isEmpty) {
      ChatAction.addMessage(ChatAction.Assistant, "No output captured.")
      AssistantDockable.showConversation(ChatAction.getHistory)
      AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
    } else {
      // Check if it timed out
      val timedOut = traceOutput.contains("TIMED_OUT")

      AssistantDockable.setStatus("Explaining trace...")

      Isabelle_Thread.fork(name = "explain-trace") {
        try {
          val subs = Map(
            "goal" -> goal,
            "trace" -> traceOutput,
            "method" -> method
          ) ++ (if (timedOut) Map("timed_out" -> "true") else Map.empty)

          val prompt = PromptLoader.load("trace_simplifier.md", subs)
          val response = BedrockClient.invokeInContext(prompt)

          GUI_Thread.later {
            ChatAction.addMessage(ChatAction.Assistant, response)
            AssistantDockable.showConversation(ChatAction.getHistory)
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
        } catch {
          case ex: Exception =>
            GUI_Thread.later {
              // Show raw trace if LLM fails
              ChatAction.addMessage(
                ChatAction.Assistant,
                s"Trace output:\n\n$traceOutput"
              )
              AssistantDockable.showConversation(ChatAction.getHistory)
              AssistantDockable.setStatus("Error: " + ex.getMessage)
            }
        }
      }
    }
  }
}
