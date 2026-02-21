/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/** Shared counterexample-finder logic used by both NitpickAction and
  * QuickcheckAction. Parameterized by tool name, timeout getter, and IQ query
  * args.
  */
object CounterexampleFinderAction {
  case class Config(
      toolName: String,
      displayName: String,
      queryArgs: List[String],
      getTimeout: () => Long
  )

  val Nitpick: Config = Config(
    toolName = "nitpick",
    displayName = "Nitpick",
    queryArgs = List("nitpick"),
    getTimeout = () => AssistantOptions.getNitpickTimeout
  )

  val Quickcheck: Config = Config(
    toolName = "quickcheck",
    displayName = "Quickcheck",
    queryArgs = List("quickcheck"),
    getTimeout = () => AssistantOptions.getQuickcheckTimeout
  )

  def run(view: View, config: Config): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)

    commandOpt match {
      case None =>
        GUI.warning_dialog(view, "Isabelle Assistant", "No command at cursor")
      case Some(command) =>
        val goal = GoalExtractor.getGoalState(buffer, offset).getOrElse("")
        AssistantDockable.setStatus(s"Running ${config.toolName}...")
        val timeout = config.getTimeout()

        GUI_Thread.later {
          IQIntegration.runQueryAsync(
            view,
            command,
            config.queryArgs,
            timeout,
            { result =>
              GUI_Thread.later {
                displayResult(view, result, goal, config)
                AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
              }
            }
          )
        }
    }
  }

  private def displayResult(
      view: View,
      result: Either[String, String],
      goal: String,
      config: Config
  ): Unit = {
    result match {
      case Right(output) if output.toLowerCase.contains("counterexample") =>
        val header =
          if (
            config.toolName == "nitpick" && output.toLowerCase.contains(
              "potential"
            )
          )
            s"${config.displayName} found potential counterexample:"
          else s"${config.displayName} found counterexample:"
        val id = AssistantDockable.registerAction(() =>
          ExplainCounterexampleAction.explain(view, goal, output.trim)
        )
        ChatAction.addMessage(
          ChatAction.Assistant,
          s"$header\n\n```\n${output.trim}\n```\n\n{{ACTION:$id:Explain counterexample}}"
        )
        AssistantDockable.showConversation(ChatAction.getHistory)
      case Right(output) if output.toLowerCase.contains("no counterexample") =>
        AssistantDockable.respondInChat(
          s"${config.displayName}: No counterexample found."
        )
      case Right(output) =>
        val text = if (output.trim.isEmpty) "(no output)" else output.trim
        AssistantDockable.respondInChat(
          s"${config.displayName} result:\n\n$text"
        )
      case Left(error) =>
        AssistantDockable.respondInChat(s"${config.displayName} error: $error")
    }
  }
}
