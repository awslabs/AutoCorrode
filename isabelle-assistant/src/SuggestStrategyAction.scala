/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Recommends high-level proof strategies using LLM with MePo-filtered context. */
object SuggestStrategyAction {

  def suggest(view: View): Unit = {
    ChatAction.addMessage(ChatAction.User, ":suggest-strategy")
    AssistantDockable.showConversation(ChatAction.getHistory)

    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition

    GoalExtractor.getGoalState(buffer, offset) match {
      case None =>
        GUI.warning_dialog(view, "Isabelle Assistant", "No goal at cursor")
      case Some(goalState) =>
        val command =
          CommandExtractor.getCommandAtOffset(buffer, offset).getOrElse("")

        ActionHelper.runAndRespond(
          "assistant-suggest-strategy",
          "Analyzing goal..."
        ) {
          val bundle =
            ProofContextSupport.collect(
              view,
              offset,
              Some(goalState),
              includeDefinitions = true
            )
          val subs = Map("goal_state" -> goalState, "command" -> command) ++
            bundle.localFactsOpt.map("local_facts" -> _) ++
            bundle.relevantTheoremsOpt.map("relevant_theorems" -> _) ++
            bundle.definitionsOpt.map("context" -> _)
          val prompt = PromptLoader.load("suggest_strategy.md", subs)
          BedrockClient.invokeInContext(prompt)
        }
    }
  }
}
