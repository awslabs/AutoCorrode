/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Recommends high-level proof strategies using LLM with MePo-filtered context. */
object SuggestStrategyAction {

  def suggest(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition

    ChatAction.addMessage(ChatAction.User, ":suggest-strategy")
    AssistantDockable.showConversation(ChatAction.getHistory)

    // Goal and command lookups both go through I/Q MCP, so they must run
    // on a background thread. The old code did the goal check on the EDT,
    // which froze jEdit when MCP was slow.
    ActionHelper.runAsync(
      "assistant-suggest-strategy",
      "Analyzing goal…"
    ) {
      GoalExtractor.getGoalState(buffer, offset) match {
        case None => ""
        case Some(goalState) =>
          val command =
            CommandExtractor.getCommandAtOffset(buffer, offset).getOrElse("")
          val bundle = ProofContextSupport.collect(
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
    }(response => {
      if (response.isEmpty)
        GUI.warning_dialog(view, "Isabelle Assistant", "No goal at cursor")
      else {
        ChatAction.addMessage(ChatAction.Assistant, response)
        AssistantDockable.showConversation(ChatAction.getHistory)
      }
      AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
    })
  }
}
