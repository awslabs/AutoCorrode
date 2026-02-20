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
    
    val goalState = GoalExtractor.getGoalState(buffer, offset)
    if (goalState.isEmpty) {
      GUI.warning_dialog(view, "Isabelle Assistant", "No goal at cursor")
    } else {
      val command = CommandExtractor.getCommandAtOffset(buffer, offset).getOrElse("")
      val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
    
      ActionHelper.runAndRespond("assistant-suggest-strategy", "Analyzing goal...") {
        val bundle =
          ProofContextSupport.collect(
            view,
            offset,
            commandOpt,
            goalState,
            includeDefinitions = true
          )
        val subs = Map("goal_state" -> goalState.get, "command" -> command) ++
          bundle.localFactsOpt.map("local_facts" -> _) ++
          bundle.relevantTheoremsOpt.map("relevant_theorems" -> _) ++
          bundle.definitionsOpt.map("context" -> _)
        val prompt = PromptLoader.load("suggest_strategy.md", subs)
        BedrockClient.invokeInContext(prompt)
      }
    }
  }
}
