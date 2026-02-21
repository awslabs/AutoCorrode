/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Generates Eisbach method definitions from proof patterns via LLM. */
object SuggestTacticAction {
  
  /** Chat command handler: suggest tactic for command at cursor. */
  def chatSuggest(view: View): Unit = {
    CommandExtractor.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition) match {
      case Some(commandText) => suggest(view, commandText)
      case None => ChatAction.addResponse("No proof pattern found at cursor position.")
    }
  }

  def suggest(view: View, proofPattern: String): Unit = {
    ChatAction.addMessage(ChatAction.User, ":suggest-tactic selection")
    AssistantDockable.showConversation(ChatAction.getHistory)
    
    val hasEisbach = AssistantSupport.hasEisbach(view.getBuffer)
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val goalState = GoalExtractor.getGoalState(buffer, offset)
    
    ActionHelper.runAsync("assistant-suggest-tactic", "Generating Eisbach method...") {
      val bundle =
        ProofContextSupport.collect(
          view,
          offset,
          goalState,
          includeDefinitions = true
        )
      val subs = Map("proof_pattern" -> proofPattern) ++
        goalState.map("goal_state" -> _) ++
        bundle.localFactsOpt.map("local_facts" -> _) ++
        bundle.relevantTheoremsOpt.map("relevant_theorems" -> _) ++
        bundle.definitionsOpt.map("context" -> _)
      val prompt = PromptLoader.load("suggest_tactic.md", subs)
      val response =
        SendbackHelper.stripCodeFences(BedrockClient.invokeInContext(prompt).trim)
      response.linesIterator.map(_.trim).find(_.startsWith("method ")).getOrElse(response)
    }(
      methodLine => {
        val badge =
          if (hasEisbach) VerificationBadge.Unverified
          else VerificationBadge.EisbachMissing
        showMethodResult(view, methodLine, hasEisbach, badge)
      }
    )
  }

  private def showMethodResult(view: View, methodLine: String, hasEisbach: Boolean, badge: VerificationBadge.BadgeType): Unit = {
    val sb = new StringBuilder()
    if (!hasEisbach) {
      val importId = AssistantDockable.registerAction(() =>
        view.getBuffer.insert(view.getTextArea.getCaretPosition, AssistantSupport.importSuggestion))
      sb.append(s"Warning: Eisbach not imported. Add: `${AssistantSupport.importSuggestion}` {{INSERT:$importId}}\n\n")
    }
    val badgeStr = badge match {
      case VerificationBadge.Verified(t) => s" [ok]${t.map(ms => s" (${ms}ms)").getOrElse("")}"
      case VerificationBadge.Failed(r) => s" [FAIL]${if (r.nonEmpty) s" ($r)" else ""}"
      case _ => ""
    }
    val methodId = AssistantDockable.registerAction(() =>
      view.getBuffer.insert(view.getTextArea.getCaretPosition, methodLine))
    sb.append(s"`$methodLine`$badgeStr {{INSERT:$methodId}}")
    ChatAction.addMessage(ChatAction.Assistant, sb.toString)
    AssistantDockable.showConversation(ChatAction.getHistory)
    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
  }
}
