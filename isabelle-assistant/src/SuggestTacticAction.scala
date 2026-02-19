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
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
    val canVerify = IQAvailable.isAvailable && commandOpt.isDefined && hasEisbach
    
    ActionHelper.runAsync("assistant-suggest-tactic", "Generating Eisbach method...") {
      val context = ContextFetcher.getContext(view, 3000)
      val subs = Map("proof_pattern" -> proofPattern) ++ context.map("context" -> _)
      val prompt = PromptLoader.load("suggest_tactic.md", subs)
      val response = BedrockClient.invokeInContext(prompt).trim
      response.linesIterator.map(_.trim).find(_.startsWith("method ")).getOrElse(response)
    }(
      methodLine => {
        if (canVerify) {
          // Verify the generated method definition via I/Q
          GUI_Thread.later {
            VerifyWithRetry.verify(view, commandOpt.get,
              methodLine, methodLine, 1,
              retryPrompt = (failed, error) => s"Your Eisbach method failed:\n```\n$error\n```\nFailed attempt:\n```\n$failed\n```\nOriginal pattern:\n```isabelle\n$proofPattern\n```\nFix the method. Output ONLY the corrected method line.",
              extractCode = resp => resp.linesIterator.map(_.trim).find(_.startsWith("method ")).getOrElse(resp),
              showResult = (resp, badge) => showMethodResult(view, resp, hasEisbach, badge))
          }
        } else {
          showMethodResult(view, methodLine, hasEisbach, VerificationBadge.Unverified)
        }
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
