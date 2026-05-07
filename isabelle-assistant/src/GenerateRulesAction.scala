/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Generates introduction and elimination rules for datatypes/definitions via LLM. */
object GenerateRulesAction {
  
  /** Chat command handler: generate intro rule for definition at cursor. */
  def chatGenerateIntro(view: View): Unit =
    chatGenerateFromCursor(view, "generate_intro_rule.md", "intro")

  /** Chat command handler: generate elim rule for definition at cursor. */
  def chatGenerateElim(view: View): Unit =
    chatGenerateFromCursor(view, "generate_elim_rule.md", "elim")

  /** Resolve the command at cursor and run the LLM call. The MCP-backed
    * command resolution must run on a background thread or jEdit locks up.
    */
  private def chatGenerateFromCursor(
      view: View,
      promptFile: String,
      kind: String
  ): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    ActionHelper.runAsync(s"assistant-generate-$kind", s"Generating $kind rule…") {
      CommandExtractor.getCommandAtOffset(buffer, offset) match {
        case Some(definitionText) =>
          val context = ContextFetcher.getContext(view, 3000)
          val subs = Map("definition" -> definitionText) ++ context.map("context" -> _)
          val prompt = PromptLoader.load(promptFile, subs)
          SendbackHelper.stripCodeFences(BedrockClient.invokeInContext(prompt).trim)
        case None => ""
      }
    }(cleaned => {
      if (cleaned.isEmpty) {
        ChatAction.addResponse(AssistantConstants.UIText.NO_DEFINITION_AT_CURSOR)
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      } else {
        AssistantDockable.respondInChat(
          s"Generated $kind rule:",
          Some(
            (
              cleaned,
              () => view.getBuffer.insert(view.getTextArea.getCaretPosition, cleaned)
            )
          )
        )
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      }
    })
  }

  def generateIntro(view: View, definitionText: String): Unit = {
    ChatAction.addMessage(ChatAction.User, ":generate-intro selection")
    AssistantDockable.showConversation(ChatAction.getHistory)
    generateInternal(view, definitionText, "generate_intro_rule.md", "intro")
  }

  def generateElim(view: View, definitionText: String): Unit = {
    ChatAction.addMessage(ChatAction.User, ":generate-elim selection")
    AssistantDockable.showConversation(ChatAction.getHistory)
    generateInternal(view, definitionText, "generate_elim_rule.md", "elim")
  }

  private def generateInternal(view: View, definitionText: String, promptFile: String, kind: String): Unit = {

    ActionHelper.runAsync(s"assistant-generate-$kind", s"Generating $kind rule…") {
      val context = ContextFetcher.getContext(view, 3000)
      val subs = Map("definition" -> definitionText) ++ context.map("context" -> _)
      val prompt = PromptLoader.load(promptFile, subs)
      SendbackHelper.stripCodeFences(BedrockClient.invokeInContext(prompt).trim)
    }(
      cleaned => {
        AssistantDockable.respondInChat(s"Generated $kind rule:", Some((cleaned, () =>
          view.getBuffer.insert(view.getTextArea.getCaretPosition, cleaned))))
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      }
    )
  }
}
