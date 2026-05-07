/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Generates test cases and examples for Isabelle definitions via LLM. */
object GenerateTestsAction {
  
  /** Chat command handler: generate tests for definition at cursor. Resolves
    * the command via MCP inside the async body so the EDT is never blocked.
    */
  def chatGenerate(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    ActionHelper.runAsync("assistant-generate-tests", "Generating test cases...") {
      CommandExtractor.getCommandAtOffset(buffer, offset) match {
        case Some(definitionText) =>
          val context = ContextFetcher.getContext(view, 3000)
          val subs = Map("definition" -> definitionText) ++ context.map("context" -> _)
          val prompt = PromptLoader.load("generate_tests.md", subs)
          SendbackHelper.stripCodeFences(BedrockClient.invokeInContext(prompt).trim)
        case None => ""
      }
    }(cleaned => {
      if (cleaned.isEmpty) {
        ChatAction.addResponse(AssistantConstants.UIText.NO_DEFINITION_AT_CURSOR)
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      } else {
        AssistantDockable.respondInChat(
          "Generated test cases:",
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

  def generate(view: View, definitionText: String): Unit = {
    ChatAction.addMessage(ChatAction.User, ":generate-tests selection")
    AssistantDockable.showConversation(ChatAction.getHistory)
    generateInternal(view, definitionText)
  }

  private def generateInternal(view: View, definitionText: String): Unit = {
    
    ActionHelper.runAsync("assistant-generate-tests", "Generating test cases...") {
      val context = ContextFetcher.getContext(view, 3000)
      val subs = Map("definition" -> definitionText) ++ context.map("context" -> _)
      val prompt = PromptLoader.load("generate_tests.md", subs)
      SendbackHelper.stripCodeFences(BedrockClient.invokeInContext(prompt).trim)
    }(
      cleaned => {
        AssistantDockable.respondInChat("Generated test cases:", Some((cleaned, () =>
          view.getBuffer.insert(view.getTextArea.getCaretPosition, cleaned))))
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      }
    )
  }
}
