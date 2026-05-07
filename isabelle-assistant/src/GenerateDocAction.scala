/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Generates Isabelle documentation comments for definitions, datatypes,
  * lemmas, and theorems.
  *
  * Uses LLM to analyze the code structure and produce properly formatted text
  * blocks with Isabelle's document markup symbols (\<^verbatim>, \<^const>,
  * \<^term>, etc.).
  *
  * The generated documentation follows Isabelle conventions and is suitable for
  * HTML and PDF document generation via isabelle build.
  */

/** Generates documentation comments for Isabelle definitions and theorems via
  * LLM.
  */
object GenerateDocAction {

  private val documentableKeywords = IsabelleKeywords.entityKeywords

  /** Detect the command type from source text (legacy, used as fallback). */
  def detectCommandType(source: String): Option[String] = {
    CommandMatcher.findMatchingKeyword(source, documentableKeywords)
  }

  /** Detect the command type using PIDE span name at a buffer offset. Preferred
    * over detectCommandType(source) — no string splitting.
    */
  def detectCommandTypeAtOffset(
      buffer: org.gjt.sp.jedit.buffer.JEditBuffer,
      offset: Int
  ): Option[String] = {
    CommandExtractor
      .getCommandKeyword(buffer, offset)
      .filter(documentableKeywords.contains)
  }

  /** Chat command handler: generate doc for command at cursor.
    * The MCP-backed command lookup must run on a background thread, not on
    * the EDT, or the entire jEdit UI freezes for the duration of the round
    * trip. Capture buffer + caret offset on the EDT (Swing requires it) and
    * do the resolution inside the async body.
    */
  def chatGenerate(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    ActionHelper.runAsync("assistant-gendoc", "Generating documentation…") {
      CommandExtractor.getCommandAtOffset(buffer, offset) match {
        case Some(commandText) =>
          val prompt = PromptLoader.load(
            "generate_doc.md",
            Map("command" -> commandText, "command_type" -> "definition")
          )
          BedrockClient.invokeInContext(prompt)
        case None =>
          ""
      }
    }(response => {
      if (response.isEmpty) {
        ChatAction.addResponse(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      } else {
        val cleaned = SendbackHelper.stripCodeFences(response.trim)
        AssistantDockable.respondInChat(
          "Generated documentation:",
          Some(
            (
              cleaned,
              () =>
                view.getBuffer
                  .insert(view.getTextArea.getCaretPosition, cleaned)
            )
          )
        )
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      }
    })
  }

  def generate(view: View, commandText: String, commandType: String): Unit = {
    ChatAction.addMessage(ChatAction.User, ":generate-doc")
    AssistantDockable.showConversation(ChatAction.getHistory)
    generateInternal(view, commandText, commandType)
  }

  private def generateInternal(
      view: View,
      commandText: String,
      commandType: String
  ): Unit = {
    val promptOpt = try {
      Some(
        PromptLoader.load(
          "generate_doc.md",
          Map("command" -> commandText, "command_type" -> commandType)
        )
      )
    } catch {
      case ex: Exception =>
        AssistantDockable.respondInChat(
          s"Failed to load prompt: ${ex.getMessage}"
        )
        None
    }

    promptOpt.foreach { prompt =>
      ActionHelper.runAsync("assistant-gendoc", "Generating documentation…") {
        BedrockClient.invokeInContext(prompt)
      }(response => {
        val cleaned = SendbackHelper.stripCodeFences(response.trim)
        AssistantDockable.respondInChat(
          "Generated documentation:",
          Some(
            (
              cleaned,
              () =>
                view.getBuffer
                  .insert(view.getTextArea.getCaretPosition, cleaned)
            )
          )
        )
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      })
    }
  }
}
