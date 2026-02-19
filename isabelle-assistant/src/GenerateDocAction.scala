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

  /** Chat command handler: generate doc for command at cursor. */
  def chatGenerate(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    CommandExtractor.getCommandAtOffset(buffer, offset) match {
      case Some(commandText) =>
        generateInternal(view, commandText, "definition")
      case None =>
        ChatAction.addResponse("No command found at cursor position.")
    }
  }

  def generate(view: View, commandText: String, commandType: String): Unit = {
    ChatAction.addMessage("user", ":generate-doc")
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
      ActionHelper.runAsync("assistant-gendoc", "Generating documentation...") {
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
