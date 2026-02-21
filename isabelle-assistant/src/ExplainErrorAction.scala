/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer

/** Extracts and explains PIDE error messages at cursor using LLM with goal/definition context. */
object ExplainErrorAction {
  def explainError(view: View): Unit = {
    ChatAction.addMessage(ChatAction.User, ":explain-error")
    AssistantDockable.showConversation(ChatAction.getHistory)

    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition

    extractErrorAtOffset(buffer, offset) match {
      case None =>
        ChatAction.addResponse("No error at cursor position.")
      case Some(error) =>
        val commandText =
          CommandExtractor.getCommandAtOffset(buffer, offset).getOrElse("")
        val goalState = GoalExtractor.getGoalState(buffer, offset)

        ActionHelper.runAndRespond(
          "assistant-explain-error",
          "Explaining error..."
        ) {
          val defContext = ContextFetcher.getContext(view)
          val subs = Map("error" -> error, "context" -> commandText) ++
            goalState.map("goal_state" -> _) ++ defContext.map(
              "definitions" -> _
            )
          val prompt = PromptLoader.load("explain_error.md", subs)
          BedrockClient.invokeInContext(prompt)
        }
    }
  }

  def extractErrorAtOffset(buffer: JEditBuffer, offset: Int): Option[String] = {
    try {
      Document_Model.get_model(buffer).flatMap { model =>
        val snapshot = Document_Model.snapshot(model)
        // Expand search to entire command span, not just 1 character at cursor
        val command = IQIntegration.getCommandAtOffset(buffer, offset)
        val range = command match {
          case Some(cmd) => cmd.range
          case None => 
            // Fallback to single char, clamped to buffer length
            val safeEnd = math.min(offset + 1, buffer.getLength)
            Text.Range(offset, safeEnd)
        }

        val errors = snapshot.cumulate(range, List.empty[String],
          Markup.Elements(Markup.ERROR_MESSAGE, Markup.ERROR), _ => {
            case (acc, Text.Info(_, XML.Elem(Markup(Markup.ERROR_MESSAGE, _), body))) =>
              Some(acc :+ XML.content(body))
            case (acc, Text.Info(_, XML.Elem(Markup(Markup.ERROR, _), body))) =>
              Some(acc :+ XML.content(body))
            case _ => None
          })

        val allErrors = errors.flatMap(_._2).distinct
        if (allErrors.nonEmpty) Some(allErrors.mkString("\n")) else None
      }
    } catch {
      case _: Exception => None
    }
  }

  def hasErrorAtOffset(buffer: JEditBuffer, offset: Int): Boolean =
    extractErrorAtOffset(buffer, offset).isDefined
}
