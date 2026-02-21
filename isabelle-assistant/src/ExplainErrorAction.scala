/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
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
    val clamped = math.max(0, math.min(offset, buffer.getLength))
    val selectionArgs =
      MenuContext.bufferPath(buffer) match {
        case Some(path) =>
          Map(
            "command_selection" -> "file_offset",
            "path" -> path,
            "offset" -> clamped
          )
        case None =>
          Map("command_selection" -> "current")
      }

    IQMcpClient
      .callGetDiagnostics(
        severity = IQMcpClient.DiagnosticSeverity.Error,
        scope = IQMcpClient.DiagnosticScope.Selection,
        timeoutMs =
          AssistantConstants.CONTEXT_FETCH_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS,
        selectionArgs = selectionArgs
      )
      .toOption
      .flatMap { result =>
        val messages = result.diagnostics.map(_.message.trim).filter(_.nonEmpty).distinct
        if (messages.nonEmpty) Some(messages.mkString("\n")) else None
      }
  }

  def hasErrorAtOffset(buffer: JEditBuffer, offset: Int): Boolean =
    extractErrorAtOffset(buffer, offset).isDefined
}
