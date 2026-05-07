/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/**
 * Shared helper for the common action pattern: fork a background thread,
 * run an LLM call, and dispatch the result back to the GUI thread.
 * Uses ErrorHandler for consistent error handling across all actions.
 */
object ActionHelper {

  /**
   * Run an LLM-backed action in the standard fork/try/catch/GUI_Thread.later pattern.
   *
   * @param name   Thread name for debugging
   * @param status Status text shown while running
   * @param body   Background work returning the response string
   * @param onSuccess Called on GUI thread with the response
   * @param onError   Called on GUI thread with the exception message
   */
  def runAsync(
    name: String,
    status: String = AssistantConstants.STATUS_THINKING
  )(body: => String)(
    onSuccess: String => Unit,
    onError: String => Unit = msg => {
      // msg has already been through ErrorHandler.makeUserFriendly in the
      // caller below — addErrorResponse would re-translate. Go directly
      // through ChatAction.addMessage with the Error kind.
      ChatAction.addMessage(
        ChatAction.Message(
          ChatAction.Assistant,
          msg,
          java.time.LocalDateTime.now(),
          kind = ChatAction.ResponseKind.Error
        )
      )
      AssistantDockable.showConversation(ChatAction.getHistory)
      AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
    }
  ): Unit = {
    AssistantDockable.setStatus(status)
    val _ = Isabelle_Thread.fork(name = name) {
      ErrorHandler.withErrorHandling(name) {
        body
      } match {
        case scala.util.Success(response) =>
          GUI_Thread.later { onSuccess(response) }
        case scala.util.Failure(ex) =>
          GUI_Thread.later { onError(ErrorHandler.makeUserFriendly(ex.getMessage, name)) }
      }
    }
  }

  /** Convenience: run async, post response as chat message, set status Ready. */
  def runAndRespond(name: String, status: String = AssistantConstants.STATUS_THINKING)(body: => String): Unit =
    runAsync(name, status)(body)(
      response => {
        ChatAction.addMessage(ChatAction.Assistant, response)
        AssistantDockable.showConversation(ChatAction.getHistory)
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      }
    )

  /**
   * Record a chat-invocation prelude: echo the command into the chat as if
   * the user had typed it, then run the usual async LLM fetch and post the
   * response. Most of the colon-command handlers share this scaffold.
   *
   * @param commandLine    Exact user-visible command (e.g. ":suggest-strategy")
   * @param threadName     Isabelle_Thread name for diagnostics
   * @param status         Busy-indicator status text
   * @param buildPrompt    Runs on a background thread; must return the final
   *                       prompt text to send to the LLM.
   */
  def runChatCommand(
      commandLine: String,
      threadName: String,
      status: String = AssistantConstants.STATUS_THINKING
  )(buildPrompt: => String): Unit = {
    ChatAction.addMessage(ChatAction.User, commandLine)
    AssistantDockable.showConversation(ChatAction.getHistory)
    runAndRespond(threadName, status) {
      BedrockClient.invokeInContext(buildPrompt)
    }
  }

  /**
   * Run an I/Q-backed command action: fork background thread, check command at cursor, execute body.
   * Handles the common pattern of verifying cursor position before dispatching I/Q work.
   * The body receives the view and is executed on a background thread, allowing it to safely
   * call IQIntegration.*Async methods which handle their own threading and GUI callbacks.
   * 
   * @param name Thread name for debugging
   * @param status Status text to display while running
   * @param body Work to execute after verifying command exists (receives View)
   * @param view The current jEdit view
   */
  def runIQCommand(
      name: String,
      status: String
  )(body: View => Unit)(view: org.gjt.sp.jedit.View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    AssistantDockable.setStatus(status)
    
    val _ = Isabelle_Thread.fork(name = name) {
      // Verify command exists at cursor (this may call I/Q MCP so must be on background thread)
      CommandExtractor.getCommandAtOffset(buffer, offset) match {
        case None =>
          GUI_Thread.later {
            ChatAction.addResponse(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
        case Some(_) => 
          // Command exists — execute the body
          // Body will typically call IQIntegration.*Async which handles its own threading
          body(view)
      }
    }
  }

  /**
   * Run an I/Q-backed goal action: fork background thread, check goal state at cursor, execute body.
   * Similar to runIQCommand but checks for goal state instead of command presence.
   * Use this for proof-related actions (sledgehammer, nitpick, etc.) where what matters is
   * whether there's a proof goal, not whether the cursor is on a specific command span.
   * 
   * @param name Thread name for debugging
   * @param status Status text to display while running
   * @param body Work to execute after verifying goal exists (receives View)
   * @param view The current jEdit view
   */
  def runIQGoalAction(
      name: String,
      status: String
  )(body: View => Unit)(view: org.gjt.sp.jedit.View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    AssistantDockable.setStatus(status)
    
    val _ = Isabelle_Thread.fork(name = name) {
      // Verify goal exists at cursor (this calls I/Q MCP so must be on background thread)
      GoalExtractor.getGoalState(buffer, offset) match {
        case None =>
          GUI_Thread.later {
            ChatAction.addResponse(AssistantConstants.UIText.NO_GOAL_AT_CURSOR)
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
        case Some(_) => 
          // Goal exists — execute the body
          // Body will typically call IQIntegration.*Async which handles its own threading
          body(view)
      }
    }
  }
}
