/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

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
      ChatAction.addMessage(ChatAction.Assistant, s"Error: $msg")
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
}
