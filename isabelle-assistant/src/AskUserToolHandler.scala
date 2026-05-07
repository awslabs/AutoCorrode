/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import java.util.concurrent.{CountDownLatch, TimeUnit}
import scala.annotation.unused

import ToolArgs._

/** Executes the ask_user tool and hosts the shared prompt-with-choices
  * primitive used by both this tool and ToolPermissions.promptUser.
  *
  * Split out of AssistantTools so the ask-user flow (widget construction +
  * latch-based wait + timeout handling) lives alongside its HTML builder.
  */
private[assistant] object AskUserToolHandler {

  /** Timeout in seconds to wait for the user to click an option. */
  private val PROMPT_TIMEOUT_SECONDS = 300L

  /** Poll interval for the latch while we check the global cancel flag. */
  private val LATCH_POLL_MS = 500L

  /** Prompt the user with a question and a list of options. Returns
    * Some(choice) if the user clicks one; None on timeout or cancel.
    * Requires at least two options.
    */
  def promptUserWithChoices(
      question: String,
      options: List[String],
      context: String,
      @unused view: View
  ): Option[String] = {
    if (options.length < 2) return None

    val latch = new CountDownLatch(1)
    @volatile var selectedOption = ""

    GUI_Thread.later {
      val html = buildAskUserHtml(question, context, options, { choice =>
        selectedOption = choice
        latch.countDown()
      })
      ChatAction.addMessage(
        ChatAction.Message(
          ChatAction.Widget,
          html,
          java.time.LocalDateTime.now(),
          rawHtml = true,
          transient = true
        )
      )
      AssistantDockable.showConversation(ChatAction.getHistory)
    }

    AssistantDockable.setStatus("Waiting for your input…")

    var responded = false
    val endTime = System.currentTimeMillis() + PROMPT_TIMEOUT_SECONDS * 1000L
    while (!responded && !AssistantDockable.isCancelled && System.currentTimeMillis() < endTime) {
      responded = latch.await(LATCH_POLL_MS, TimeUnit.MILLISECONDS)
    }

    if (AssistantDockable.isCancelled || !responded) {
      None
    } else {
      AssistantDockable.setStatus("Processing your choice…")
      GUI_Thread.later {
        ChatAction.addMessage(
          ChatAction.Message(
            ChatAction.User,
            s"You selected: $selectedOption.",
            java.time.LocalDateTime.now(),
            transient = true
          )
        )
        AssistantDockable.showConversation(ChatAction.getHistory)
      }
      Some(selectedOption)
    }
  }

  def execAskUser(args: ResponseParser.ToolArgs, view: View): String = {
    val question = safeStringArg(args, "question", 500)
    val optionsStr = safeStringArg(args, "options", 1000)
    val context = safeStringArg(args, "context", 500)

    if (question.isEmpty) return "Error: question required"

    val options = optionsStr.split(",").map(_.trim).filter(_.nonEmpty).toList
    if (options.length < 2) return "Error: at least 2 options required"

    promptUserWithChoices(question, options, context, view) match {
      case Some(choice)                          => choice
      case None if AssistantDockable.isCancelled => "User cancelled the operation."
      case None                                  => "User did not respond within the time limit."
    }
  }

  private def buildAskUserHtml(
      question: String,
      context: String,
      options: List[String],
      onChoice: String => Unit
  ): String =
    WidgetRenderer.askUser(question, context, options, onChoice)
}
