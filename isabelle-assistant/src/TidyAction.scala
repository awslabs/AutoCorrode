/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Cleans up Isabelle code via LLM (cartouches, formatting) with optional I/Q
  * verification and retry.
  */
object TidyAction {
  def tidy(view: View): Unit = {
    val buffer = view.getBuffer
    val textArea = view.getTextArea
    val selection = textArea.getSelectedText

    val code =
      if (selection != null && selection.trim.nonEmpty) selection
      else
        CommandExtractor
          .getCommandAtOffset(buffer, textArea.getCaretPosition)
          .getOrElse("")

    if (code.isEmpty) {
      ChatAction.addResponse(
        "No code to tidy. Select text or place cursor on a command."
      )
    } else {
      val offset = textArea.getCaretPosition
      val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
      val goalState = GoalExtractor.getGoalState(buffer, offset)
      val canVerify = IQAvailable.isAvailable && commandOpt.isDefined

      AssistantDockable.setBadge(VerificationBadge.Verifying)

      Isabelle_Thread.fork(name = "assistant-tidy") {
        try {
          val bundle =
            ProofContextSupport.collect(
              view,
              offset,
              commandOpt,
              goalState,
              includeDefinitions = true
            )
          val subs = Map("code" -> code) ++
            goalState.map("goal_state" -> _) ++
            bundle.localFactsOpt.map("local_facts" -> _) ++
            bundle.relevantTheoremsOpt.map("relevant_theorems" -> _) ++
            bundle.definitionsOpt.map("context" -> _)

          val prompt = PromptLoader.load("tidy.md", subs)
          val response = BedrockClient.invokeInContext(prompt)

          if (!canVerify) {
            GUI_Thread.later {
              showResult(view, response, VerificationBadge.Unverified)
            }
          } else {
            GUI_Thread.later {
              VerifyWithRetry.verify(
                view,
                commandOpt.get,
                extractCode(response),
                response,
                1,
                retryPrompt = (failed, error) =>
                  PromptLoader.load(
                    "tidy_retry.md",
                    Map(
                      "code" -> code,
                      "failed_attempt" -> failed,
                      "error" -> error
                    )
                      ++ goalState.map("goal_state" -> _) ++
                      bundle.localFactsOpt.map("local_facts" -> _) ++
                      bundle.relevantTheoremsOpt.map("relevant_theorems" -> _) ++
                      bundle.definitionsOpt.map("context" -> _)
                  ),
                extractCode = extractCode,
                showResult = (resp, badge) => showResult(view, resp, badge)
              )
            }
          }
        } catch {
          case ex: Exception =>
            GUI_Thread.later {
              AssistantDockable.setStatus("Error: " + ex.getMessage)
              GUI.error_dialog(view, "Tidy Error", ex.getMessage)
            }
        }
      }
    }
  }

  private def showResult(
      view: View,
      response: String,
      badge: VerificationBadge.BadgeType
  ): Unit = {
    val code = extractCode(response)
    AssistantDockable.setBadge(badge)
    AssistantDockable.respondInChat(
      "Tidied code:",
      Some((code, InsertHelper.createInsertAction(view, code)))
    )
    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
  }

  private def extractCode(response: String): String = {
    val fromJson = ResponseParser
      .extractJsonObjectString(response)
      .flatMap { json =>
        ResponseParser.parseStringField(json, "code").map(_.trim)
      }
    val fromFences = SendbackHelper.extractCodeBlocks(response).mkString("\n").trim
    fromJson.orElse(Option(fromFences).filter(_.nonEmpty)).getOrElse(response)
  }
}
