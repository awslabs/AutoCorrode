/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Converts apply-style proofs to structured Isar via LLM, with optional I/Q
  * verification and retry.
  */
object RefactorAction {

  /** Chat command handler: refactor selected proof text. */
  def chatRefactor(view: View): Unit = {
    val selectedText = view.getTextArea.getSelectedText
    if (selectedText != null && selectedText.trim.nonEmpty)
      refactor(view, selectedText)
    else ChatAction.addResponse("Please select proof text to refactor.")
  }

  def refactor(view: View, proofText: String): Unit = {
    ChatAction.addMessage(ChatAction.User, ":refactor selection")
    AssistantDockable.showConversation(ChatAction.getHistory)

    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
    val goalState = GoalExtractor.getGoalState(buffer, offset)
    val canVerify = IQAvailable.isAvailable && commandOpt.isDefined

    AssistantDockable.setBadge(VerificationBadge.Verifying)

    Isabelle_Thread.fork(name = "assistant-refactor") {
      try {
        val bundle =
          ProofContextSupport.collect(
            view,
            offset,
            commandOpt,
            goalState,
            includeDefinitions = true
          )
        val subs = buildPromptSubstitutions(proofText, goalState, bundle)

        val prompt = PromptLoader.load("refactor_to_isar.md", subs)
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
                  "refactor_to_isar_retry.md",
                  buildPromptSubstitutions(
                    proofText,
                    goalState,
                    bundle,
                    Map("failed_attempt" -> failed, "error" -> error)
                  )
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
            GUI.error_dialog(view, "Refactor Error", ex.getMessage)
          }
      }
    }
  }

  private def showResult(
      view: View,
      response: String,
      badge: VerificationBadge.BadgeType
  ): Unit = {
    val insertable = extractCode(response)
    AssistantDockable.setBadge(badge)
    AssistantDockable.respondInChat(
      "Refactored to Isar:",
      Some(
        (
          insertable,
          () => {
            view.getBuffer.insert(view.getTextArea.getCaretPosition, insertable)
          }
        )
      )
    )
    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
  }

  private[assistant] def extractCode(response: String): String = {
    val fromJson = ResponseParser
      .extractJsonObjectString(response)
      .flatMap { json =>
        ResponseParser.parseStringField(json, "code").map(_.trim)
      }
    val fromFences = SendbackHelper.extractCodeBlocks(response).mkString("\n").trim
    fromJson.orElse(Option(fromFences).filter(_.nonEmpty)).getOrElse(response)
  }

  private[assistant] def buildPromptSubstitutions(
      proofText: String,
      goalState: Option[String],
      bundle: ProofContextSupport.ContextBundle,
      extra: Map[String, String] = Map.empty
  ): Map[String, String] =
    Map("proof" -> proofText) ++
      goalState.map("goal_state" -> _) ++
      bundle.localFactsOpt.map("local_facts" -> _) ++
      bundle.relevantTheoremsOpt.map("relevant_theorems" -> _) ++
      bundle.definitionsOpt.map("context" -> _) ++
      extra
}
