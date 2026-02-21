/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Converts apply-style proofs to structured Isar via LLM, with optional I/Q
  * verification and retry.
  */
object RefactorAction {

  private val refactorSchema = StructuredResponseSchema(
    "return_code", "Return the refactored Isar proof code",
    """{"type":"object","properties":{"code":{"type":"string"}},"required":["code"]}"""
  )

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
        val args = BedrockClient.invokeInContextStructured(prompt, refactorSchema)
        val code = ResponseParser.toolValueToString(args.getOrElse("code", ResponseParser.NullValue))

        if (!canVerify) {
          GUI_Thread.later {
            showResult(view, code, VerificationBadge.Unverified)
          }
        } else {
          val invokeAndExtract: String => String = { retryPrompt =>
            val retryArgs = BedrockClient.invokeNoCacheStructured(retryPrompt, refactorSchema)
            ResponseParser.toolValueToString(retryArgs.getOrElse("code", ResponseParser.NullValue))
          }
          GUI_Thread.later {
            VerifyWithRetry.verify(
              view,
              commandOpt.get,
              code,
              code,
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
              invokeAndExtract = invokeAndExtract,
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
      code: String,
      badge: VerificationBadge.BadgeType
  ): Unit = {
    AssistantDockable.setBadge(badge)
    AssistantDockable.respondInChat(
      "Refactored to Isar:",
      Some(
        (
          code,
          () => {
            view.getBuffer.insert(view.getTextArea.getCaretPosition, code)
          }
        )
      )
    )
    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
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
