/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Cleans up Isabelle code via LLM (cartouches, formatting) with optional I/Q
  * verification and retry.
  */
object TidyAction {

  private val tidySchema = StructuredResponseSchema(
    "return_code", "Return the tidied Isabelle code",
    """{"type":"object","properties":{"code":{"type":"string"}},"required":["code"]}"""
  )

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
          val subs = buildPromptSubstitutions(code, goalState, bundle)

          val prompt = PromptLoader.load("tidy.md", subs)
          val args = BedrockClient.invokeInContextStructured(prompt, tidySchema)
          val tidied = ResponseParser.toolValueToString(args.getOrElse("code", ResponseParser.NullValue))

          commandOpt match {
            case Some(command) if IQAvailable.isAvailable =>
              val invokeAndExtract: String => String = { retryPrompt =>
                val retryArgs = BedrockClient.invokeNoCacheStructured(retryPrompt, tidySchema)
                ResponseParser.toolValueToString(retryArgs.getOrElse("code", ResponseParser.NullValue))
              }
              GUI_Thread.later {
                VerifyWithRetry.verify(
                  view,
                  command,
                  tidied,
                  tidied,
                  1,
                  retryPrompt = (failed, error) =>
                    PromptLoader.load(
                      "tidy_retry.md",
                      buildPromptSubstitutions(
                        code,
                        goalState,
                        bundle,
                        Map("failed_attempt" -> failed, "error" -> error)
                      )
                    ),
                  invokeAndExtract = invokeAndExtract,
                  showResult = (resp, badge) => showResult(view, resp, badge)
                )
              }
            case _ =>
              GUI_Thread.later {
                showResult(view, tidied, VerificationBadge.Unverified)
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
      code: String,
      badge: VerificationBadge.BadgeType
  ): Unit = {
    AssistantDockable.setBadge(badge)
    AssistantDockable.respondInChat(
      "Tidied code:",
      Some((code, InsertHelper.createInsertAction(view, code)))
    )
    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
  }

  private[assistant] def buildPromptSubstitutions(
      code: String,
      goalState: Option[String],
      bundle: ProofContextSupport.ContextBundle,
      extra: Map[String, String] = Map.empty
  ): Map[String, String] =
    Map("code" -> code) ++
      goalState.map("goal_state" -> _) ++
      bundle.localFactsOpt.map("local_facts" -> _) ++
      bundle.relevantTheoremsOpt.map("relevant_theorems" -> _) ++
      bundle.definitionsOpt.map("context" -> _) ++
      extra
}
