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
    val offset = textArea.getCaretPosition
    val selection = textArea.getSelectedText
    // Selection text is EDT-safe; command resolution and goal state are not.
    // Capture EDT-only values here and resolve everything else on the
    // background thread.
    val initialCode =
      if (selection != null && selection.trim.nonEmpty) selection else ""

    AssistantDockable.setBadge(VerificationBadge.Verifying)
    AssistantDockable.setStatus("Tidying code…")

    val _ = Isabelle_Thread.fork(name = "assistant-tidy") {
      try {
        val code =
          if (initialCode.nonEmpty) initialCode
          else
            CommandExtractor
              .getCommandAtOffset(buffer, offset)
              .getOrElse("")

        if (code.isEmpty) {
          GUI_Thread.later {
            AssistantDockable.setBadge(VerificationBadge.Unverified)
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            ChatAction.addResponse(
              "No code to tidy. Select text or place cursor on a command."
            )
          }
        } else {
          val hasCommand =
            CommandExtractor.getCommandAtOffset(buffer, offset).isDefined
          val goalState = GoalExtractor.getGoalState(buffer, offset)

          val bundle =
            ProofContextSupport.collect(
              view,
              offset,
              goalState,
              includeDefinitions = true
            )
          val subs = buildPromptSubstitutions(code, goalState, bundle)

          val prompt = PromptLoader.load("tidy.md", subs)
          val args = BedrockClient.invokeInContextStructured(prompt, tidySchema)
          val tidied = ResponseParser.toolValueToString(args.getOrElse("code", ResponseParser.NullValue))

          if (IQAvailable.isAvailable && hasCommand) {
            val invokeAndExtract: String => String = { retryPrompt =>
              val retryArgs =
                BedrockClient.invokeNoCacheStructured(retryPrompt, tidySchema)
              ResponseParser.toolValueToString(
                retryArgs.getOrElse("code", ResponseParser.NullValue)
              )
            }
            GUI_Thread.later {
              VerifyWithRetry.verify(
                view,
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
          } else {
            GUI_Thread.later {
              showResult(view, tidied, VerificationBadge.Unverified)
            }
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
