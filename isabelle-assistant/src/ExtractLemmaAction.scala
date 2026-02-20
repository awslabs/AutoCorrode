/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer

/** Extracts selected proof steps into a separate reusable lemma. Uses LLM to
  * generate the extracted lemma and updated proof, then optionally verifies
  * both via I/Q with retry on failure.
  */
object ExtractLemmaAction {

  case class ExtractionResult(
      extractedLemma: String,
      updatedProof: String,
      lemmaName: String
  )

  private case class ExtractionContext(
      selectedText: String,
      fullProofBlock: String,
      lemmaStatement: String,
      goalStateAtSelection: Option[String],
      localFacts: Option[String] = None,
      relevantTheorems: Option[String] = None,
      definitions: Option[String] = None
  )

  /** Chat command handler: extract selected text as lemma. */
  def chatExtract(view: View): Unit = {
    val selectedText = view.getTextArea.getSelectedText
    if (selectedText != null && selectedText.trim.nonEmpty)
      extract(view, selectedText)
    else ChatAction.addResponse("Please select text to extract as a lemma.")
  }

  def extract(view: View, selectedText: String): Unit = {
    ChatAction.addMessage(ChatAction.User, ":extract selection")
    AssistantDockable.showConversation(ChatAction.getHistory)

    val buffer = view.getBuffer
    val textArea = view.getTextArea
    val selStart =
      if (textArea.getSelectionCount > 0) textArea.getSelection(0).getStart
      else textArea.getCaretPosition

    val context = getExtractionContext(buffer, selStart, selectedText)
    if (context.isEmpty) {
      GUI.warning_dialog(
        view,
        "Isabelle Assistant",
        "Could not determine proof context"
      )
    } else {
      val ctx = context.get
      val commandOpt = IQIntegration.getCommandAtOffset(buffer, selStart)
      val canVerify = IQAvailable.isAvailable && commandOpt.isDefined

      AssistantDockable.setStatus("Extracting lemma...")
      AssistantDockable.setBadge(VerificationBadge.Verifying)

      Isabelle_Thread.fork(name = "assistant-extract") {
        try {
          val bundle =
            ProofContextSupport.collect(
              view,
              selStart,
              commandOpt,
              ctx.goalStateAtSelection,
              includeDefinitions = true
            )
          val enrichedCtx = ctx.copy(
            localFacts = bundle.localFactsOpt,
            relevantTheorems = bundle.relevantTheoremsOpt,
            definitions = bundle.definitionsOpt
          )

          val prompt = PromptLoader.load(
            "extract_lemma.md",
            Map(
              "selected_text" -> enrichedCtx.selectedText,
              "full_proof" -> enrichedCtx.fullProofBlock,
              "lemma_statement" -> enrichedCtx.lemmaStatement,
              "goal_state" -> enrichedCtx.goalStateAtSelection.getOrElse("")
            )
              ++ enrichedCtx.localFacts.map("local_facts" -> _) ++
              enrichedCtx.relevantTheorems.map("relevant_theorems" -> _) ++
              enrichedCtx.definitions.map("context" -> _)
          )

          val response = BedrockClient.invokeInContext(prompt)
          parseExtractionResponse(response) match {
            case Some(result) if canVerify =>
              GUI_Thread.later {
                startVerification(view, commandOpt.get, enrichedCtx, result, 1)
              }
            case Some(result) =>
              GUI_Thread.later {
                showResult(view, result, VerificationBadge.Unverified)
              }
            case None =>
              GUI_Thread.later {
                ChatAction.addMessage(ChatAction.Assistant, response);
                AssistantDockable.showConversation(ChatAction.getHistory)
                AssistantDockable.setStatus("Could not parse extraction result")
              }
          }
        } catch {
          case ex: Exception =>
            GUI_Thread.later {
              AssistantDockable.setStatus("Error: " + ex.getMessage)
              GUI.error_dialog(view, "Extract Lemma Error", ex.getMessage)
            }
        }
      }
    }
  }

  private def getExtractionContext(
      buffer: JEditBuffer,
      selStart: Int,
      selectedText: String
  ): Option[ExtractionContext] = {
    ProofExtractor.getProofBlockAtOffset(buffer, selStart).map { fullProof =>
      val lemmaStatement = fullProof.linesIterator
        .find(line =>
          CommandMatcher
            .findMatchingKeyword(line, IsabelleKeywords.proofStarters)
            .isDefined
        )
        .getOrElse("")

      ExtractionContext(
        selectedText,
        fullProof,
        lemmaStatement,
        GoalExtractor.getGoalState(buffer, selStart)
      )
    }
  }

  private def parseExtractionResponse(
      response: String
  ): Option[ExtractionResult] = {
    ResponseParser.extractJsonObjectString(response).flatMap { json =>
      for {
        lemma <- ResponseParser.parseStringField(json, "extracted_lemma")
        proof <- ResponseParser.parseStringField(json, "updated_proof")
      } yield {
        val name = """(?:lemma|theorem)\s+(\w+)""".r
          .findFirstMatchIn(lemma)
          .map(_.group(1))
          .getOrElse("extracted")
        ExtractionResult(lemma.trim, proof.trim, name)
      }
    }
  }

  private def startVerification(
      view: View,
      command: Command,
      ctx: ExtractionContext,
      result: ExtractionResult,
      attempt: Int
  ): Unit = {
    val maxRetries = AssistantOptions.getMaxVerificationRetries
    val timeout = AssistantOptions.getVerificationTimeout

    AssistantDockable.setStatus(
      s"Verifying extracted lemma (attempt $attempt/$maxRetries)..."
    )

    GUI_Thread.later {
      IQIntegration.verifyProofAsync(
        view,
        command,
        result.extractedLemma,
        timeout,
        {
          case IQIntegration.ProofSuccess(_, _) =>
            GUI_Thread.later {
              AssistantDockable.setStatus("Verifying updated proof...")
              IQIntegration.verifyProofAsync(
                view,
                command,
                result.updatedProof,
                timeout,
                {
                  case IQIntegration.ProofSuccess(timeMs, _) =>
                    GUI_Thread.later {
                      showResult(
                        view,
                        result,
                        VerificationBadge.Verified(Some(timeMs))
                      )
                    }
                  case IQIntegration.ProofFailure(error)
                      if attempt < maxRetries =>
                    retryInBackground(
                      view,
                      command,
                      ctx,
                      result,
                      s"Updated proof failed: $error",
                      attempt,
                      maxRetries
                    )
                  case IQIntegration.ProofFailure(error) =>
                    GUI_Thread.later {
                      showResult(
                        view,
                        result,
                        VerificationBadge.Failed(
                          s"Updated proof failed: ${error.take(50)}"
                        )
                      )
                    }
                  case _ =>
                    GUI_Thread.later {
                      showResult(view, result, VerificationBadge.Unverified)
                    }
                }
              )
            }

          case IQIntegration.ProofFailure(error) if attempt < maxRetries =>
            retryInBackground(
              view,
              command,
              ctx,
              result,
              s"Extracted lemma failed: $error",
              attempt,
              maxRetries
            )
          case IQIntegration.ProofFailure(error) =>
            GUI_Thread.later {
              showResult(
                view,
                result,
                VerificationBadge.Failed(s"Lemma failed: ${error.take(50)}")
              )
            }
          case _ =>
            GUI_Thread.later {
              showResult(view, result, VerificationBadge.Unverified)
            }
        }
      )
    }
  }

  private def retryInBackground(
      view: View,
      command: Command,
      ctx: ExtractionContext,
      failedResult: ExtractionResult,
      error: String,
      attempt: Int,
      maxRetries: Int
  ): Unit = {
    GUI_Thread.later {
      AssistantDockable.setStatus(s"Retrying (${attempt + 1}/$maxRetries)...")
    }

    Isabelle_Thread.fork(name = "assistant-extract-retry") {
      try {
        val retryPrompt = PromptLoader.load(
          "extract_lemma_retry.md",
          Map(
            "selected_text" -> ctx.selectedText,
            "full_proof" -> ctx.fullProofBlock,
            "lemma_statement" -> ctx.lemmaStatement,
            "goal_state" -> ctx.goalStateAtSelection.getOrElse(""),
            "failed_lemma" -> failedResult.extractedLemma,
            "failed_proof" -> failedResult.updatedProof,
            "error" -> error
          )
            ++ ctx.localFacts.map("local_facts" -> _) ++
            ctx.relevantTheorems.map("relevant_theorems" -> _) ++
            ctx.definitions.map("context" -> _)
        )
        val response = BedrockClient.invokeNoCache(retryPrompt)
        parseExtractionResponse(response) match {
          case Some(result) =>
            GUI_Thread.later {
              startVerification(view, command, ctx, result, attempt + 1)
            }
          case None =>
            GUI_Thread.later {
              showResult(
                view,
                failedResult,
                VerificationBadge.Failed("Retry parse failed")
              )
            }
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            showResult(
              view,
              failedResult,
              VerificationBadge.Failed("Retry error: " + ex.getMessage)
            )
          }
      }
    }
  }

  private def showResult(
      view: View,
      result: ExtractionResult,
      badge: VerificationBadge.BadgeType
  ): Unit = {
    val code = s"${result.extractedLemma}\n\n${result.updatedProof}"
    AssistantDockable.setBadge(badge)
    AssistantDockable.respondInChat(
      s"Extracted lemma '${result.lemmaName}':",
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
}
