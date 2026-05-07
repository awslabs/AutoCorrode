/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import javax.swing.JOptionPane

/** Summarizes theory content via LLM, with context window size checking. */
object SummarizeTheoryAction {
  /** Estimate context window size based on model ID.
    * `private[assistant]` so tests can pin the lookup table without going
    * through `AssistantOptions` — a mistaken 200000 → 32000 regression here
    * would silently gate out large summaries on capable models. */
  private[assistant] def estimateContextWindowFor(modelIdLower: String): Int = {
    if (modelIdLower.contains("claude-sonnet") || modelIdLower.contains("claude-opus") || modelIdLower.contains("claude-4")) 200000
    else if (modelIdLower.contains("claude")) 200000
    else if (modelIdLower.contains("llama3") || modelIdLower.contains("llama-3")) 128000
    else if (modelIdLower.contains("mistral-large")) 128000
    else if (modelIdLower.contains("titan")) 32000
    else 100000 // conservative default
  }

  private def estimateContextWindow: Int =
    estimateContextWindowFor(AssistantOptions.getModelId.toLowerCase)

  def summarize(view: View): Unit = {
    val buffer = view.getBuffer
    val source = buffer.getText(0, buffer.getLength)
    val estimatedTokens = source.length / 4
    val contextWindow = estimateContextWindow

    if (estimatedTokens > contextWindow * 0.8) {
      val proceed = JOptionPane.showConfirmDialog(view,
        s"Theory file is ~$estimatedTokens tokens, which may exceed the model's context window (~$contextWindow tokens).\nContinue?",
        "Large Theory Warning", JOptionPane.YES_NO_OPTION, JOptionPane.WARNING_MESSAGE)
      if (proceed != JOptionPane.YES_OPTION) {
        () // user declined
      } else doSummarize(view, buffer, source)
    } else doSummarize(view, buffer, source)
  }

  private def doSummarize(view: View, buffer: org.gjt.sp.jedit.Buffer, source: String): Unit = {
    val theoryName =
      TheoryMetadata.theoryName(buffer).getOrElse(buffer.getName.stripSuffix(".thy"))

    val promptOpt = try {
      Some(PromptLoader.load("summarize_theory.md", Map("theory_name" -> theoryName, "source" -> source)))
    } catch {
      case ex: Exception =>
        GUI.error_dialog(view, "Isabelle Assistant", "Failed to load prompt: " + ex.getMessage)
        None
    }

    promptOpt.foreach { prompt =>
      ActionHelper.runAndRespond("assistant-summarize", "Summarizing theory…") {
        BedrockClient.invokeInContext(prompt)
      }
    }
  }
}
