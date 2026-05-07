/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/**
 * Analyzes proof patterns across a theory file and suggests improvements.
 * Proof blocks are extracted through typed I/Q MCP introspection.
 */
object AnalyzePatternsAction {
  private val MaxProofBlocks = 30
  private val MinProofChars = 8
  private val ProofBlocksTimeoutMs =
    AssistantConstants.DEFAULT_FIND_THEOREMS_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS

  def analyze(view: View): Unit = {
    val buffer = view.getBuffer
    val maybePath = MenuContext.bufferPath(buffer)

    if (!IQAvailable.isAvailable) {
      GUI.warning_dialog(
        view,
        "Isabelle Assistant",
        "I/Q is required for pattern analysis."
      )
      return
    }

    maybePath match {
      case None =>
        GUI.warning_dialog(
          view,
          "Isabelle Assistant",
          "Current buffer has no file path. Save the theory and retry pattern analysis."
        )
      case Some(path) =>
        // fetchProofBlocks goes to I/Q MCP and must not run on the EDT.
        ActionHelper.runAsync(
          "assistant-analyze-patterns",
          "Analyzing proof patterns…"
        ) {
          fetchProofBlocks(path) match {
            case Left(error) => s"ERROR:$error"
            case Right(proofs) if proofs.isEmpty => "EMPTY"
            case Right(proofs) =>
              val subs = Map(
                "proofs" -> proofs.mkString("\n\n---\n\n"),
                "proof_count" -> proofs.length.toString
              )
              val prompt = PromptLoader.load("analyze_patterns.md", subs)
              BedrockClient.invokeInContext(prompt)
          }
        }(response => {
          if (response.startsWith("ERROR:")) {
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            GUI.warning_dialog(
              view,
              "Isabelle Assistant",
              s"Failed to extract proof blocks: ${response.stripPrefix("ERROR:")}"
            )
          } else if (response == "EMPTY") {
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            GUI.warning_dialog(
              view,
              "Isabelle Assistant",
              "No proof blocks found in theory."
            )
          } else {
            ChatAction.addMessage(ChatAction.Assistant, response)
            AssistantDockable.showConversation(ChatAction.getHistory)
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
        })
    }
  }

  private def fetchProofBlocks(path: String): Either[String, List[String]] =
    IQMcpClient
      .callGetProofBlocksForFile(
        path = path,
        maxResults = Some(MaxProofBlocks),
        minChars = Some(MinProofChars),
        timeoutMs = ProofBlocksTimeoutMs
      )
      .map(_.proofBlocks.map(_.proofText.trim).filter(_.length >= MinProofChars))
}
