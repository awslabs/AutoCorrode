/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.buffer.JEditBuffer

/** Extracts proof blocks via typed I/Q MCP introspection and detects apply-style proofs. */
object ProofExtractor {
  private val ProofBlockLookupTimeoutMs =
    AssistantConstants.CONTEXT_FETCH_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS

  private def selectionArgs(buffer: JEditBuffer, offset: Int): Map[String, Any] = {
    val clamped = math.max(0, math.min(offset, buffer.getLength))
    MenuContext.bufferPath(buffer) match {
      case Some(path) =>
        Map(
          "command_selection" -> "file_offset",
          "path" -> path,
          "offset" -> clamped
        )
      case None =>
        Map("command_selection" -> "current")
    }
  }

  def getProofBlockAtOffset(
      buffer: JEditBuffer,
      offset: Int
  ): Option[String] = {
    IQMcpClient
      .callGetProofBlock(selectionArgs(buffer, offset), ProofBlockLookupTimeoutMs)
      .toOption
      .filter(_.hasProofBlock)
      .map(_.proofText.trim)
      .filter(_.nonEmpty)
  }

  def isApplyStyleProof(proofText: String): Boolean =
    proofText.linesIterator.exists(line =>
      CommandMatcher.startsWithKeyword(line, "apply")
    )
}
