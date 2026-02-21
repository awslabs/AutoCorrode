/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.buffer.JEditBuffer

/**
 * Extracts the Isabelle command source text at a given buffer offset via I/Q MCP.
 */
object CommandExtractor {
  private val CommandLookupTimeoutMs =
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

  private def resolveCommand(
      buffer: JEditBuffer,
      offset: Int
  ): Option[IQMcpClient.ResolvedCommandTarget] =
    IQMcpClient
      .callResolveCommandTarget(selectionArgs(buffer, offset), CommandLookupTimeoutMs)
      .toOption

  /** Get the source text of the Isabelle command at the given buffer offset.
   */
  def getCommandAtOffset(buffer: JEditBuffer, offset: Int): Option[String] = {
    resolveCommand(buffer, offset).map(_.command.source).filter(_.trim.nonEmpty)
  }

  /** Get the PIDE span name (parsed command keyword) at the given buffer offset.
   *  Uses I/Q command resolution rather than local document traversal.
   */
  def getCommandKeyword(buffer: JEditBuffer, offset: Int): Option[String] = {
    resolveCommand(buffer, offset).map(_.command.keyword).filter(_.nonEmpty)
  }
}
