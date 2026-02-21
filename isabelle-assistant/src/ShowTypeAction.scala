/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer

/** Displays type information at cursor via typed I/Q MCP introspection. */
object ShowTypeAction {
  private val TypeLookupTimeoutMs =
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

  def showType(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition

    getTypeAtOffset(buffer, offset) match {
      case Some(typ) =>
        AssistantDockable.respondInChat(s"Type: `$typ`")
      case None =>
        AssistantDockable.respondInChat("No type information available at cursor position.")
    }
  }

  def getTypeAtOffset(buffer: JEditBuffer, offset: Int): Option[String] = {
    IQMcpClient
      .callGetTypeAtSelection(selectionArgs(buffer, offset), TypeLookupTimeoutMs)
      .toOption
      .filter(_.hasType)
      .map(_.typeText.trim)
      .filter(_.nonEmpty)
  }

  def hasTypeAtOffset(buffer: JEditBuffer, offset: Int): Boolean =
    getTypeAtOffset(buffer, offset).isDefined
}
