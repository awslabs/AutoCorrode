/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer
import scala.jdk.CollectionConverters._
import java.io.File

/** Analyzes cursor context to determine which context menu items to show. */
object MenuContext {

  /** Common view state extracted once for reuse across actions. */
  case class ViewContext(
    buffer: JEditBuffer,
    offset: Int,
    hasCommand: Boolean,
    selection: Option[String]
  ) {
    def hasIQ: Boolean = IQAvailable.isAvailable && hasCommand
  }

  object ViewContext {
    def apply(view: View): ViewContext = {
      val buffer = view.getBuffer
      val offset = view.getTextArea.getCaretPosition
      val hasCommand = CommandExtractor.getCommandAtOffset(buffer, offset).isDefined
      val selection = Option(view.getTextArea.getSelectedText).filter(_.trim.nonEmpty)
      ViewContext(buffer, offset, hasCommand, selection)
    }
  }

  /** Find an open theory buffer by name (with or without .thy suffix). 
    * Uses proper path matching to avoid matching substring theory names. */
  def findTheoryBuffer(theoryName: String): Option[JEditBuffer] = {
    val normalized = if (theoryName.endsWith(".thy")) theoryName else s"$theoryName.thy"
    val buffers = org.gjt.sp.jedit.jEdit.getBufferManager().getBuffers().asScala
      .filter(b => b.getPath != null && b.getPath.endsWith(".thy"))

    val byExactPath = buffers.filter(_.getPath == normalized)
    if (byExactPath.size == 1) return byExactPath.headOption

    val byPathSuffix = buffers.filter { b =>
      val path = b.getPath
      path.endsWith(File.separator + normalized) ||
      path.endsWith("/" + normalized) ||
      path.endsWith("\\" + normalized)
    }
    if (byPathSuffix.size == 1) return byPathSuffix.headOption

    val byFilename = buffers.filter(b => new File(b.getPath).getName == normalized)
    if (byFilename.size == 1) byFilename.headOption
    else None
  }

  /** Best-effort absolute path lookup for a jEdit buffer. */
  def bufferPath(buffer: JEditBuffer): Option[String] =
    buffer match {
      case b: org.gjt.sp.jedit.Buffer =>
        Option(b.getPath).map(_.trim).filter(_.nonEmpty)
      case _ =>
        org.gjt.sp.jedit.jEdit
          .getBufferManager()
          .getBuffers()
          .asScala
          .find(_ eq buffer)
          .flatMap(b => Option(b.getPath).map(_.trim).filter(_.nonEmpty))
    }

  case class Context(
    inProof: Boolean,
    hasGoal: Boolean,
    onError: Boolean,
    onWarning: Boolean,
    hasSelection: Boolean,
    hasCommand: Boolean,
    hasTypeInfo: Boolean,
    hasApplyProof: Boolean,
    onDefinition: Boolean,
    iqAvailable: Boolean
  )

  def analyze(view: View, buffer: JEditBuffer, offset: Int, selection: Option[String]): Context = {
    val inProof = GoalExtractor.isInProofContext(buffer, offset)
    val hasGoal = inProof && GoalExtractor.getGoalState(buffer, offset).isDefined
    val onError = ExplainErrorAction.hasErrorAtOffset(buffer, offset)
    val onWarning = hasWarningAtOffset(buffer, offset)
    val hasSelection = selection.exists(_.trim.nonEmpty)
    val command = CommandExtractor.getCommandAtOffset(buffer, offset)
    val hasCommand = command.isDefined
    val hasTypeInfo = ShowTypeAction.hasTypeAtOffset(buffer, offset)
    val hasApplyProof = {
      val block = if (hasSelection) selection else ProofExtractor.getProofBlockAtOffset(buffer, offset)
      block.exists(ProofExtractor.isApplyStyleProof)
    }
    // Use PIDE span name to detect definition keywords — no string splitting
    val onDefinition = {
      val defKeywords = IsabelleKeywords.entityKeywords
      CommandExtractor.getCommandKeyword(buffer, offset).exists(defKeywords.contains)
    }

    Context(
      inProof = inProof,
      hasGoal = hasGoal,
      onError = onError,
      onWarning = onWarning,
      hasSelection = hasSelection,
      hasCommand = hasCommand,
      hasTypeInfo = hasTypeInfo,
      hasApplyProof = hasApplyProof,
      onDefinition = onDefinition,
      iqAvailable = IQAvailable.isAvailable
    )
  }

  private def hasWarningAtOffset(buffer: JEditBuffer, offset: Int): Boolean = {
    if (!IQAvailable.isAvailable) false
    else {
      val clamped = math.max(0, math.min(offset, buffer.getLength))
      val selectionArgs = bufferPath(buffer) match {
        case Some(path) =>
          Map(
            "command_selection" -> "file_offset",
            "path" -> path,
            "offset" -> clamped
          )
        case None =>
          Map("command_selection" -> "current")
      }
      IQMcpClient
        .callGetDiagnostics(
          severity = IQMcpClient.DiagnosticSeverity.Warning,
          scope = IQMcpClient.DiagnosticScope.Selection,
          timeoutMs = 1000L,
          selectionArgs = selectionArgs
        )
        .toOption
        .exists(_.diagnostics.nonEmpty)
    }
  }
}
