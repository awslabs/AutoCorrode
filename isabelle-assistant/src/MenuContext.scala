/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer
import scala.jdk.CollectionConverters._

/** Analyzes cursor context to determine which context menu items to show. */
object MenuContext {

  /** Common view state extracted once for reuse across actions. */
  case class ViewContext(
    buffer: JEditBuffer,
    offset: Int,
    command: Option[Command],
    selection: Option[String]
  ) {
    def hasIQ: Boolean = IQAvailable.isAvailable && command.isDefined
  }

  object ViewContext {
    def apply(view: View): ViewContext = {
      val buffer = view.getBuffer
      val offset = view.getTextArea.getCaretPosition
      val command = IQIntegration.getCommandAtOffset(buffer, offset)
      val selection = Option(view.getTextArea.getSelectedText).filter(_.trim.nonEmpty)
      ViewContext(buffer, offset, command, selection)
    }
  }

  /** Find an open theory buffer by name (with or without .thy suffix). 
    * Uses proper path matching to avoid matching substring theory names. */
  def findTheoryBuffer(theoryName: String): Option[JEditBuffer] = {
    val normalized = if (theoryName.endsWith(".thy")) theoryName else s"$theoryName.thy"
    val buffers = org.gjt.sp.jedit.jEdit.getBufferManager().getBuffers().asScala
    buffers.find { b =>
      if (b.getPath == null) false
      else {
        val path = b.getPath
        // Match if path ends with /theoryName or exactly equals theoryName
        path.endsWith("/" + normalized) || path.endsWith("\\" + normalized) || 
        java.io.File(path).getName == normalized
      }
    }
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
    try {
      Document_Model.get_model(buffer).exists { model =>
        val snapshot = Document_Model.snapshot(model)
        // Clamp range to avoid exceeding buffer length when cursor is at end
        val safeEnd = math.min(offset + 1, buffer.getLength)
        val range = Text.Range(offset, safeEnd)
        snapshot.cumulate(range, false,
          Markup.Elements(Markup.WARNING_MESSAGE, Markup.WARNING, Markup.LEGACY), _ => {
            case _ => Some(true)
          }).exists(_._2)
      }
    } catch {
      case _: Exception => false
    }
  }
}
