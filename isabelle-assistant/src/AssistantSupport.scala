/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.buffer.JEditBuffer

/**
 * Detects Assistant feature support level based on theory imports.
 * Reports FullSupport (Assistant_Support imported), PartialSupport (I/Q or Eisbach),
 * or NoSupport (LLM-only). Used by the status bar and help dialog.
 */
object AssistantSupport {
  
  sealed trait Status
  case object FullSupport extends Status      // Assistant_Support imported
  case object PartialSupport extends Status   // I/Q available or Eisbach imported  
  case object NoSupport extends Status        // No special support
  
  /** Check if a theory appears in explicit or open-buffer-resolvable imports. */
  private def hasTheoryImport(buffer: JEditBuffer, theoryName: String): Boolean = {
    TheoryMetadata.hasImport(buffer, theoryName)
  }
  
  private def hasAssistantSupport(buffer: JEditBuffer): Boolean =
    hasTheoryImport(buffer, "Assistant_Support")
  
  private def hasEisbachImport(buffer: JEditBuffer): Boolean =
    // Assistant_Support imports Eisbach, so if we have Assistant_Support we have Eisbach
    hasAssistantSupport(buffer) || hasTheoryImport(buffer, "Eisbach")
  
  def getStatus(buffer: JEditBuffer): Status = {
    val hasAssistant = hasAssistantSupport(buffer)
    val hasEisbach = hasEisbachImport(buffer)
    val hasIQ = IQAvailable.isAvailable
    
    // Full support requires Assistant_Support (which includes Eisbach)
    if (hasAssistant) FullSupport
    // Partial if we have I/Q or Eisbach but not Assistant_Support
    else if (hasIQ || hasEisbach) PartialSupport
    else NoSupport
  }
  
  def hasEisbach(buffer: JEditBuffer): Boolean = 
    hasAssistantSupport(buffer) || hasEisbachImport(buffer)
  
  def hasIQ: Boolean = IQAvailable.isAvailable
  
  def importSuggestion: String = 
    """imports "Isabelle_Assistant.Assistant_Support" (* or: imports "$ISABELLE_ASSISTANT_HOME/Assistant_Support" *)"""
  
  def statusText(status: Status): String = status match {
    case FullSupport => "Ready"
    case PartialSupport =>
      if (!IQAvailable.isAvailable) "No I/Q"
      else "Partial"
    case NoSupport => "LLM Only"
  }
  
  def statusColor(status: Status): java.awt.Color = status match {
    case FullSupport => ThemeUtils.successColor
    case PartialSupport => ThemeUtils.warningColor
    case NoSupport => ThemeUtils.neutralColor
  }
  
  def helpText(buffer: JEditBuffer): String = {
    val hasAssistant = hasAssistantSupport(buffer)
    val hasEisbach = hasEisbachImport(buffer)
    val hasIQ = IQAvailable.isAvailable
    
    val features = List(
      if (hasIQ) "[ok] Proof verification (I/Q)" else "[n/a] Proof verification (I/Q not installed)",
      if (hasIQ) "[ok] Sledgehammer integration" else "[n/a] Sledgehammer (I/Q not installed)",
      if (hasEisbach || hasAssistant) "[ok] Custom tactic generation (Eisbach)" else "[n/a] Custom tactics (import Eisbach)",
      if (hasIQ) "[ok] Simplifier tracing" else "[n/a] Simplifier tracing (I/Q not installed)"
    ).mkString("\n")
    
    if (hasAssistant && hasIQ) {
      s"""Assistant has full support enabled.
         |
         |$features""".stripMargin
    } else {
      s"""Assistant feature status:
         |
         |$features
         |
         |For full features, import:
         |$importSuggestion""".stripMargin
    }
  }
}
