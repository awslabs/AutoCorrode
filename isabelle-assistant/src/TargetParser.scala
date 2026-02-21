/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer
import scala.util.Try
import scala.jdk.CollectionConverters._

/**
 * Parses target specifications for commands like `:explain` and `:suggest`.
 * Supports cursor, selection, file:line, file:range, named elements,
 * relative offsets, and multi-targets.
 */
object TargetParser {
  sealed trait Target
  case class FileRange(theory: String, startLine: Int, endLine: Int) extends Target
  case class FileLine(theory: String, line: Int) extends Target
  case class MultiTarget(targets: List[Target]) extends Target
  case class NamedElement(theory: String, name: String) extends Target
  case class RelativePosition(base: Target, offset: Int) extends Target
  case object CurrentSelection extends Target
  case object CurrentCursor extends Target

  def parseTarget(spec: String, view: View): Option[Target] = {
    spec.trim match {
      case "cursor" | "current" => Some(CurrentCursor)
      case "selection" => Some(CurrentSelection)
      case s if s.matches("""(?:cursor|selection)[+-]\d+""") =>
        // Relative positioning: cursor+5, selection-3
        parseRelativePosition(s)
      case s if s.contains(",") =>
        // Multi-target: Theory.thy:10,20,30-40
        parseMultiTarget(s, view)
      case s if s.contains(":") =>
        val parts = s.split(":", 2)
        if (parts.length == 2) {
          val theory = parts(0)
          parts(1) match {
            case range if range.contains("-") && range.forall(c => c.isDigit || c == '-') =>
              // Range: Theory.thy:10-20
              val lines = range.split("-", 2)
              if (lines.length == 2) {
                for {
                  start <- Try(lines(0).toInt).toOption
                  end <- Try(lines(1).toInt).toOption
                } yield FileRange(theory, start, end)
              } else None
            case line if line.forall(_.isDigit) =>
              // Single line: Theory.thy:42
              Try(line.toInt).toOption.map(FileLine(theory, _))
            case name =>
              // Named element: Theory.thy:lemma_name
              Some(NamedElement(theory, name))
          }
        } else None
      case _ => None
    }
  }

  private def parseRelativePosition(spec: String): Option[Target] = {
    val pattern = """(cursor|selection)([+-]\d+)""".r
    spec match {
      case pattern(base, offsetStr) =>
        val baseTarget = if (base == "cursor") CurrentCursor else CurrentSelection
        Try(offsetStr.toInt).toOption.map(RelativePosition(baseTarget, _))
      case _ => None
    }
  }

  private def parseMultiTarget(spec: String, view: View): Option[Target] = {
    val parts = spec.split(",").map(_.trim)
    val targets = parts.flatMap(part => parseTarget(part, view)).toList
    if (targets.length == parts.length && targets.nonEmpty) {
      Some(MultiTarget(targets))
    } else None
  }

  def resolveTarget(target: Target, view: View): Option[(JEditBuffer, Int, Int)] = {
    target match {
      case CurrentCursor =>
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition
        Some((buffer, offset, offset))
        
      case CurrentSelection =>
        val textArea = view.getTextArea
        val buffer = view.getBuffer
        val selection = textArea.getSelectedText
        if (selection != null && selection.trim.nonEmpty && textArea.getSelectionCount > 0) {
          val sel = textArea.getSelection(0)
          val start = sel.getStart
          val end = sel.getEnd
          Some((buffer, start, end))
        } else None
        
      case FileLine(theory, line) =>
        findTheoryBuffer(theory, view).map { buffer =>
          val offset = buffer.getLineStartOffset(math.max(0, line - 1))
          val endOffset = buffer.getLineEndOffset(math.max(0, line - 1))
          (buffer, offset, endOffset)
        }
        
      case FileRange(theory, startLine, endLine) =>
        findTheoryBuffer(theory, view).map { buffer =>
          val start = buffer.getLineStartOffset(math.max(0, startLine - 1))
          val end = buffer.getLineEndOffset(math.max(0, endLine - 1))
          (buffer, start, end)
        }
        
      case MultiTarget(targets) =>
        // Resolve all targets and concatenate their ranges — only if all in the same buffer
        val resolved = targets.flatMap(resolveTarget(_, view))
        if (resolved.isEmpty) None
        else {
          val firstBuffer = resolved.head._1
          val sameBuffer = resolved.filter(_._1 eq firstBuffer)
          if (sameBuffer.length != resolved.length) None  // cross-buffer targets not supported
          else {
            val start = sameBuffer.map(_._2).min
            val end = sameBuffer.map(_._3).max
            Some((firstBuffer, start, end))
          }
        }
        
      case NamedElement(theory, name) =>
        // Find named element using Isabelle keyword patterns for precise matching
        findTheoryBuffer(theory, view).flatMap { buffer =>
          val content = buffer.getText(0, buffer.getLength)
          val keywords = IsabelleKeywords.entityKeywords
          val lines = content.split("\n")
          lines.zipWithIndex.find { case (line, _) =>
            val trimmed = line.trim
            keywords.exists(kw => trimmed.matches(s"""(?s)$kw\\s+$name\\b.*"""))
          } match {
            case Some((_, lineIdx)) =>
              val offset = buffer.getLineStartOffset(lineIdx)
              val endOffset = buffer.getLineEndOffset(lineIdx)
              Some((buffer, offset, endOffset))
            case None => None
          }
        }
        
      case RelativePosition(base, offset) =>
        // Offset is in lines, not characters
        resolveTarget(base, view).map { case (buffer, start, end) =>
          val baseLine = buffer.getLineOfOffset(start)
          val targetLine = math.max(0, math.min(buffer.getLineCount - 1, baseLine + offset))
          val newStart = buffer.getLineStartOffset(targetLine)
          val newEnd = buffer.getLineEndOffset(targetLine)
          (buffer, newStart, newEnd)
        }
    }
  }

  private def findTheoryBuffer(theoryName: String, view: View): Option[JEditBuffer] =
    MenuContext.findTheoryBuffer(theoryName).orElse {
      // Fall back to current buffer if it matches
      val normalized = if (theoryName.endsWith(".thy")) theoryName else s"$theoryName.thy"
      val currentBuffer = view.getBuffer
      if (currentBuffer.getPath != null && currentBuffer.getPath.endsWith(normalized)) Some(currentBuffer)
      else None
    }

  def formatTarget(target: Target): String = target match {
    case CurrentCursor => "cursor"
    case CurrentSelection => "selection"
    case FileLine(theory, line) => s"$theory:$line"
    case FileRange(theory, start, end) => s"$theory:$start-$end"
    case MultiTarget(targets) => targets.map(formatTarget).mkString(",")
    case NamedElement(theory, name) => s"$theory:$name"
    case RelativePosition(base, offset) => 
      val sign = if (offset >= 0) "+" else ""
      s"${formatTarget(base)}$sign$offset"
  }
}
