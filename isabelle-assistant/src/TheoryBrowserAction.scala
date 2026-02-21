/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.View
import scala.annotation.unused

/** Theory browsing commands: list, read, search, and dependency inspection. */
object TheoryBrowserAction {

  private val timeoutMs: Long =
    AssistantConstants.CONTEXT_FETCH_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS

  private val numberedLinePattern = """^\s*(?:→\s*)?(\d+):(.*)$""".r

  private def baseName(path: String): String =
    java.nio.file.Paths.get(path).getFileName.toString

  private def stripNumberPrefixes(content: String): String =
    content.linesIterator
      .map {
        case numberedLinePattern(_, rest) => rest
        case other                        => other
      }
      .mkString("\n")

  private def firstHighlightedOrFirstLine(context: String): String = {
    val lines = context.linesIterator.map(_.trim).filter(_.nonEmpty).toList
    lines.find(_.startsWith("→")).orElse(lines.headOption).map {
      case numberedLinePattern(_, rest) => rest.trim
      case other                        => other
    }.getOrElse("")
  }

  private def resolveTheoryPath(theoryName: String): Either[String, String] = {
    val normalized =
      if (theoryName.endsWith(".thy")) theoryName else s"$theoryName.thy"
    IQMcpClient
      .callListFiles(
        filterOpen = Some(true),
        filterTheory = Some(true),
        sortBy = Some("path"),
        timeoutMs = timeoutMs
      )
      .flatMap { listed =>
        val matches = listed.files.filter(f => baseName(f.path) == normalized)
        matches match {
          case one :: Nil => Right(one.path)
          case Nil =>
            Left(
              s"Theory '$theoryName' not found in open buffers. Use :theories to list available theories."
            )
          case many =>
            Left(
              s"Theory '$theoryName' is ambiguous across open buffers: ${
                  many.map(_.path).mkString(", ")
                }"
            )
        }
      }
  }

  def theories(): Unit = {
    IQMcpClient
      .callListFiles(
        filterOpen = Some(true),
        filterTheory = Some(true),
        sortBy = Some("path"),
        timeoutMs = timeoutMs
      )
      .fold(
        err => ChatAction.addResponse(s"Error listing theories: $err"),
        listed => {
          val theories = listed.files
            .map(f => baseName(f.path).stripSuffix(".thy"))
            .distinct
            .sorted
          if (theories.nonEmpty)
            ChatAction.addResponse(
              s"**Open Theories (${theories.length}):**\n\n- ${theories.mkString("\n- ")}"
            )
          else ChatAction.addResponse("No theory files currently open.")
        }
      )
  }

  def read(@unused view: View, args: String): Unit = {
    if (args.trim.isEmpty) {
      ChatAction.addResponse("Usage: `:read <theory> [lines]`  (default: 100 lines)")
      return
    }
    val parts = args.trim.split("\\s+", 2)
    val theoryName = parts(0)
    val maxLines =
      if (parts.length > 1) try parts(1).toInt
      catch { case _: NumberFormatException => 100 }
      else 100
    resolveTheoryPath(theoryName).fold(
      err => ChatAction.addResponse(err),
      path =>
        IQMcpClient
          .callReadFileLine(
            path = path,
            startLine = Some(1),
            endLine = Some(math.max(1, maxLines)),
            timeoutMs = timeoutMs
          )
          .fold(
            readErr => ChatAction.addResponse(s"Error reading theory: $readErr"),
            content =>
              ChatAction.addResponse(
                s"**Theory: $theoryName**\n\n```isabelle\n$content\n```"
              )
          )
    )
  }

  def deps(@unused view: View, theoryName: String): Unit = {
    if (theoryName.trim.isEmpty) {
      ChatAction.addResponse("Usage: `:deps <theory>`")
      return
    }
    resolveTheoryPath(theoryName).fold(
      err => ChatAction.addResponse(err),
      path =>
        IQMcpClient
          .callReadFileLine(
            path = path,
            startLine = Some(1),
            endLine = Some(-1),
            timeoutMs = timeoutMs
          )
          .fold(
            readErr => ChatAction.addResponse(s"Error getting dependencies: $readErr"),
            content => {
              val importPattern = """(?s)imports\s+(.*?)(?:\bbegin\b|\z)""".r
              val plain = stripNumberPrefixes(content)
              importPattern.findFirstMatchIn(plain) match {
                case Some(m) =>
                  val tokenPattern = """"[^"]+"|[^\s"]+""".r
                  val imports =
                    tokenPattern.findAllIn(m.group(1)).toList.filter(_.nonEmpty)
                  if (imports.nonEmpty)
                    ChatAction.addResponse(
                      s"**Dependencies of $theoryName:**\n\n- ${imports.mkString("\n- ")}"
                    )
                  else
                    ChatAction.addResponse(
                      s"Theory '$theoryName' has no explicit imports."
                    )
                case None =>
                  ChatAction.addResponse(
                    s"No imports found in theory '$theoryName'."
                  )
              }
            }
          )
    )
  }

  def search(@unused view: View, args: String): Unit = {
    val parts = args.split("\\s+", 2)
    if (parts.length < 2) {
      ChatAction.addResponse("Usage: `:search <theory> <pattern>`")
      return
    }
    val theoryName = parts(0)
    val pattern = parts(1)
    val maxResults = 20
    resolveTheoryPath(theoryName).fold(
      err => ChatAction.addResponse(err),
      path =>
        IQMcpClient
          .callReadFileSearch(
            path = path,
            pattern = pattern,
            contextLines = 0,
            timeoutMs = timeoutMs
          )
          .fold(
            searchErr => ChatAction.addResponse(s"Error searching theory: $searchErr"),
            matches => {
              val shown = matches.take(maxResults)
              if (shown.nonEmpty) {
                val matchList = shown
                  .map(m =>
                    s"Line ${m.lineNumber}: ${firstHighlightedOrFirstLine(m.context)}"
                  )
                  .mkString("\n")
                val truncated =
                  if (matches.length > maxResults)
                    s"\n\n... (showing $maxResults of ${matches.length} matches)"
                  else ""
                ChatAction.addResponse(
                  s"**Found matches in $theoryName:**\n\n$matchList$truncated"
                )
              } else
                ChatAction.addResponse(
                  s"No matches found for '$pattern' in theory '$theoryName'."
                )
            }
          )
    )
  }
}
