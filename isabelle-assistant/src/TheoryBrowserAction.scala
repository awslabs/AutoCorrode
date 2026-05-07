/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import scala.annotation.unused

/** Theory browsing commands: list, read, search, and dependency inspection. */
object TheoryBrowserAction {

  private val timeoutMs: Long =
    AssistantConstants.CONTEXT_FETCH_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS

  private val numberedLinePattern = """^\s*(?:→\s*)?(\d+):(.*)$""".r

  private[assistant] def baseName(path: String): String =
    java.nio.file.Paths.get(path).getFileName.toString

  private[assistant] def stripNumberPrefixes(content: String): String =
    content.linesIterator
      .map {
        case numberedLinePattern(_, rest) => rest
        case other                        => other
      }
      .mkString("\n")

  private[assistant] def firstHighlightedOrFirstLine(context: String): String = {
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

  /** Run a synchronous MCP-backed action on a background thread and post its
    * result to the chat. All four :theories/:read/:deps/:search commands
    * share this scaffold because every path resolves into one or more
    * IQMcpClient.call* round trips that must not run on the EDT.
    */
  private def runBrowser(threadName: String, status: String)(body: => String): Unit = {
    AssistantDockable.setStatus(status)
    val _ = Isabelle_Thread.fork(name = threadName) {
      val outcome: Either[String, String] =
        try Right(body)
        catch {
          case ex: Exception => Left(ex.getMessage)
        }
      GUI_Thread.later {
        outcome match {
          case Right(result) => ChatAction.addResponse(result)
          case Left(err)     => ChatAction.addErrorResponse(err, threadName)
        }
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      }
    }
  }

  def theories(): Unit = runBrowser("assistant-theories", "Listing theories…") {
    IQMcpClient
      .callListFiles(
        filterOpen = Some(true),
        filterTheory = Some(true),
        sortBy = Some("path"),
        timeoutMs = timeoutMs
      )
      .fold(
        err => s"Error listing theories: $err",
        listed => {
          val theories = listed.files
            .map(f => baseName(f.path).stripSuffix(".thy"))
            .distinct
            .sorted
          if (theories.nonEmpty)
            s"**Open Theories (${theories.length}):**\n\n- ${theories.mkString("\n- ")}"
          else "No theory files currently open."
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
    runBrowser("assistant-read-theory", s"Reading $theoryName…") {
      resolveTheoryPath(theoryName).fold(
        identity,
        path =>
          IQMcpClient
            .callReadFileLine(
              path = path,
              startLine = Some(1),
              endLine = Some(math.max(1, maxLines)),
              timeoutMs = timeoutMs
            )
            .fold(
              readErr => s"Error reading theory: $readErr",
              content => s"**Theory: $theoryName**\n\n```isabelle\n$content\n```"
            )
      )
    }
  }

  def deps(@unused view: View, theoryName: String): Unit = {
    if (theoryName.trim.isEmpty) {
      ChatAction.addResponse("Usage: `:deps <theory>`")
      return
    }
    runBrowser("assistant-deps", s"Reading dependencies of $theoryName…") {
      resolveTheoryPath(theoryName).fold(
        identity,
        path =>
          IQMcpClient
            .callReadFileLine(
              path = path,
              startLine = Some(1),
              endLine = Some(-1),
              timeoutMs = timeoutMs
            )
            .fold(
              readErr => s"Error getting dependencies: $readErr",
              content => {
                val importPattern = """(?s)imports\s+(.*?)(?:\bbegin\b|\z)""".r
                val plain = stripNumberPrefixes(content)
                importPattern.findFirstMatchIn(plain) match {
                  case Some(m) =>
                    val tokenPattern = """"[^"]+"|[^\s"]+""".r
                    val imports =
                      tokenPattern.findAllIn(m.group(1)).toList.filter(_.nonEmpty)
                    if (imports.nonEmpty)
                      s"**Dependencies of $theoryName:**\n\n- ${imports.mkString("\n- ")}"
                    else
                      s"Theory '$theoryName' has no explicit imports."
                  case None =>
                    s"No imports found in theory '$theoryName'."
                }
              }
            )
      )
    }
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
    runBrowser("assistant-search-theory", s"Searching $theoryName…") {
      resolveTheoryPath(theoryName).fold(
        identity,
        path =>
          IQMcpClient
            .callReadFileSearch(
              path = path,
              pattern = pattern,
              contextLines = 0,
              timeoutMs = timeoutMs
            )
            .fold(
              searchErr => s"Error searching theory: $searchErr",
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
                      s"\n\n… (showing $maxResults of ${matches.length} matches)"
                    else ""
                  s"**Found matches in $theoryName:**\n\n$matchList$truncated"
                } else
                  s"No matches found for '$pattern' in theory '$theoryName'."
              }
            )
      )
    }
  }
}
