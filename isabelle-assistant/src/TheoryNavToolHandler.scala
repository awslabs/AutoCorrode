/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.View

import ToolArgs._

/** Read-only theory-navigation tools: `read_theory`, `list_theories`,
  * `search_in_theory`, `search_all_theories`, `search_theories`,
  * `get_dependencies`.
  *
  * All are thin wrappers over `IQMcpClient.callReadFile*` / `callListFiles`
  * with result formatting. Theory path resolution (`resolveTheoryPath`) and
  * the shared read-tools timeout (`readToolsTimeoutMs`) come from
  * `ToolHelpers`. No proof semantics touched here — the MCP-only layering
  * gate covers each method.
  */
private[assistant] object TheoryNavToolHandler {

  // imports clause parser, compiled once at class init rather than per call.
  private val importClausePattern = """(?s)imports\s+(.*?)(?:\bbegin\b|\z)""".r
  private val importTokenPattern = """"[^"]+"|[^\s"]+""".r

  def execReadTheory(args: ResponseParser.ToolArgs): String =
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        val start = optionalIntArg(args, "start_line")
        val end = optionalIntArg(args, "end_line")
        ToolHelpers.resolveTheoryPath(theory).fold(
          err => err,
          path =>
            IQMcpClient
              .callReadFileLine(
                path = path,
                startLine = start.orElse(Some(1)),
                endLine = end,
                timeoutMs = ToolHelpers.readToolsTimeoutMs
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                content =>
                  if (content.trim.isEmpty) s"Theory $theory is empty."
                  else s"Theory $theory:\n$content"
              )
        )
    }

  def execListTheories(): String =
    IQMcpClient
      .callListFiles(
        filterOpen = Some(true),
        filterTheory = Some(true),
        sortBy = Some("path"),
        timeoutMs = ToolHelpers.readToolsTimeoutMs
      )
      .fold(
        err => s"Error: $err",
        listed => {
          val theories =
            listed.files.map(f => ToolHelpers.baseName(f.path)).distinct.sorted
          if (theories.nonEmpty) theories.mkString("\n")
          else "No theory files open."
        }
      )

  def execSearchInTheory(args: ResponseParser.ToolArgs): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        if (pattern.isEmpty) "Error: pattern required"
        else {
          val max = math.min(
            AssistantConstants.MAX_SEARCH_RESULTS,
            math.max(1, intArg(args, "max_results", 20))
          )
          ToolHelpers.resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient
                .callReadFileSearch(
                  path = path,
                  pattern = pattern,
                  contextLines = 0,
                  timeoutMs = ToolHelpers.readToolsTimeoutMs
                )
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  matches => {
                    val shown = matches.take(max)
                    if (shown.isEmpty) s"No matches for '$pattern' in $theory."
                    else
                      shown
                        .map(m =>
                          s"${m.lineNumber}: ${ToolHelpers.firstHighlightedOrFirstLine(m.context)}"
                        )
                        .mkString("\n")
                  }
                )
          )
        }
    }
  }

  def execSearchAllTheories(args: ResponseParser.ToolArgs): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else {
      val maxTotal = math.min(200, math.max(1, intArg(args, "max_results", 50)))
      IQMcpClient
        .callListFiles(
          filterOpen = Some(true),
          filterTheory = Some(true),
          sortBy = Some("path"),
          timeoutMs = ToolHelpers.readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          listed => {
            val allMatches = scala.collection.mutable.ListBuffer[String]()
            listed.files.iterator
              .takeWhile(_ => allMatches.length < maxTotal)
              .foreach { file =>
                val remaining = maxTotal - allMatches.length
                val matches = IQMcpClient
                  .callReadFileSearch(
                    path = file.path,
                    pattern = pattern,
                    contextLines = 0,
                    timeoutMs = ToolHelpers.readToolsTimeoutMs
                  )
                  .getOrElse(Nil)
                  .take(remaining)
                matches.foreach { m =>
                  allMatches += s"${ToolHelpers.baseName(file.path)}:${m.lineNumber}: ${
                      ToolHelpers.firstHighlightedOrFirstLine(m.context)
                    }"
                }
              }

            if (allMatches.nonEmpty) {
              val truncated =
                if (allMatches.length >= maxTotal) s" (showing first $maxTotal)"
                else ""
              s"Found ${allMatches.length} matches$truncated:\n${allMatches.mkString("\n")}"
            } else s"No matches for '$pattern' in any open theory."
          }
        )
    }
  }

  def execSearchTheories(args: ResponseParser.ToolArgs, view: View): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    val scope = safeStringArg(args, "scope", 200)
    if (pattern.isEmpty) "Error: pattern required"
    else if (scope.isEmpty) "Error: scope required"
    else {
      scope.toLowerCase match {
        case "current" =>
          execSearchInTheory(
            args + (
              "theory" -> ResponseParser.StringValue(
                ToolHelpers.currentBufferPath(view).getOrElse("")
              )
            )
          )
        case "all" => execSearchAllTheories(args)
        case _ =>
          execSearchInTheory(
            args + ("theory" -> ResponseParser.StringValue(scope))
          )
      }
    }
  }

  def execGetDependencies(args: ResponseParser.ToolArgs): String =
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        ToolHelpers.resolveTheoryPath(theory).fold(
          err => err,
          path =>
            IQMcpClient
              .callReadFileLine(
                path = path,
                startLine = Some(1),
                endLine = Some(-1),
                timeoutMs = ToolHelpers.readToolsTimeoutMs
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                numberedContent => {
                  val content = ToolHelpers.stripNumberPrefixes(numberedContent)
                  importClausePattern.findFirstMatchIn(content) match {
                    case Some(m) =>
                      val imports =
                        importTokenPattern
                          .findAllIn(m.group(1))
                          .toList
                          .filter(_.nonEmpty)
                      if (imports.nonEmpty)
                        s"Dependencies of $theory:\n${imports.mkString("\n")}"
                      else s"Theory '$theory' has no explicit imports."
                    case None => s"No imports found in theory '$theory'."
                  }
                }
              )
        )
    }
}
