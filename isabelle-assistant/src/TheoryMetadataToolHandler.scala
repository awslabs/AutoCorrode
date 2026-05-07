/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import ToolArgs._

/** Read-only theory-metadata tools: `get_file_stats`, `get_processing_status`,
  * `get_sorry_positions`. All three share the same structure — take a theory
  * name, resolve it to a tracked path, issue a single MCP query, format the
  * result — so they're grouped here rather than cluttering AssistantTools.
  *
  * The handlers delegate path resolution (`resolveTheoryPath`) and the
  * read-tools timeout (`readToolsTimeoutMs`) to `ToolHelpers`, which owns
  * the shared utilities for all tool handlers. They do not themselves
  * execute any proof semantics.
  */
private[assistant] object TheoryMetadataToolHandler {

  def execGetFileStats(args: ResponseParser.ToolArgs): String =
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
        else
          ToolHelpers.resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient.callGetFileStats(path, ToolHelpers.readToolsTimeoutMs).fold(
                err => s"Error: $err",
                stats =>
                  s"""Theory: $theory
                     |Lines: ${stats.lineCount}
                     |Entities: ${stats.entityCount}
                     |Fully Processed: ${stats.fullyProcessed}
                     |Errors: ${stats.errorCount}
                     |Warnings: ${stats.warningCount}""".stripMargin
              )
          )
    }

  def execGetProcessingStatus(args: ResponseParser.ToolArgs): String =
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
        else
          ToolHelpers.resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient.callGetProcessingStatus(path, ToolHelpers.readToolsTimeoutMs).fold(
                err => s"Error: $err",
                status =>
                  s"""Processing Status for $theory:
                     |Fully Processed: ${status.fullyProcessed}
                     |Unprocessed: ${status.unprocessed}
                     |Running: ${status.running}
                     |Finished: ${status.finished}
                     |Failed: ${status.failed}""".stripMargin
              )
          )
    }

  def execGetSorryPositions(args: ResponseParser.ToolArgs): String =
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
        else
          ToolHelpers.resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient.callGetSorryPositions(path, ToolHelpers.readToolsTimeoutMs).fold(
                err => s"Error: $err",
                sorry =>
                  if (sorry.positions.isEmpty) s"No sorry/oops found in $theory."
                  else {
                    val lines = sorry.positions.map { pos =>
                      s"Line ${pos.line}: ${pos.keyword} in ${pos.inProof}"
                    }
                    s"Found ${sorry.count} sorry/oops in $theory:\n${lines.mkString("\n")}"
                  }
              )
          )
    }
}
