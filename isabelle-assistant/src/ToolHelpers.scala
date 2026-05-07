/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Shared utilities for tool handlers.
  *
  * Extracted from `AssistantTools` so that sibling handler objects
  * (`TheoryNavToolHandler`, `TheoryMetadataToolHandler`, etc.) do not have to
  * reach back into their former host module for common operations like
  * "resolve a theory name to an on-disk path" or "strip numbering from an
  * I/Q `read_file` response". Keeping these together in a dedicated module:
  *
  *   - breaks the circular-feel coupling between handlers and the parent,
  *   - surfaces the complete I/Q call timeout used by read-only tools, and
  *   - lets the layering gate reason about helpers without needing
  *     `AssistantTools`-specific exceptions.
  *
  * All members are package-private: they're part of the handler internal
  * contract, not the plugin's public surface.
  */
private[assistant] object ToolHelpers {

  /** Total timeout for read-only I/Q calls: the context-fetch budget plus a
    * small buffer to accommodate transport jitter. Used directly by
    * `callListFiles`, `callReadFile`, `callGetFileStats`, etc. */
  val readToolsTimeoutMs: Long =
    AssistantConstants.CONTEXT_FETCH_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS

  private val numberedLinePattern = """^\s*(?:→\s*)?(\d+):(.*)$""".r

  /** Snapshot of the things we want to read from `View`/`Buffer` under the
    * EDT lock. All accesses happen inside a single `GUI_Thread.now` so we
    * never interleave mutations from editor events. */
  final case class ViewStateSnapshot(
      path: Option[String],
      caretOffset: Int,
      bufferLength: Int
  )

  /** Append `.thy` to a raw theory name if missing; leave already-suffixed
    * names alone. Trims whitespace so accidental padding in a tool arg
    * doesn't silently break path matching. */
  def normalizeTheoryFileName(raw: String): String = {
    val trimmed = raw.trim
    if (trimmed.endsWith(".thy")) trimmed else s"$trimmed.thy"
  }

  /** Last path component, as a `String`. Wraps `java.nio.file.Paths` so the
    * handlers don't each import Paths individually. */
  def baseName(path: String): String =
    java.nio.file.Paths.get(path).getFileName.toString

  /** Read the view's buffer path, caret offset, and buffer length while
    * holding the EDT lock. Returns `None` when the view is null or an
    * exception escapes the EDT probe. */
  def snapshotViewState(view: View): Option[ViewStateSnapshot] =
    Option(view).flatMap { v =>
      try {
        Some(
          GUI_Thread.now {
            val bufferOpt = Option(v.getBuffer)
            val path =
              bufferOpt.flatMap(b => Option(b.getPath)).map(_.trim).filter(_.nonEmpty)
            val bufferLength = bufferOpt.map(_.getLength).getOrElse(0)
            val caretOffset = Option(v.getTextArea).map(_.getCaretPosition).getOrElse(0)
            ViewStateSnapshot(path, caretOffset, bufferLength)
          }
        )
      } catch {
        case _: Exception => None
      }
    }

  /** Path of the buffer in `view`, or an `Error: ...` message if no view /
    * no path is available. */
  def currentBufferPath(view: View): Either[String, String] =
    snapshotViewState(view)
      .flatMap(_.path)
      .toRight("Error: current buffer has no path")

  /** Resolve a user-supplied theory name (with or without `.thy`) to an
    * absolute path that the I/Q server recognises. When `openOnly` is true,
    * only files already open in jEdit are considered — this is the typical
    * safety default for read-only tools that operate on the user's current
    * editing session. Pass `openOnly = false` to widen to all tracked
    * theories. */
  def resolveTheoryPath(
      theory: String,
      openOnly: Boolean = true
  ): Either[String, String] = {
    val normalized = normalizeTheoryFileName(theory)
    IQMcpClient
      .callListFiles(
        filterOpen = if (openOnly) Some(true) else None,
        filterTheory = Some(true),
        sortBy = Some("path"),
        timeoutMs = readToolsTimeoutMs
      )
      .flatMap { result =>
        val matches = result.files.filter(f => baseName(f.path) == normalized)
        matches match {
          case one :: Nil => Right(one.path)
          case Nil =>
            val scopeHint =
              if (openOnly) "open or tracked theory files" else "tracked theory files"
            Left(s"Theory '$theory' not found in $scopeHint.")
          case many =>
            Left(
              s"Theory '$theory' is ambiguous; matching paths: ${
                  many.map(_.path).mkString(", ")
                }"
            )
        }
      }
  }

  /** Count lines in an I/Q `read_file` response that look numbered (e.g.
    * `  42: …`). Useful when the caller wants `lines = N` metadata. */
  def lineCountFromNumberedContent(content: String): Int =
    content.linesIterator.count {
      case numberedLinePattern(_, _) => true
      case _                         => false
    }

  private def stripNumberPrefix(line: String): String = line match {
    case numberedLinePattern(_, rest) => rest
    case _                            => line
  }

  /** Strip the leading `  N:` number prefixes emitted by I/Q's `read_file`
    * from every line of a response, yielding the plain source text. */
  def stripNumberPrefixes(content: String): String =
    content.linesIterator.map(stripNumberPrefix).mkString("\n")

  /** Best-effort summary of a search-context block: returns the line the
    * server highlighted with a `→` marker, falling back to the first
    * non-empty line. Number prefixes are stripped and the result is
    * trimmed. */
  def firstHighlightedOrFirstLine(context: String): String = {
    val nonEmpty = context.linesIterator.map(_.trim).filter(_.nonEmpty).toList
    val picked = nonEmpty.find(_.startsWith("→")).orElse(nonEmpty.headOption).getOrElse("")
    stripNumberPrefix(picked).trim
  }
}
