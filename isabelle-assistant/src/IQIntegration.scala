/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import scala.annotation.unused
import java.util.Locale

/** Integration layer for I/Q (Isabelle/Q) plugin functionality.
  *
  * Provides asynchronous proof verification, sledgehammer integration, and
  * theorem finding capabilities when I/Q plugin is available. All operations
  * are designed to be non-blocking and provide proper error handling and
  * timeout management.
  *
  * Common pattern abstracted via runIQOperationAsync: create operation, set up
  * callbacks, activate, handle timeout, and deactivate.
  */
object IQIntegration {

  /** Result types for proof verification operations. */
  enum VerificationResult {

    /** Proof verification succeeded with timing information. */
    case ProofSuccess(timeMs: Long, resultState: String = "")

    /** Proof verification failed with error message. */
    case ProofFailure(error: String)

    /** Verification operation timed out. */
    case ProofTimeout

    /** I/Q plugin is not available. */
    case IQUnavailable

    /** Missing required import for verification. */
    case MissingImport(suggestion: String)
  }
  export VerificationResult._

  /** Result from sledgehammer proof search.
    *
    * @param proofMethod
    *   The proof method found by sledgehammer
    * @param timeMs
    *   Time taken to find the proof in milliseconds
    */
  case class SledgehammerResult(proofMethod: String, timeMs: Long)

  /** Structured result from executing a proof step via isar_explore. Unlike
    * VerificationResult, this carries the resulting proof state for chaining.
    */
  case class ProofStepResult(
      complete: Boolean,
      numSubgoals: Option[Int],
      stateText: String,
      timeMs: Long
  )

  /** Get suggestion text for importing Isar_Explore.
    *
    * @return
    *   Import suggestion message
    */
  def getIsarExploreImportSuggestion: String =
    """To use proof verification, import Isar_Explore from the I/Q plugin:
  imports ... "$IQ_HOME/Isar_Explore"
Replace $IQ_HOME with the path to your I/Q plugin installation."""

  private def callbackOnGui[A](callback: A => Unit, result: A): Unit =
    GUI_Thread.later { callback(result) }

  private def runMcpAsync[A](
      threadName: String,
      callback: Either[String, A] => Unit
  )(
      body: => Either[String, A]
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callbackOnGui(callback, Left("I/Q unavailable"))
    } else {
      val _ = IQOperationLifecycle.forkJvmThread(
        name = threadName,
        body = () => callbackOnGui(callback, body)
      )
    }
  }

  private def selectionParamsForView(view: View): Map[String, Any] =
    Option(view) match {
      case None => Map("command_selection" -> "current")
      case Some(v) =>
        try {
          GUI_Thread.now {
            val buffer = v.getBuffer
            val pathOpt = Option(buffer).flatMap(b => Option(b.getPath)).map(_.trim).filter(_.nonEmpty)
            pathOpt match {
              case Some(path) =>
                val rawOffset = Option(v.getTextArea).map(_.getCaretPosition).getOrElse(0)
                val bufferLength = Option(buffer).map(_.getLength).getOrElse(0)
                val offset = math.max(0, math.min(rawOffset, bufferLength))
                Map(
                  "command_selection" -> "file_offset",
                  "path" -> path,
                  "offset" -> offset
                )
              case None =>
                Map("command_selection" -> "current")
            }
          }
        } catch {
          case _: Exception =>
            Map("command_selection" -> "current")
        }
    }

  private def exploreFailureMessage(
      explore: IQMcpClient.ExploreResult,
      fallback: String
  ): String = {
    val message = Option(explore.message).getOrElse("").trim
    if (message.nonEmpty) message
    else Option(explore.error).flatten.map(_.trim).filter(_.nonEmpty).getOrElse(fallback)
  }

  private def indicatesMissingIsarExplore(message: String): Boolean = {
    val lower = Option(message).getOrElse("").toLowerCase(Locale.ROOT)
    lower.contains("isar_explore") || lower.contains("import iq.isar_explore")
  }

  private def parseSledgehammerResults(text: String): List[SledgehammerResult] = {
    val tryThisPattern = """Try this:\s*(.+?)\s*\((\d+(?:\.\d+)?)\s*(ms|s)\)""".r
    tryThisPattern
      .findAllMatchIn(Option(text).getOrElse(""))
      .map { m =>
        val method = m.group(1).trim
        val value = m.group(2).toDouble
        val unit = m.group(3)
        val timeMs =
          if (unit == "s") (value * 1000.0).toLong
          else value.toLong
        SledgehammerResult(method, timeMs)
      }
      .toList
      .distinct
  }

  private def parseFindTheoremsResults(text: String): List[String] =
    Option(text)
      .getOrElse("")
      .linesIterator
      .map(_.trim)
      .filter(_.nonEmpty)
      .filter(line =>
        line.contains(":") &&
          !line.startsWith("found") &&
          !line.contains("error") &&
          !line.contains("Outer syntax") &&
          !line.contains("bad input")
      )
      .toList
      .distinct

  private def resolveCommandForSelection(
      selectionParams: Map[String, Any],
      timeoutMs: Long
  ): Option[IQMcpClient.CommandInfo] =
    IQMcpClient
      .callResolveCommandTarget(
        selectionArgs = selectionParams,
        timeoutMs = timeoutMs
      )
      .toOption
      .map(_.command)

  def resolveCommandTargetAsync(
      view: View,
      timeoutMs: Long,
      callback: Either[String, IQMcpClient.ResolvedCommandTarget] => Unit
  ): Unit =
    runMcpAsync("assistant-resolve-target-via-mcp", callback) {
      IQMcpClient.callResolveCommandTarget(selectionParamsForView(view), timeoutMs)
    }

  def getGoalStateAsync(
      view: View,
      timeoutMs: Long,
      callback: Either[String, IQMcpClient.GoalStateResult] => Unit
  ): Unit =
    runMcpAsync("assistant-goal-state-via-mcp", callback) {
      IQMcpClient.callGetGoalState(selectionParamsForView(view), timeoutMs)
    }

  def getContextInfoAsync(
      view: View,
      timeoutMs: Long,
      callback: Either[String, IQMcpClient.ContextInfoResult] => Unit
  ): Unit =
    runMcpAsync("assistant-context-info-via-mcp", callback) {
      IQMcpClient.callGetContextInfo(selectionParamsForView(view), timeoutMs)
    }

  def getProofContextAsync(
      view: View,
      timeoutMs: Long,
      callback: Either[String, IQMcpClient.ProofContextResult] => Unit
  ): Unit =
    runMcpAsync("assistant-proof-context-via-mcp", callback) {
      IQMcpClient.callGetProofContext(selectionParamsForView(view), timeoutMs)
    }

  def getDefinitionsAsync(
      view: View,
      names: List[String],
      timeoutMs: Long,
      callback: Either[String, IQMcpClient.DefinitionsResult] => Unit
  ): Unit = {
    val normalized = names.map(_.trim).filter(_.nonEmpty).distinct
    if (normalized.isEmpty) {
      callbackOnGui(callback, Left("no names provided"))
    } else
      runMcpAsync("assistant-definitions-via-mcp", callback) {
        IQMcpClient.callGetDefinitions(
          names = normalized,
          selectionArgs = selectionParamsForView(view),
          timeoutMs = timeoutMs
        )
      }
  }

  def getDiagnosticsAtSelectionAsync(
      view: View,
      severity: IQMcpClient.DiagnosticSeverity,
      timeoutMs: Long,
      callback: Either[String, IQMcpClient.DiagnosticsResult] => Unit
  ): Unit =
    runMcpAsync("assistant-diagnostics-selection-via-mcp", callback) {
      IQMcpClient.callGetDiagnostics(
        severity = severity,
        scope = IQMcpClient.DiagnosticScope.Selection,
        timeoutMs = timeoutMs,
        selectionArgs = selectionParamsForView(view)
      )
    }

  def getDiagnosticsForFileAsync(
      path: String,
      severity: IQMcpClient.DiagnosticSeverity,
      timeoutMs: Long,
      callback: Either[String, IQMcpClient.DiagnosticsResult] => Unit
  ): Unit = {
    val normalizedPath = Option(path).map(_.trim).getOrElse("")
    if (normalizedPath.isEmpty) {
      callbackOnGui(callback, Left("path required"))
    } else
      runMcpAsync("assistant-diagnostics-file-via-mcp", callback) {
        IQMcpClient.callGetDiagnostics(
          severity = severity,
          scope = IQMcpClient.DiagnosticScope.File,
          timeoutMs = timeoutMs,
          path = Some(normalizedPath)
        )
      }
  }

  def getEntitiesAsync(
      path: String,
      maxResults: Option[Int],
      timeoutMs: Long,
      callback: Either[String, IQMcpClient.EntitiesResult] => Unit
  ): Unit = {
    val normalizedPath = Option(path).map(_.trim).getOrElse("")
    if (normalizedPath.isEmpty) {
      callbackOnGui(callback, Left("path required"))
    } else
      runMcpAsync("assistant-entities-via-mcp", callback) {
        IQMcpClient.callGetEntities(
          path = normalizedPath,
          maxResults = maxResults,
          timeoutMs = timeoutMs
        )
      }
  }

  /** Verify a proof asynchronously through I/Q MCP. Callback is dispatched on
    * the GUI thread.
    *
    * @param view
    *   The current jEdit view
    * @param proofText
    *   The proof text to verify
    * @param timeoutMs
    *   Timeout in milliseconds
    * @param callback
    *   Callback function to receive the result
    */
  def verifyProofAsync(
      view: View,
      proofText: String,
      timeoutMs: Long,
      callback: VerificationResult => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callbackOnGui(callback, IQUnavailable)
    } else {
      // Check cache first
      val selectionParams = selectionParamsForView(view)
      val commandInfoOpt = resolveCommandForSelection(selectionParams, timeoutMs)
      commandInfoOpt.flatMap(commandInfo =>
        VerificationCache.get(commandInfo, proofText)
      ) match {
        case Some(cachedResult) =>
          callbackOnGui(callback, cachedResult)
        case None =>
          val _ = IQOperationLifecycle.forkJvmThread(
            name = "assistant-verify-via-mcp",
            body = () => {
              val startTime = System.currentTimeMillis()
              val result = IQMcpClient
                .callExplore(
                  query = "proof",
                  arguments = proofText,
                  timeoutMs = timeoutMs,
                  extraParams = selectionParams
                )
                .fold(
                  mcpErr => ProofFailure(s"I/Q MCP verification failed: $mcpErr"),
                  explore => {
                    if (explore.success)
                      ProofSuccess(
                        System.currentTimeMillis() - startTime,
                        Option(explore.results).getOrElse("").trim
                      )
                    else if (explore.timedOut) ProofTimeout
                    else {
                      val message =
                        exploreFailureMessage(explore, "proof verification failed")
                      if (indicatesMissingIsarExplore(message))
                        MissingImport(getIsarExploreImportSuggestion)
                      else ProofFailure(message)
                    }
                  }
                )
              commandInfoOpt.foreach(commandInfo =>
                VerificationCache.put(commandInfo, proofText, result)
              )
              callbackOnGui(callback, result)
            }
          )
      }
    }
  }

  /** Execute a proof step and return the resulting proof state via I/Q MCP.
    * Parses the PROOF_COMPLETE/PROOF_STATE header from isar_explore. Callback
    * is dispatched on the GUI thread.
    */
  def executeStepAsync(
      view: View,
      proofText: String,
      timeoutMs: Long,
      callback: Either[String, ProofStepResult] => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callbackOnGui(callback, Left("I/Q unavailable"))
    } else {
      val selectionParams = selectionParamsForView(view)
      val _ = IQOperationLifecycle.forkJvmThread(
        name = "assistant-execute-step-via-mcp",
        body = () => {
          val startTime = System.currentTimeMillis()
          val result = IQMcpClient
            .callExplore(
              query = "proof",
              arguments = proofText,
              timeoutMs = timeoutMs,
              extraParams = selectionParams
            )
            .fold(
              mcpErr => Left(s"I/Q MCP step execution failed: $mcpErr"),
              explore => {
                if (explore.success) {
                  val text = Option(explore.results).getOrElse("").trim
                  Right(parseStepResult(text, System.currentTimeMillis() - startTime))
                } else if (explore.timedOut) Left("timeout")
                else Left(exploreFailureMessage(explore, "step execution failed"))
              }
            )
          callbackOnGui(callback, result)
        }
      )
    }
  }

  /** Parse the PROOF_COMPLETE/PROOF_STATE header from isar_explore output. */
  private[assistant] def parseStepResult(
      text: String,
      timeMs: Long
  ): ProofStepResult = {
    val lines = text.linesIterator
    if (!lines.hasNext)
      return ProofStepResult(
        complete = true,
        numSubgoals = Some(0),
        stateText = "",
        timeMs = timeMs
      )
    val header = lines.next()
    val rest = if (lines.hasNext) lines.mkString("\n") else ""
    if (header.startsWith("PROOF_COMPLETE"))
      ProofStepResult(
        complete = true,
        numSubgoals = Some(0),
        stateText = rest,
        timeMs = timeMs
      )
    else if (header.startsWith("PROOF_STATE ")) {
      val n =
        scala.util.Try(header.stripPrefix("PROOF_STATE ").trim.toInt).toOption
      ProofStepResult(
        complete = false,
        numSubgoals = n,
        stateText = rest,
        timeMs = timeMs
      )
    } else
      // Legacy format without header — treat as opaque state
      ProofStepResult(
        complete = false,
        numSubgoals = None,
        stateText = text,
        timeMs = timeMs
      )
  }

  /** Run find_theorems asynchronously via I/Q MCP to search for relevant
    * theorems.
    *
    * @param view
    *   The current jEdit view
    * @param pattern
    *   The search pattern (should be quoted)
    * @param limit
    *   Maximum number of results to return
    * @param timeoutMs
    *   Timeout in milliseconds
    * @param callback
    *   Callback function to receive results or error
    */
  def runFindTheoremsAsync(
      view: View,
      pattern: String,
      limit: Int,
      timeoutMs: Long,
      callback: Either[String, List[String]] => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callbackOnGui(callback, Left("I/Q unavailable"))
    } else {
      val selectionParams = selectionParamsForView(view)
      val _ = IQOperationLifecycle.forkJvmThread(
        name = "assistant-find-theorems-via-mcp",
        body = () => {
          val result = IQMcpClient
            .callExplore(
              query = "find_theorems",
              arguments = pattern,
              timeoutMs = timeoutMs,
              extraParams = selectionParams + ("max_results" -> limit)
            )
            .fold(
              mcpErr => Left(s"find_theorems via I/Q MCP failed: $mcpErr"),
              explore => {
                if (explore.success)
                  Right(parseFindTheoremsResults(explore.results))
                else if (explore.timedOut) Left("find_theorems timed out")
                else
                  Left(exploreFailureMessage(explore, "find_theorems failed"))
              }
            )
          callbackOnGui(callback, result)
        }
      )
    }
  }

  /** Run an arbitrary I/Q proof query asynchronously via I/Q MCP.
    *
    * @param view
    *   The current jEdit view
    * @param queryArgs
    *   Arguments to pass to isar_explore
    * @param timeoutMs
    *   Timeout in milliseconds
    * @param callback
    *   Callback with Right(output) on completion or Left(error)
    */
  def runQueryAsync(
      view: View,
      queryArgs: List[String],
      timeoutMs: Long,
      callback: Either[String, String] => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callbackOnGui(callback, Left("I/Q unavailable"))
    } else {
      val queryText = queryArgs.map(_.trim).filter(_.nonEmpty).mkString(" ").trim
      if (queryText.isEmpty) callbackOnGui(callback, Left("query arguments required"))
      else {
        val selectionParams = selectionParamsForView(view)
        val _ = IQOperationLifecycle.forkJvmThread(
          name = "assistant-query-via-mcp",
          body = () => {
            val result = IQMcpClient
              .callExplore(
                query = "proof",
                arguments = queryText,
                timeoutMs = timeoutMs,
                extraParams = selectionParams
              )
              .fold(
                mcpErr => Left(s"I/Q MCP query failed: $mcpErr"),
                explore => {
                  if (explore.success) Right(Option(explore.results).getOrElse(""))
                  else if (explore.timedOut) Left("query timed out")
                  else Left(exploreFailureMessage(explore, "query failed"))
                }
              )
            callbackOnGui(callback, result)
          }
        )
      }
    }
  }

  // I/Q Status for dockable header

  /** Status types for I/Q integration. */
  enum IQStatus {

    /** I/Q plugin is connected and available. */
    case IQConnected

    /** I/Q plugin is not available. */
    case IQDisconnected
  }
  export IQStatus._

  /** Get I/Q status for a specific buffer.
    *
    * @param buffer
    *   The jEdit buffer to check
    * @return
    *   Current I/Q status
    */
  def getStatus(@unused buffer: org.gjt.sp.jedit.buffer.JEditBuffer): IQStatus =
    if (IQAvailable.isAvailable) IQConnected else IQDisconnected

  /** Run sledgehammer asynchronously via I/Q MCP. Callback is dispatched on
    * the GUI thread.
    */
  def runSledgehammerAsync(
      view: View,
      timeoutMs: Long,
      callback: Either[String, List[SledgehammerResult]] => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callbackOnGui(callback, Left("I/Q unavailable"))
    } else {
      val selectionParams = selectionParamsForView(view)
      val _ = IQOperationLifecycle.forkJvmThread(
        name = "assistant-sledgehammer-via-mcp",
        body = () => {
          val result = IQMcpClient
            .callExplore(
              query = "sledgehammer",
              arguments = "",
              timeoutMs = timeoutMs,
              extraParams = selectionParams
            )
            .fold(
              mcpErr => Left(s"sledgehammer via I/Q MCP failed: $mcpErr"),
              explore => {
                if (explore.success) Right(parseSledgehammerResults(explore.results))
                else if (explore.timedOut) Left("sledgehammer timed out")
                else Left(exploreFailureMessage(explore, "sledgehammer failed"))
              }
            )
          callbackOnGui(callback, result)
        }
      )
    }
  }
}
