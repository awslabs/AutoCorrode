/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer

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
      numSubgoals: Int,
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

  /** Verify a proof asynchronously. Calls the callback with the result. MUST be
    * called from the GUI thread.
    *
    * @param view
    *   The current jEdit view
    * @param command
    *   The Isabelle command to verify against
    * @param proofText
    *   The proof text to verify
    * @param timeoutMs
    *   Timeout in milliseconds
    * @param callback
    *   Callback function to receive the result
    */
  def verifyProofAsync(
      view: View,
      command: Command,
      proofText: String,
      timeoutMs: Long,
      callback: VerificationResult => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callback(IQUnavailable)
    } else {
      // Check cache first
      VerificationCache.get(command, proofText) match {
        case Some(cachedResult) =>
          callback(cachedResult)
        case None =>
          val startTime = System.currentTimeMillis()
          val outputLock = new Object()
          @volatile var receivedOutput = false
          var operation: Extended_Query_Operation = null
          val lifecycle = new IQOperationLifecycle[VerificationResult](
            onComplete = newResult => {
              VerificationCache.put(command, proofText, newResult)
              callback(newResult)
            },
            deactivate = () => Option(operation).foreach(_.deactivate())
          )

          operation = new Extended_Query_Operation(
            PIDE.editor,
            view,
            AssistantConstants.IQ_OPERATION_ISAR_EXPLORE,
            status => {
              if (status == Extended_Query_Operation.Status.failed) {
                lifecycle.complete(
                  ProofFailure(
                    "Verification unavailable (import iq.Isar_Explore to enable)"
                  )
                )
              } else if (status == Extended_Query_Operation.Status.finished) {
                // Don't immediately report success — wait to see if we received valid output.
                // Schedule a 500ms grace period callback instead of blocking a thread.
                val p = scala.concurrent.Promise[Unit]()
                TimeoutGuard.scheduleTimeout(p, 500L, "Grace period elapsed")
                import scala.concurrent.ExecutionContext.Implicits.global
                p.future.recover { case _ =>
                  outputLock.synchronized {
                    if (!lifecycle.isCompleted && !receivedOutput) {
                      lifecycle.complete(
                        ProofFailure(
                          "proof method did not produce a result (may not have terminated)"
                        )
                      )
                    }
                  }
                }
              }
            },
            (snapshot, cmdResults, output) => {
              outputLock.synchronized {
                if (!lifecycle.isCompleted) {
                  // Check for errors by XML markup, not text content heuristics
                  val errors = output.filter(e =>
                    e.name == Markup.ERROR_MESSAGE || e.name == Markup.ERROR
                  )
                  if (errors.nonEmpty) {
                    val errorMsg = errors
                      .map(e => XML.content(e).trim)
                      .mkString("\n")
                      .take(100)
                    lifecycle.complete(
                      ProofFailure(
                        if (errorMsg.nonEmpty) errorMsg
                        else "proof method failed"
                      )
                    )
                  } else {
                    val text = output
                      .map(XML.content(_).trim)
                      .filter(_.nonEmpty)
                      .mkString("\n")
                    if (text.nonEmpty) {
                      receivedOutput = true
                      lifecycle.complete(
                        ProofSuccess(
                          System.currentTimeMillis() - startTime,
                          text
                        )
                      )
                    }
                  }
                }
              }
            }
          )

          lifecycle.forkTimeout(name = "verify-timeout", timeoutMs = timeoutMs)(
            ProofTimeout
          )

          try {
            operation.activate()
            operation.apply_query_at_command(command, List(proofText))
          } catch {
            case ex: Exception =>
              lifecycle.complete(
                ProofFailure(s"verification setup failed: ${ex.getMessage}")
              )
          }
      }
    }
  }

  /** Execute a proof step and return the resulting proof state. Parses the
    * PROOF_COMPLETE/PROOF_STATE header from isar_explore. MUST be called from
    * the GUI thread.
    */
  def executeStepAsync(
      view: View,
      command: Command,
      proofText: String,
      timeoutMs: Long,
      callback: Either[String, ProofStepResult] => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) { callback(Left("I/Q unavailable")); return }

    val startTime = System.currentTimeMillis()
    val outputLock = new Object()
    var operation: Extended_Query_Operation = null
    val lifecycle = new IQOperationLifecycle[Either[String, ProofStepResult]](
      onComplete = callback,
      deactivate = () => Option(operation).foreach(_.deactivate())
    )

    operation = new Extended_Query_Operation(
      PIDE.editor,
      view,
      AssistantConstants.IQ_OPERATION_ISAR_EXPLORE,
      status => {
        if (status == Extended_Query_Operation.Status.failed)
          lifecycle.complete(
            Left("Verification unavailable (import iq.Isar_Explore to enable)")
          )
        // Do NOT complete on finished — wait for output callback
      },
      (snapshot, cmdResults, output) => {
        outputLock.synchronized {
          if (!lifecycle.isCompleted) {
            val errors = output.filter(e =>
              e.name == Markup.ERROR_MESSAGE || e.name == Markup.ERROR
            )
            if (errors.nonEmpty) {
              val errorMsg =
                errors.map(e => XML.content(e).trim).mkString("\n").take(200)
              lifecycle.complete(
                Left(if (errorMsg.nonEmpty) errorMsg else "proof method failed")
              )
            } else {
              val text = output
                .map(XML.content(_).trim)
                .filter(_.nonEmpty)
                .mkString("\n")
              if (text.nonEmpty) {
                val elapsed = System.currentTimeMillis() - startTime
                lifecycle.complete(Right(parseStepResult(text, elapsed)))
              }
            }
          }
        }
      }
    )

    lifecycle.forkTimeout(name = "step-timeout", timeoutMs = timeoutMs)(
      Left("timeout")
    )

    try {
      operation.activate()
      operation.apply_query_at_command(command, List(proofText))
    } catch {
      case ex: Exception =>
        lifecycle.complete(Left(s"verification setup failed: ${ex.getMessage}"))
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
        numSubgoals = 0,
        stateText = "",
        timeMs = timeMs
      )
    val header = lines.next()
    val rest = if (lines.hasNext) lines.mkString("\n") else ""
    if (header.startsWith("PROOF_COMPLETE"))
      ProofStepResult(
        complete = true,
        numSubgoals = 0,
        stateText = rest,
        timeMs = timeMs
      )
    else if (header.startsWith("PROOF_STATE ")) {
      val n = try { header.stripPrefix("PROOF_STATE ").trim.toInt }
      catch { case _: NumberFormatException => -1 }
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
        numSubgoals = -1,
        stateText = text,
        timeMs = timeMs
      )
  }

  /** Run find_theorems asynchronously to search for relevant theorems.
    *
    * @param view
    *   The current jEdit view
    * @param command
    *   The Isabelle command context for the search
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
      command: Command,
      pattern: String,
      limit: Int,
      timeoutMs: Long,
      callback: Either[String, List[String]] => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callback(Left("I/Q unavailable"))
    } else {

      val outputLock = new Object()
      val results = scala.collection.mutable.ListBuffer[String]()
      var operation: Extended_Query_Operation = null
      val lifecycle = new IQOperationLifecycle[Either[String, List[String]]](
        onComplete = callback,
        deactivate = () => Option(operation).foreach(_.deactivate())
      )

      operation = new Extended_Query_Operation(
        PIDE.editor,
        view,
        AssistantConstants.IQ_OPERATION_FIND_THEOREMS,
        status => {
          if (
            status == Extended_Query_Operation.Status.finished ||
            status == Extended_Query_Operation.Status.failed
          ) {
            lifecycle.complete(Right(results.synchronized { results.toList }))
          }
        },
        (snapshot, cmdResults, output) => {
          outputLock.synchronized {
            if (!lifecycle.isCompleted) {
              // Parse theorem results - format is typically "theorem_name: statement"
              val text = output.map(XML.content(_)).mkString("\n")
              results.synchronized {
                for (
                  line <- text.linesIterator
                  if line.contains(":") && !line.startsWith("found") &&
                    !line.contains("error") && !line
                      .contains("Outer syntax") && !line.contains("bad input")
                ) {
                  results += line.trim
                }
              }
            }
          }
        }
      )

      lifecycle.forkTimeout(
        name = "find-theorems-timeout",
        timeoutMs = timeoutMs
      ) {
        Right(results.synchronized { results.toList })
      }

      try {
        operation.activate()
        // find_theorems args: limit, allow_dups, query
        operation.apply_query_at_command(
          command,
          List(limit.toString, "false", pattern)
        )
      } catch {
        case ex: Exception =>
          lifecycle.complete(
            Left(s"find_theorems setup failed: ${ex.getMessage}")
          )
      }
    }
  }

  /** Run an arbitrary I/Q query asynchronously with timeout. MUST be called
    * from the GUI thread.
    *
    * @param view
    *   The current jEdit view
    * @param command
    *   The Isabelle command context
    * @param queryArgs
    *   Arguments to pass to isar_explore
    * @param timeoutMs
    *   Timeout in milliseconds
    * @param callback
    *   Callback with Right(output) on completion or Left(error)
    */
  def runQueryAsync(
      view: View,
      command: Command,
      queryArgs: List[String],
      timeoutMs: Long,
      callback: Either[String, String] => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callback(Left("I/Q unavailable"))
    } else {

      val outputLock = new Object()
      val output = new StringBuilder
      var operation: Extended_Query_Operation = null
      val lifecycle = new IQOperationLifecycle[Either[String, String]](
        onComplete = callback,
        deactivate = () => Option(operation).foreach(_.deactivate())
      )

      operation = new Extended_Query_Operation(
        PIDE.editor,
        view,
        AssistantConstants.IQ_OPERATION_ISAR_EXPLORE,
        status => {
          if (
            status == Extended_Query_Operation.Status.finished ||
            status == Extended_Query_Operation.Status.failed
          ) {
            lifecycle.complete(Right(output.synchronized { output.toString }))
          }
        },
        (snapshot, cmdResults, results) => {
          outputLock.synchronized {
            if (!lifecycle.isCompleted) {
              val text = results.map(XML.content(_)).mkString("\n")
              if (text.nonEmpty) output.synchronized {
                output.append(text).append("\n")
              }
            }
          }
        }
      )

      lifecycle.forkTimeout(name = "iq-query-timeout", timeoutMs = timeoutMs) {
        Right(output.synchronized { output.toString })
      }

      try {
        operation.activate()
        operation.apply_query_at_command(command, queryArgs)
      } catch {
        case ex: Exception =>
          lifecycle.complete(Left(s"query setup failed: ${ex.getMessage}"))
      }
    }
  }

  /** Get the Isabelle command at a specific buffer offset.
    *
    * @param buffer
    *   The jEdit buffer
    * @param offset
    *   The character offset in the buffer
    * @return
    *   Some(Command) if found, None otherwise
    */
  def getCommandAtOffset(buffer: JEditBuffer, offset: Int): Option[Command] = {
    try {
      Document_Model.get_model(buffer).flatMap { model =>
        val snapshot = Document_Model.snapshot(model)
        val node = snapshot.get_node(model.node_name)
        if (node.commands.isEmpty) None
        else
          node
            .command_iterator(Text.Range(offset, offset + 1))
            .toList
            .headOption
            .map(_._1)
      }
    } catch { case _: Exception => None }
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
  def getStatus(buffer: JEditBuffer): IQStatus =
    if (IQAvailable.isAvailable) IQConnected else IQDisconnected

  /** Run sledgehammer asynchronously. Calls the callback with results. MUST be
    * called from the GUI thread.
    */
  def runSledgehammerAsync(
      view: View,
      command: Command,
      timeoutMs: Long,
      callback: Either[String, List[SledgehammerResult]] => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callback(Left("I/Q unavailable"))
    } else {

      val startTime = System.currentTimeMillis()
      val outputLock = new Object()
      val results = scala.collection.mutable.ListBuffer[SledgehammerResult]()

      // Pattern to match sledgehammer output: "Try this: by simp (0.5 ms)"
      val tryThisPattern =
        """Try this:\s*(.+?)\s*\((\d+(?:\.\d+)?)\s*(ms|s)\)""".r

      var operation: Extended_Query_Operation = null
      val lifecycle =
        new IQOperationLifecycle[Either[String, List[SledgehammerResult]]](
          onComplete = callback,
          deactivate = () => Option(operation).foreach(_.deactivate())
        )

      operation = new Extended_Query_Operation(
        PIDE.editor,
        view,
        AssistantConstants.IQ_OPERATION_ISAR_EXPLORE,
        status => {
          if (
            status == Extended_Query_Operation.Status.finished ||
            status == Extended_Query_Operation.Status.failed
          ) {
            lifecycle.complete(Right(results.synchronized { results.toList }))
          }
        },
        (snapshot, cmdResults, output) => {
          outputLock.synchronized {
            if (!lifecycle.isCompleted) {
              val text = output.map(XML.content(_)).mkString("\n")
              results.synchronized {
                for (m <- tryThisPattern.findAllMatchIn(text)) {
                  val method = m.group(1).trim
                  val timeVal = m.group(2).toDouble
                  val unit = m.group(3)
                  val timeMs =
                    if (unit == "s") (timeVal * 1000).toLong else timeVal.toLong
                  results += SledgehammerResult(method, timeMs)
                }
              }
            }
          }
        }
      )

      lifecycle.forkTimeout(
        name = "sledgehammer-timeout",
        timeoutMs = timeoutMs
      ) {
        Right(results.synchronized { results.toList })
      }

      try {
        operation.activate()
        operation.apply_query_at_command(command, List("sledgehammer"))
      } catch {
        case ex: Exception =>
          lifecycle.complete(
            Left(s"sledgehammer setup failed: ${ex.getMessage}")
          )
      }
    }
  }
}
