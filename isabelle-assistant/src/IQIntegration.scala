/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer

/**
 * Integration layer for I/Q (Isabelle/Q) plugin functionality.
 * 
 * Provides asynchronous proof verification, sledgehammer integration,
 * and theorem finding capabilities when I/Q plugin is available.
 * All operations are designed to be non-blocking and provide proper
 * error handling and timeout management.
 * 
 * Common pattern abstracted via runIQOperationAsync: create operation,
 * set up callbacks, activate, handle timeout, and deactivate.
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

  /**
   * Result from sledgehammer proof search.
   * 
   * @param proofMethod The proof method found by sledgehammer
   * @param timeMs Time taken to find the proof in milliseconds
   */
  case class SledgehammerResult(proofMethod: String, timeMs: Long)

  /**
   * Structured result from executing a proof step via isar_explore.
   * Unlike VerificationResult, this carries the resulting proof state for chaining.
   */
  case class ProofStepResult(
    complete: Boolean,
    numSubgoals: Int,
    stateText: String,
    timeMs: Long
  )

  /**
   * Get suggestion text for importing Isar_Explore.
   * 
   * @return Import suggestion message
   */
  def getIsarExploreImportSuggestion: String =
    """To use proof verification, import Isar_Explore from the I/Q plugin:
  imports ... "$IQ_HOME/Isar_Explore"
Replace $IQ_HOME with the path to your I/Q plugin installation."""

  /**
   * Verify a proof asynchronously. Calls the callback with the result.
   * MUST be called from the GUI thread.
   * 
   * @param view The current jEdit view
   * @param command The Isabelle command to verify against
   * @param proofText The proof text to verify
   * @param timeoutMs Timeout in milliseconds
   * @param callback Callback function to receive the result
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
          val completionLock = new Object()
          @volatile var completed = false
          @volatile var timeoutThread: Thread = null

          def completeOperation(newResult: VerificationResult): Unit = {
            completionLock.synchronized {
              if (!completed) {
                completed = true
                VerificationCache.put(command, proofText, newResult)
                callback(newResult)
                // Always interrupt timeout thread on any completion path
                Option(timeoutThread).foreach(_.interrupt())
              }
            }
          }

          val operation = new Extended_Query_Operation(
            PIDE.editor, view, AssistantConstants.IQ_OPERATION_ISAR_EXPLORE,
            status => {
              if (status == Extended_Query_Operation.Status.finished ||
                  status == Extended_Query_Operation.Status.failed) {
                val elapsed = System.currentTimeMillis() - startTime
                if (status == Extended_Query_Operation.Status.failed)
                  completeOperation(ProofFailure("Verification unavailable (import iq.Isar_Explore to enable)"))
                else
                  completeOperation(ProofSuccess(elapsed))
              }
            },
            (snapshot, cmdResults, output) => {
              completionLock.synchronized {
                if (!completed) {
                  // Check for errors by XML markup, not text content heuristics
                  val errors = output.filter(e => e.name == Markup.ERROR_MESSAGE || e.name == Markup.ERROR)
                  if (errors.nonEmpty) {
                    val errorMsg = errors.map(e => XML.content(e).trim).mkString("\n").take(100)
                    completeOperation(ProofFailure(if (errorMsg.nonEmpty) errorMsg else "proof method failed"))
                  } else {
                    val text = output.map(XML.content(_).trim).filter(_.nonEmpty).mkString("\n")
                    if (text.nonEmpty) {
                      completeOperation(ProofSuccess(System.currentTimeMillis() - startTime, text))
                    }
                  }
                }
              }
            }
          )

          operation.activate()
          operation.apply_query_at_command(command, List(proofText))

          timeoutThread = Isabelle_Thread.fork(name = "verify-timeout") {
            try {
              Thread.sleep(timeoutMs)
              completeOperation(ProofTimeout)
              GUI_Thread.later { operation.deactivate() }
            } catch { case _: InterruptedException => /* early completion, thread exits cleanly */ }
          }
      }
    }
  }

  /**
   * Execute a proof step and return the resulting proof state.
   * Parses the PROOF_COMPLETE/PROOF_STATE header from isar_explore.
   * MUST be called from the GUI thread.
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
    val completionLock = new Object()
    @volatile var completed = false
    @volatile var timeoutThread: Thread = null

    def complete(result: Either[String, ProofStepResult]): Unit = {
      completionLock.synchronized {
        if (!completed) {
          completed = true
          callback(result)
          val tt = timeoutThread
          if (tt != null) tt.interrupt()
        }
      }
    }

    val operation = new Extended_Query_Operation(
      PIDE.editor, view, AssistantConstants.IQ_OPERATION_ISAR_EXPLORE,
      status => {
        if (status == Extended_Query_Operation.Status.failed)
          complete(Left("Verification unavailable (import iq.Isar_Explore to enable)"))
        // Do NOT complete on finished — wait for output callback
      },
      (snapshot, cmdResults, output) => {
        completionLock.synchronized {
          if (!completed) {
            val errors = output.filter(e => e.name == Markup.ERROR_MESSAGE || e.name == Markup.ERROR)
            if (errors.nonEmpty) {
              val errorMsg = errors.map(e => XML.content(e).trim).mkString("\n").take(200)
              complete(Left(if (errorMsg.nonEmpty) errorMsg else "proof method failed"))
            } else {
              val text = output.map(XML.content(_).trim).filter(_.nonEmpty).mkString("\n")
              if (text.nonEmpty) {
                val elapsed = System.currentTimeMillis() - startTime
                complete(Right(parseStepResult(text, elapsed)))
              }
            }
          }
        }
      }
    )

    operation.activate()
    operation.apply_query_at_command(command, List(proofText))

    timeoutThread = Isabelle_Thread.fork(name = "step-timeout") {
      try {
        Thread.sleep(timeoutMs)
        complete(Left("timeout"))
        GUI_Thread.later { operation.deactivate() }
      } catch { case _: InterruptedException => }
    }
  }

  /** Parse the PROOF_COMPLETE/PROOF_STATE header from isar_explore output. */
  private[assistant] def parseStepResult(text: String, timeMs: Long): ProofStepResult = {
    val lines = text.linesIterator
    if (!lines.hasNext) return ProofStepResult(complete = true, numSubgoals = 0, stateText = "", timeMs = timeMs)
    val header = lines.next()
    val rest = if (lines.hasNext) lines.mkString("\n") else ""
    if (header.startsWith("PROOF_COMPLETE"))
      ProofStepResult(complete = true, numSubgoals = 0, stateText = rest, timeMs = timeMs)
    else if (header.startsWith("PROOF_STATE ")) {
      val n = try { header.stripPrefix("PROOF_STATE ").trim.toInt } catch { case _: NumberFormatException => -1 }
      ProofStepResult(complete = false, numSubgoals = n, stateText = rest, timeMs = timeMs)
    } else
      // Legacy format without header — treat as opaque state
      ProofStepResult(complete = false, numSubgoals = -1, stateText = text, timeMs = timeMs)
  }

  /**
   * Run find_theorems asynchronously to search for relevant theorems.
   * 
   * @param view The current jEdit view
   * @param command The Isabelle command context for the search
   * @param pattern The search pattern (should be quoted)
   * @param limit Maximum number of results to return
   * @param timeoutMs Timeout in milliseconds
   * @param callback Callback function to receive results or error
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

    val completionLock = new Object()
    @volatile var completed = false
    val results = scala.collection.mutable.ListBuffer[String]()

    def completeWith(result: Either[String, List[String]]): Unit = {
      completionLock.synchronized {
        if (!completed) {
          completed = true
          callback(result)
        }
      }
    }

    val operation = new Extended_Query_Operation(
      PIDE.editor, view, AssistantConstants.IQ_OPERATION_FIND_THEOREMS,
      status => {
        if (status == Extended_Query_Operation.Status.finished ||
            status == Extended_Query_Operation.Status.failed) {
          completeWith(Right(results.synchronized { results.toList }))
        }
      },
      (snapshot, cmdResults, output) => {
        completionLock.synchronized {
          if (!completed) {
            // Parse theorem results - format is typically "theorem_name: statement"
            val text = output.map(XML.content(_)).mkString("\n")
            results.synchronized {
              for (line <- text.linesIterator if line.contains(":") && !line.startsWith("found") &&
                   !line.contains("error") && !line.contains("Outer syntax") && !line.contains("bad input")) {
                results += line.trim
              }
            }
          }
        }
      }
    )

    operation.activate()
    // find_theorems args: limit, allow_dups, query
    operation.apply_query_at_command(command, List(limit.toString, "false", pattern))

    Isabelle_Thread.fork(name = "find-theorems-timeout") {
      try {
        Thread.sleep(timeoutMs)
        completeWith(Right(results.synchronized { results.toList }))
        GUI_Thread.later { operation.deactivate() }
      } catch { case _: InterruptedException => /* early completion */ }
    }
    }
  }

  /**
   * Run an arbitrary I/Q query asynchronously with timeout.
   * MUST be called from the GUI thread.
   *
   * @param view The current jEdit view
   * @param command The Isabelle command context
   * @param queryArgs Arguments to pass to isar_explore
   * @param timeoutMs Timeout in milliseconds
   * @param callback Callback with Right(output) on completion or Left(error)
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

    val completionLock = new Object()
    @volatile var completed = false
    val output = new StringBuilder

    def completeWith(result: Either[String, String]): Unit = {
      completionLock.synchronized {
        if (!completed) {
          completed = true
          callback(result)
        }
      }
    }

    val operation = new Extended_Query_Operation(
      PIDE.editor, view, AssistantConstants.IQ_OPERATION_ISAR_EXPLORE,
      status => {
        if (status == Extended_Query_Operation.Status.finished ||
            status == Extended_Query_Operation.Status.failed) {
          completeWith(Right(output.synchronized { output.toString }))
        }
      },
      (snapshot, cmdResults, results) => {
        completionLock.synchronized {
          if (!completed) {
            val text = results.map(XML.content(_)).mkString("\n")
            if (text.nonEmpty) output.synchronized { output.append(text).append("\n") }
          }
        }
      }
    )

    operation.activate()
    operation.apply_query_at_command(command, queryArgs)

    Isabelle_Thread.fork(name = "iq-query-timeout") {
      try {
        Thread.sleep(timeoutMs)
        completeWith(Right(output.synchronized { output.toString }))
        GUI_Thread.later { operation.deactivate() }
      } catch { case _: InterruptedException => /* early completion */ }
    }
    }
  }

  /**
   * Abstract the common Extended_Query_Operation pattern to reduce code repetition.
   * Handles: availability check, completion lock, timeout thread, operation lifecycle.
   * 
   * @param view jEdit view for the operation
   * @param operationName Name of the I/Q operation (e.g., "isar_explore")
   * @param queryArgs Arguments to pass to the query
   * @param timeoutMs Timeout in milliseconds
   * @param onStatusChange Callback when operation status changes
   * @param onResults Callback when results arrive (called multiple times potentially)
   * @param callback Final callback with aggregated result
   * @tparam T Type of the aggregated result
   */
  private def runIQOperationAsync[T](
    view: View,
    command: Command,
    operationName: String,
    queryArgs: List[String],
    timeoutMs: Long,
    onStatusChange: Extended_Query_Operation.Status => Option[T],
    onResults: List[XML.Tree] => Unit,
    callback: Either[String, T] => Unit
  ): Unit = {
    if (!IQAvailable.isAvailable) {
      callback(Left("I/Q unavailable"))
      return
    }

    val completionLock = new Object()
    @volatile var completed = false
    @volatile var timeoutThread: Thread = null

    def completeWith(result: Either[String, T]): Unit = {
      completionLock.synchronized {
        if (!completed) {
          completed = true
          callback(result)
          val tt = timeoutThread
          if (tt != null) tt.interrupt()
        }
      }
    }

    val operation = new Extended_Query_Operation(
      PIDE.editor, view, operationName,
      status => {
        completionLock.synchronized {
          if (!completed) {
            onStatusChange(status).foreach(result => completeWith(Right(result)))
          }
        }
      },
      (snapshot, cmdResults, output) => {
        completionLock.synchronized {
          if (!completed) {
            onResults(output)
          }
        }
      }
    )

    operation.activate()
    operation.apply_query_at_command(command, queryArgs)

    timeoutThread = Isabelle_Thread.fork(name = s"$operationName-timeout") {
      try {
        Thread.sleep(timeoutMs)
        GUI_Thread.later { operation.deactivate() }
      } catch { case _: InterruptedException => /* early completion */ }
    }
  }

  /**
   * Get the Isabelle command at a specific buffer offset.
   * 
   * @param buffer The jEdit buffer
   * @param offset The character offset in the buffer
   * @return Some(Command) if found, None otherwise
   */
  def getCommandAtOffset(buffer: JEditBuffer, offset: Int): Option[Command] = {
    try {
      Document_Model.get_model(buffer).flatMap { model =>
        val snapshot = Document_Model.snapshot(model)
        val node = snapshot.get_node(model.node_name)
        if (node.commands.isEmpty) None
        else node.command_iterator(Text.Range(offset, offset + 1)).toList.headOption.map(_._1)
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

  /**
   * Get I/Q status for a specific buffer.
   * 
   * @param buffer The jEdit buffer to check
   * @return Current I/Q status
   */
  def getStatus(buffer: JEditBuffer): IQStatus =
    if (IQAvailable.isAvailable) IQConnected else IQDisconnected

  /**
   * Run sledgehammer asynchronously. Calls the callback with results.
   * MUST be called from the GUI thread.
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
    val completionLock = new Object()
    @volatile var completed = false
    val results = scala.collection.mutable.ListBuffer[SledgehammerResult]()

    // Pattern to match sledgehammer output: "Try this: by simp (0.5 ms)"
    val tryThisPattern = """Try this:\s*(.+?)\s*\((\d+(?:\.\d+)?)\s*(ms|s)\)""".r

    def completeWith(result: Either[String, List[SledgehammerResult]]): Unit = {
      completionLock.synchronized {
        if (!completed) {
          completed = true
          callback(result)
        }
      }
    }

    val operation = new Extended_Query_Operation(
      PIDE.editor, view, AssistantConstants.IQ_OPERATION_ISAR_EXPLORE,
      status => {
        if (status == Extended_Query_Operation.Status.finished ||
            status == Extended_Query_Operation.Status.failed) {
          completeWith(Right(results.synchronized { results.toList }))
        }
      },
      (snapshot, cmdResults, output) => {
        completionLock.synchronized {
          if (!completed) {
            val text = output.map(XML.content(_)).mkString("\n")
            results.synchronized {
              for (m <- tryThisPattern.findAllMatchIn(text)) {
                val method = m.group(1).trim
                val timeVal = m.group(2).toDouble
                val unit = m.group(3)
                val timeMs = if (unit == "s") (timeVal * 1000).toLong else timeVal.toLong
                results += SledgehammerResult(method, timeMs)
              }
            }
          }
        }
      }
    )

    operation.activate()
    operation.apply_query_at_command(command, List("sledgehammer"))

    // Timeout check
    Isabelle_Thread.fork(name = "sledgehammer-timeout") {
      try {
        Thread.sleep(timeoutMs)
        completeWith(Right(results.synchronized { results.toList }))
        GUI_Thread.later { operation.deactivate() }
      } catch { case _: InterruptedException => /* early completion */ }
    }
    }
  }
}
