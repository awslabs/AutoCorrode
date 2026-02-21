/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import scala.util.{Try, Failure}
import java.util.concurrent.atomic.AtomicReference
import scala.util.control.NonFatal

/** Unified error handling, input validation, resource management, and operation
  * logging for Isabelle Assistant.
  *
  * Provides:
  *   - User-friendly error message translation
  *   - Input validation and sanitization
  *   - Operation timing/logging
  *   - Standardized Try-based error handling with optional post-hoc timeout
  *     check
  *   - AutoCloseable resource registry with automatic cleanup
  */
object ErrorHandler {

  // --- Input validation ---

  /** Validate user input: reject null/empty, but do NOT truncate. Use
    * `sanitize` if truncation is desired.
    */
  def validateInput(input: String): Try[String] = {
    if (input == null)
      Failure(new IllegalArgumentException("Input cannot be null"))
    else if (input.trim.isEmpty)
      Failure(new IllegalArgumentException("Input cannot be empty"))
    else scala.util.Success(input.trim)
  }

  /** Truncate a string to `maxLength`, appending "..." if truncated. */
  def sanitize(
      input: String,
      maxLength: Int = AssistantConstants.MAX_RESPONSE_LENGTH
  ): String =
    if (input == null) ""
    else if (input.length > maxLength) input.take(maxLength)
    else input

  // --- Error message translation ---

  /** Convert technical error messages to user-friendly ones. */
  def makeUserFriendly(message: String, operation: String): String = {
    if (message == null || message.trim.isEmpty) s"Unknown error in $operation"
    else {
      val msg = message.toLowerCase
      if (msg.contains("timeout") || msg.contains("timed out"))
        "Operation timed out. Try again, increase the timeout via :set verify_timeout <ms>, or check your network."
      else if (
        msg.contains("network") || msg
          .contains("connection") || msg.contains("unreachable")
      )
        "Network connection failed. Check your internet connection and verify ~/.aws/credentials or AWS_ACCESS_KEY_ID is set."
      else if (
        msg.contains("credentials") || msg.contains("unauthorized") || msg
          .contains("access denied")
      )
        "AWS credentials are invalid or insufficient. Check ~/.aws/credentials, environment variables (AWS_ACCESS_KEY_ID, AWS_SECRET_ACCESS_KEY), or IAM role permissions."
      else if (msg.contains("model") && msg.contains("not found"))
        "The selected AI model is not available. Run :models to see available models, then :set model <id> to choose one."
      else if (
        msg.contains("quota") || msg.contains("throttle") || msg.contains(
          "rate limit"
        ) || msg.contains("too many requests")
      )
        "AWS service limit reached. Wait a moment and try again, or request a quota increase in the AWS console."
      else if (msg.contains("json") || msg.contains("parse"))
        "Received invalid response from AI service. Please try again."
      else truncateError(message)
    }
  }

  /** Truncate error messages to prevent UI overflow. */
  def truncateError(error: String): String = {
    if (error == null) "Unknown error"
    else if (error.length > AssistantConstants.MAX_ERROR_MESSAGE_LENGTH)
      error.take(AssistantConstants.MAX_ERROR_MESSAGE_LENGTH) + "..."
    else error
  }

  // --- Operation logging ---

  /** Log an exception that would otherwise be silently swallowed. */
  def logSilentError(component: String, ex: Throwable): Unit = {
    safeErrorMessage(s"[$component] Unexpected error: ${ex.getMessage}")
    ex.printStackTrace(System.err)
  }

  /** Safe wrapper for Output.writeln — no-op if Isabelle runtime isn't
    * available.
    */
  private def safeWriteln(msg: String): Unit =
    try { Output.writeln(msg) }
    catch {
      case NonFatal(_) | _: LinkageError => System.err.println(msg)
    }

  /** Safe wrapper for Output.error_message — no-op if Isabelle runtime isn't
    * available.
    */
  private def safeErrorMessage(msg: String): Unit =
    try { Output.error_message(msg) }
    catch {
      case NonFatal(_) | _: LinkageError => System.err.println(s"ERROR: $msg")
    }

  /** Log operation with timing information. Re-throws with user-friendly
    * message on failure.
    */
  def logOperation[T](operation: String)(block: => T): T = {
    val startTime = System.currentTimeMillis()
    try {
      val result = block
      val elapsed = System.currentTimeMillis() - startTime
      safeWriteln(s"[Assistant] $operation completed in ${elapsed}ms")
      result
    } catch {
      case ex: Exception =>
        val elapsed = System.currentTimeMillis() - startTime
        val userMessage = makeUserFriendly(ex.getMessage, operation)
        safeErrorMessage(
          s"[Assistant] $operation failed after ${elapsed}ms: $userMessage"
        )
        throw new RuntimeException(userMessage, ex)
    }
  }

  // --- Standardized error handling (formerly StandardErrorHandler) ---

  private val resourceRegistry = new AtomicReference[List[AutoCloseable]](Nil)
  private val maxRegistrySize = 50

  /** Register a resource for automatic cleanup on plugin stop. Oldest entries
    * are closed and dropped when the registry exceeds capacity.
    */
  def registerResource(resource: AutoCloseable): Unit = {
    // Collect overflow outside the atomic update to avoid side effects in the lambda
    var toClose: List[AutoCloseable] = Nil
    resourceRegistry.updateAndGet { list =>
      val updated = resource :: list
      if (updated.length > maxRegistrySize) {
        toClose = updated.drop(maxRegistrySize)
        updated.take(maxRegistrySize)
      } else updated
    }
    toClose.foreach { r =>
      try { r.close() }
      catch { case NonFatal(_) => }
    }
  }

  /** Clean up all registered resources. */
  def cleanupAll(): Unit = {
    val resources = resourceRegistry.getAndSet(Nil)
    resources.foreach { resource =>
      try { resource.close() }
      catch { case NonFatal(_) => }
    }
  }

  /** Execute operation with standardized error handling.
    *
    * The optional `elapsedLimitMs` performs a **post-hoc** elapsed-time check
    * after the block returns — it does NOT interrupt the block. Use a
    * `CountDownLatch.await` or similar for true preemptive timeouts.
    */
  def withErrorHandling[T](
      operation: String,
      elapsedLimitMs: Option[Long] = None
  )(block: => T): Try[T] = {
    val startTime = System.currentTimeMillis()
    Try {
      val result = block
      elapsedLimitMs.foreach { limit =>
        val elapsed = System.currentTimeMillis() - startTime
        if (elapsed > limit)
          throw new RuntimeException(
            s"$operation exceeded elapsed limit after ${elapsed}ms (limit: ${limit}ms)"
          )
      }
      result
    }.recoverWith {
      case ex: java.util.concurrent.TimeoutException =>
        val msg =
          s"$operation timed out. Try reducing complexity or check connection."
        safeErrorMessage(s"Timeout in $operation: $msg")
        Failure(new RuntimeException(msg, ex))
      case ex: java.net.ConnectException =>
        val msg =
          s"Cannot connect to service. Check internet connection and credentials."
        safeErrorMessage(s"Connection error in $operation: $msg")
        Failure(new RuntimeException(msg, ex))
      case ex: Exception =>
        val msg = makeUserFriendly(ex.getMessage, operation)
        safeErrorMessage(s"Error in $operation: $msg")
        Failure(new RuntimeException(msg, ex))
    }
  }

  /** Safe resource management with automatic cleanup after use. The resource is
    * closed immediately when the block completes (or throws).
    */
  def withManagedResource[R <: AutoCloseable, T](
      resource: => R
  )(block: R => T): Try[T] = {
    var res: Option[R] = None
    val result = Try {
      val acquired = resource
      res = Some(acquired)
      block(acquired)
    }.recoverWith { case ex: Exception =>
      val msg = makeUserFriendly(ex.getMessage, "resource operation")
      safeErrorMessage(s"Resource operation failed: $msg")
      Failure(new RuntimeException(msg, ex))
    }
    res.foreach { r =>
      try { r.close() }
      catch { case NonFatal(_) => }
    }
    result
  }
}
