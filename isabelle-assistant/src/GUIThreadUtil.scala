/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import java.util.concurrent.{CountDownLatch, TimeUnit}

/**
 * Utility for coordinating work between background threads and the GUI thread.
 * 
 * Isabelle Assistant operates across three thread contexts:
 * - GUI Thread (Swing EDT): All UI updates, jEdit API calls, I/Q operations
 * - Isabelle_Thread: Background work (LLM calls, waiting on latches)
 * - I/Q Callbacks: May arrive on either thread
 * 
 * This utility encapsulates the common pattern of dispatching work to the GUI
 * thread and waiting for the result on a background thread.
 */
object GUIThreadUtil {

  /**
   * Execute a block on the GUI thread and wait for the result.
   * 
   * MUST be called from a background thread (not the GUI thread itself).
   * Times out after the specified duration, returning None.
   * 
   * @param timeoutMs Maximum time to wait in milliseconds
   * @param block The code to execute on the GUI thread
   * @return Some(result) on success, None on timeout
   * @throws RuntimeException if block throws an exception
   */
  def awaitOnGUIThread[T](timeoutMs: Long)(block: => T): Option[T] = {
    val latch = new CountDownLatch(1)
    @volatile var result: Option[T] = None
    @volatile var exception: Option[Throwable] = None
    
    GUI_Thread.later {
      try {
        result = Some(block)
      } catch {
        case ex: Throwable => exception = Some(ex)
      } finally {
        latch.countDown()
      }
    }
    
    if (latch.await(timeoutMs, TimeUnit.MILLISECONDS)) {
      exception.foreach(ex => throw new RuntimeException(s"GUI thread operation failed: ${ex.getMessage}", ex))
      result
    } else {
      None
    }
  }

  /**
   * Execute a block on the GUI thread and wait for the result.
   * Throws an exception on timeout instead of returning None.
   * 
   * @param timeoutMs Maximum time to wait in milliseconds
   * @param operation Description for error message
   * @param block The code to execute
   * @return The result from the block
   * @throws RuntimeException on timeout or if block throws
   */
  def requireOnGUIThread[T](timeoutMs: Long, operation: String)(block: => T): T = {
    awaitOnGUIThread(timeoutMs)(block).getOrElse {
      throw new RuntimeException(s"$operation timed out after ${timeoutMs}ms")
    }
  }

  /**
   * Execute a callback-based I/Q operation and wait for the result.
   * 
   * Common pattern for I/Q operations: activate operation, register callback,
   * start timeout guard, await result.
   * 
   * @param timeoutMs Operation timeout
   * @param activate Function that starts the I/Q operation and returns cleanup function
   * @return Result from callback or timeout
   */
  def awaitIQOperation[T](timeoutMs: Long)(activate: (T => Unit) => () => Unit): Either[String, T] = {
    val latch = new CountDownLatch(1)
    @volatile var result: Either[String, T] = Left("timeout")
    @volatile var timeoutThread: Option[Thread] = None
    
    val cleanup = activate { value =>
      result = Right(value)
      latch.countDown()
    }
    
    timeoutThread = Some(Isabelle_Thread.fork(name = "iq-timeout") {
      try {
        Thread.sleep(timeoutMs)
        result = Left("timeout")
        latch.countDown()
        cleanup()
      } catch {
        case _: InterruptedException => // Early completion
      }
    })
    
    latch.await(timeoutMs + 2000, TimeUnit.MILLISECONDS)
    timeoutThread.foreach(_.interrupt())
    result
  }
  
  /**
   * Execute an async operation with callback and wait for result.
   * Generic pattern used throughout Assistant for async operations with timeouts.
   * 
   * @param timeoutMs Maximum time to wait
   * @param operation Function that starts async work and registers callback
   * @return Result from callback, or Left(timeout message) on timeout
   */
  def awaitCallback[T](timeoutMs: Long)(operation: (T => Unit) => Unit): Either[String, T] = {
    val latch = new CountDownLatch(1)
    @volatile var result: Option[T] = None
    @volatile var error: Option[String] = None
    
    try {
      operation { value =>
        result = Some(value)
        latch.countDown()
      }
    } catch {
      case ex: Exception =>
        error = Some(ex.getMessage)
        latch.countDown()
    }
    
    if (latch.await(timeoutMs, TimeUnit.MILLISECONDS)) {
      error match {
        case Some(err) => Left(err)
        case None => result.map(Right(_)).getOrElse(Left("no result"))
      }
    } else {
      Left("timeout")
    }
  }
  
  /**
   * Execute work on GUI thread with a callback-based result.
   * Common pattern: dispatch to GUI thread, set up callback, await on latch.
   * 
   * @param timeoutMs Maximum time to wait
   * @param guiWork Function that executes on GUI thread and registers callback
   * @return Result from callback or None on timeout
   */
  def awaitGUICallback[T](timeoutMs: Long)(guiWork: (T => Unit) => Unit): Option[T] = {
    val latch = new CountDownLatch(1)
    @volatile var result: Option[T] = None
    
    GUI_Thread.later {
      try {
        guiWork { value =>
          result = Some(value)
          latch.countDown()
        }
      } catch {
        case _: Exception => latch.countDown()
      }
    }
    
    if (latch.await(timeoutMs, TimeUnit.MILLISECONDS)) result
    else None
  }
}
