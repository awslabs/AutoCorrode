/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle.{GUI_Thread, Isabelle_Thread}

/**
 * Shared lifecycle guard for asynchronous I/Q operations.
 * Ensures completion/deactivation happens exactly once across success/failure/timeout races.
 */
final class IQOperationLifecycle[A](
  onComplete: A => Unit,
  deactivate: () => Unit
) {
  private val lock = new Object()
  @volatile private var completed = false
  @volatile private var timeoutThread: Option[Thread] = None

  def isCompleted: Boolean = completed

  def setTimeoutThread(thread: Thread): Unit = {
    timeoutThread = Some(thread)
  }

  /** Complete from non-timeout path and interrupt timeout watcher. */
  def complete(result: A): Unit = {
    finish(result, interruptTimeout = true)
  }

  /** Complete from timeout path without self-interrupting timeout thread. */
  def completeFromTimeout(result: A): Unit = {
    finish(result, interruptTimeout = false)
  }

  /** Spawn timeout watcher that completes with the given timeout result. */
  def forkTimeout(name: String, timeoutMs: Long)(timeoutResult: => A): Thread = {
    val thread = Isabelle_Thread.fork(name = name) {
      try {
        Thread.sleep(timeoutMs)
        completeFromTimeout(timeoutResult)
      } catch {
        case _: InterruptedException => ()
      }
    }
    setTimeoutThread(thread)
    thread
  }

  private def finish(result: A, interruptTimeout: Boolean): Unit = {
    val shouldRun = lock.synchronized {
      if (!completed) {
        completed = true
        true
      } else false
    }
    if (shouldRun) {
      if (interruptTimeout) timeoutThread.foreach(_.interrupt())
      try {
        onComplete(result)
      } finally {
        GUI_Thread.later { deactivate() }
      }
    }
  }
}
