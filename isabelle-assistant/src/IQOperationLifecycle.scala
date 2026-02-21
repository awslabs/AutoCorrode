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
  deactivate: () => Unit,
  forkThread: (String, () => Unit) => Thread = IQOperationLifecycle.forkIsabelleThread,
  dispatchToGui: (() => Unit) => Unit = IQOperationLifecycle.dispatchToIsabelleGui
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
    val thread = forkThread(name, () => {
      try {
        Thread.sleep(timeoutMs)
        completeFromTimeout(timeoutResult)
      } catch {
        case _: InterruptedException => ()
      }
    })
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
        dispatchToGui(() => deactivate())
      }
    }
  }
}

object IQOperationLifecycle {
  private[assistant] def forkIsabelleThread(
      name: String,
      body: () => Unit
  ): Thread =
    Isabelle_Thread.fork(name = name) { body() }

  private[assistant] def dispatchToIsabelleGui(body: () => Unit): Unit =
    GUI_Thread.later { body() }

  private[assistant] def forkJvmThread(
      name: String,
      body: () => Unit
  ): Thread = {
    val thread = new Thread(() => body(), name)
    thread.setDaemon(true)
    thread.start()
    thread
  }

  private[assistant] def runInline(body: () => Unit): Unit =
    body()
}
