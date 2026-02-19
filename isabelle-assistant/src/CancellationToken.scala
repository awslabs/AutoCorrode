/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.util.concurrent.atomic.AtomicBoolean

/** Per-operation cancellation token. Allows individual operations to be
  * cancelled without affecting others. Thread-safe via atomic operations.
  */
class CancellationToken {
  private val cancelled = new AtomicBoolean(false)

  /** Check if this operation has been cancelled. */
  def isCancelled: Boolean = cancelled.get()

  /** Cancel this operation. */
  def cancel(): Unit = cancelled.set(true)

  /** Reset cancellation state (for reuse, though creating new tokens is
    * preferred).
    */
  def reset(): Unit = cancelled.set(false)
}
