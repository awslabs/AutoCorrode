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

  /** Reset cancellation state. Intentionally package-private — reusing a
    * token across two operations is error-prone, and callers should
    * prefer a fresh `CancellationToken` per op. Scoped to
    * `isabelle.assistant` so tests can still exercise the reset path.
    */
  private[assistant] def reset(): Unit = cancelled.set(false)
}
