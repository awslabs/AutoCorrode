/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Bounded recent-input buffer with up/down navigation, used by the chat input
  * in AssistantDockable to browse recent user messages. Stores entries in
  * oldest→newest order and deduplicates consecutive duplicates on record.
  *
  * Navigation model: when the user starts browsing (not yet in the history),
  * the current input is saved as a "draft" and restored when they navigate
  * past the newest entry.
  *
  * This type is intentionally pure — the chat input component is responsible
  * for reading/writing the text field; this buffer only reports what the text
  * should become.
  *
  * Backed by `ArrayDeque` so append and newest-peek are both O(1); mirrors the
  * pattern `ChatAction.history` uses for its bounded chat log. Capacity is
  * bounded so that long sessions with many sent messages do not leak memory —
  * the oldest entry is evicted when a new one would push past the cap.
  */
private[assistant] class InputHistoryBuffer(
    maxEntries: Int = InputHistoryBuffer.DefaultMaxEntries
) {
  require(maxEntries > 0, "maxEntries must be positive")

  private val entries = new java.util.ArrayDeque[String]() // oldest → newest
  private var index: Int = -1             // -1 = not browsing
  private var savedDraft: String = ""     // Draft saved when user starts browsing

  /** Clear history and reset navigation state. */
  def clear(): Unit = {
    entries.clear()
    resetNavigation()
  }

  /** Reset navigation state without dropping the history. Called when the user
    * starts typing a brand-new message (e.g. after a send or an Escape). */
  def resetNavigation(): Unit = {
    index = -1
    savedDraft = ""
  }

  /** Record a sent message, deduplicating consecutive repeats. Evicts the
    * oldest entry when the buffer is at capacity. Very long messages (e.g. a
    * large paste) are truncated at [[AssistantConstants.MAX_HISTORY_ENTRY_CHARS]]
    * before storage so a single runaway entry can't dominate memory for the
    * session's lifetime. */
  def record(message: String): Unit = {
    if (message.nonEmpty) {
      val truncated = truncateForStorage(message)
      if (entries.isEmpty || entries.peekLast() != truncated) {
        if (entries.size >= maxEntries) {
          val _ = entries.pollFirst()
        }
        entries.addLast(truncated)
      }
    }
    resetNavigation()
  }

  private def truncateForStorage(message: String): String = {
    val cap = AssistantConstants.MAX_HISTORY_ENTRY_CHARS
    if (message.length <= cap) message
    else message.substring(0, cap) + InputHistoryBuffer.TruncationMarker
  }

  def isEmpty: Boolean = entries.isEmpty
  def size: Int = entries.size

  /** True when the user is currently browsing (as opposed to editing a new
    * draft). Used by the Escape handler to decide whether to clear the input
    * or advance to the next Esc-tap behavior. */
  def isBrowsing: Boolean = index != -1

  /** Advance "back" in time — toward older entries. Returns the text the chat
    * input should display, or `None` if there's nothing to show (empty history
    * or already at the oldest entry). If the user isn't browsing yet, captures
    * the current draft. */
  def navigateBack(currentDraft: String): Option[String] = {
    if (entries.isEmpty) None
    else if (index == -1) {
      savedDraft = currentDraft
      index = 0
      entryFromNewest(index)
    } else if (index < entries.size - 1) {
      index += 1
      entryFromNewest(index)
    } else None
  }

  /** Advance "forward" in time — toward newer entries, eventually restoring
    * the saved draft. Returns the text the chat input should display, or
    * `None` if the user isn't browsing. */
  def navigateForward(): Option[String] = {
    if (index == -1) None
    else if (index > 0) {
      index -= 1
      entryFromNewest(index)
    } else {
      index = -1
      Some(savedDraft)
    }
  }

  /** Fetch the entry `i` steps back from the newest. `i = 0` → newest entry. */
  private def entryFromNewest(i: Int): Option[String] = {
    val it = entries.descendingIterator()
    var skipped = 0
    while (skipped < i && it.hasNext) {
      val _ = it.next()
      skipped += 1
    }
    if (it.hasNext) Some(it.next()) else None
  }
}

private[assistant] object InputHistoryBuffer {
  /** Default cap on retained recent inputs. Large enough to comfortably cover
    * a working session, small enough that unbounded growth is impossible. */
  val DefaultMaxEntries: Int = 500

  /** Sentinel appended to truncated entries so the user (and tests) can tell
    * an entry was shortened rather than sent in full. */
  val TruncationMarker: String = "\n… [truncated]"
}
