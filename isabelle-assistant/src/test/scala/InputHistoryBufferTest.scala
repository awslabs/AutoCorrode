/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class InputHistoryBufferTest extends AnyFunSuite with Matchers {

  test("empty buffer: navigateBack returns None and leaves draft untouched") {
    val buf = new InputHistoryBuffer()
    buf.isEmpty shouldBe true
    buf.navigateBack("draft") shouldBe None
    buf.isBrowsing shouldBe false
  }

  test("empty buffer: navigateForward returns None when not browsing") {
    val buf = new InputHistoryBuffer()
    buf.navigateForward() shouldBe None
  }

  test("record stores messages and deduplicates consecutive duplicates") {
    val buf = new InputHistoryBuffer()
    buf.record("hello")
    buf.record("world")
    buf.record("world") // consecutive duplicate
    buf.record("goodbye")
    buf.size shouldBe 3
  }

  test("record ignores empty messages") {
    val buf = new InputHistoryBuffer()
    buf.record("")
    buf.isEmpty shouldBe true
  }

  test("navigateBack captures draft and walks from newest to oldest") {
    val buf = new InputHistoryBuffer()
    buf.record("first")
    buf.record("second")
    buf.record("third")

    buf.navigateBack("my draft") shouldBe Some("third")
    buf.isBrowsing shouldBe true
    buf.navigateBack("my draft") shouldBe Some("second")
    buf.navigateBack("my draft") shouldBe Some("first")
    // Already at oldest: no further movement
    buf.navigateBack("my draft") shouldBe None
  }

  test("navigateForward restores saved draft after walking back to present") {
    val buf = new InputHistoryBuffer()
    buf.record("first")
    buf.record("second")

    buf.navigateBack("unsent text") shouldBe Some("second")
    buf.navigateBack("unsent text") shouldBe Some("first")
    buf.navigateForward() shouldBe Some("second")
    buf.navigateForward() shouldBe Some("unsent text")
    buf.isBrowsing shouldBe false
    // Forward past draft is no-op
    buf.navigateForward() shouldBe None
  }

  test("record resets navigation so next Back starts from newest again") {
    val buf = new InputHistoryBuffer()
    buf.record("a")
    buf.record("b")

    buf.navigateBack("") shouldBe Some("b")
    buf.navigateBack("") shouldBe Some("a")

    // User sends a new message; subsequent Back should start from newest entry
    buf.record("c")
    buf.isBrowsing shouldBe false
    buf.navigateBack("") shouldBe Some("c")
  }

  test("clear drops history and navigation") {
    val buf = new InputHistoryBuffer()
    buf.record("x")
    buf.navigateBack("") shouldBe Some("x")
    buf.clear()
    buf.isEmpty shouldBe true
    buf.isBrowsing shouldBe false
    buf.navigateBack("") shouldBe None
  }

  test("resetNavigation leaves history intact but ends browsing") {
    val buf = new InputHistoryBuffer()
    buf.record("a")
    buf.record("b")
    buf.navigateBack("") shouldBe Some("b")
    buf.resetNavigation()
    buf.isBrowsing shouldBe false
    buf.size shouldBe 2
    buf.navigateBack("") shouldBe Some("b")
  }

  test("record evicts oldest entries once the capacity is exceeded") {
    val buf = new InputHistoryBuffer(maxEntries = 3)
    buf.record("a")
    buf.record("b")
    buf.record("c")
    buf.record("d") // evicts "a"
    buf.size shouldBe 3

    buf.navigateBack("") shouldBe Some("d")
    buf.navigateBack("") shouldBe Some("c")
    buf.navigateBack("") shouldBe Some("b")
    // "a" was evicted; we're at the oldest entry now
    buf.navigateBack("") shouldBe None
  }

  test("record rejects non-positive capacities") {
    an[IllegalArgumentException] should be thrownBy new InputHistoryBuffer(maxEntries = 0)
    an[IllegalArgumentException] should be thrownBy new InputHistoryBuffer(maxEntries = -1)
  }

  test("record truncates very long entries and marks them as truncated") {
    val buf = new InputHistoryBuffer()
    val huge = "x" * (AssistantConstants.MAX_HISTORY_ENTRY_CHARS + 1000)
    buf.record(huge)
    buf.size shouldBe 1
    val stored = buf.navigateBack("").getOrElse(fail("expected entry"))
    stored.length should be < huge.length
    stored should endWith(InputHistoryBuffer.TruncationMarker)
    stored.length shouldBe (AssistantConstants.MAX_HISTORY_ENTRY_CHARS + InputHistoryBuffer.TruncationMarker.length)
  }

  test("record keeps under-cap entries verbatim") {
    val buf = new InputHistoryBuffer()
    val small = "x" * (AssistantConstants.MAX_HISTORY_ENTRY_CHARS - 1)
    buf.record(small)
    buf.navigateBack("") shouldBe Some(small)
  }
}
