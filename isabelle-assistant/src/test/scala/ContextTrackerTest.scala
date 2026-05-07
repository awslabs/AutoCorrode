/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Unit tests for [[ContextTracker]] token estimation. The int-keyed
  * overload was added to fix a perf bug: the context bar used to allocate
  * a multi-100K-char scratch string on every UI refresh just to compute
  * the character count of the active tool loop. The two helpers must
  * produce identical answers so callers can mix them freely. */
class ContextTrackerTest extends AnyFunSuite with Matchers {

  test("estimateTokens and estimateTokensFromChars agree for small inputs") {
    for (n <- 0 to 100) {
      val text = "x" * n
      ContextTracker.estimateTokens(text) shouldBe
        ContextTracker.estimateTokensFromChars(n)
    }
  }

  test("estimateTokensFromChars matches the 3.5 chars/token heuristic") {
    // 35 chars → 10 tokens (35 / 3.5 = 10 exactly).
    ContextTracker.estimateTokensFromChars(35) shouldBe 10
    // 36 chars → ceil(36 / 3.5) = 11.
    ContextTracker.estimateTokensFromChars(36) shouldBe 11
    ContextTracker.estimateTokensFromChars(0) shouldBe 0
  }

  test("estimateTokensFromChars does not allocate a scratch string for large inputs") {
    // This test passes trivially if the overload is pure arithmetic. The
    // previous `"a" * toolLoopChars` path would GC-pressure a JVM here on
    // a 10M-char input; the int overload completes in microseconds.
    val start = System.nanoTime()
    val tokens = ContextTracker.estimateTokensFromChars(10_000_000)
    val elapsedMs = (System.nanoTime() - start) / 1_000_000
    tokens shouldBe math.ceil(10_000_000 / 3.5).toInt
    elapsedMs should be < 50L
  }

  test("formatThousands produces K-suffixed rounding for large counts") {
    ContextTracker.formatThousands(999) shouldBe "999"
    ContextTracker.formatThousands(1000) shouldBe "1K"
    ContextTracker.formatThousands(14200) shouldBe "14K"
    ContextTracker.formatThousands(0) shouldBe "0"
  }

  test("modelContextWindow returns 200K for known Claude models and unknowns") {
    ContextTracker.modelContextWindow(
      "anthropic.claude-3-5-sonnet-20241022-v2:0"
    ) shouldBe 200000
    ContextTracker.modelContextWindow(
      "us.anthropic.claude-3-5-sonnet-20241022-v2:0"
    ) shouldBe 200000
    // Claude-family fallback via substring match.
    ContextTracker.modelContextWindow(
      "anthropic.claude-3-5-made-up-id"
    ) shouldBe 200000
    // Totally unknown model falls back to the conservative default.
    ContextTracker.modelContextWindow("some-other-vendor.foo") shouldBe 200000
    ContextTracker.modelContextWindow("") shouldBe 200000
  }
}
