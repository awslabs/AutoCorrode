/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Context-window heuristic used by `:summarize` to decide whether the
  * theory text is small enough to fit. Pinned here so that a regression in
  * the model-id lookup table surfaces as a failing unit test instead of an
  * unexpected warning dialog at runtime.
  */
class SummarizeTheoryActionTest extends AnyFunSuite with Matchers {

  test("Claude models (Sonnet, Opus, 4.x) get a 200K budget") {
    SummarizeTheoryAction.estimateContextWindowFor("anthropic.claude-sonnet-4-6") shouldBe 200000
    SummarizeTheoryAction.estimateContextWindowFor("anthropic.claude-opus-4-7")   shouldBe 200000
    SummarizeTheoryAction.estimateContextWindowFor("anthropic.claude-4-haiku")    shouldBe 200000
    // Generic "claude" fallback is also 200K — the default for any future
    // Claude ID the hard-coded list hasn't learnt yet.
    SummarizeTheoryAction.estimateContextWindowFor("anthropic.claude-9000-future") shouldBe 200000
  }

  test("Llama 3 and Mistral Large both budget to 128K") {
    SummarizeTheoryAction.estimateContextWindowFor("meta.llama3-8b-instruct")  shouldBe 128000
    SummarizeTheoryAction.estimateContextWindowFor("meta.llama-3-70b")         shouldBe 128000
    SummarizeTheoryAction.estimateContextWindowFor("mistral.mistral-large-2407") shouldBe 128000
  }

  test("Titan uses 32K, everything else defaults to 100K") {
    SummarizeTheoryAction.estimateContextWindowFor("amazon.titan-text-premier") shouldBe 32000
    SummarizeTheoryAction.estimateContextWindowFor("some.unknown-model-v1")      shouldBe 100000
  }
}
