/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Tests for SuggestAction.parseStructuredSuggestions and rankCandidates. These are
  * pure functions that don't require jEdit runtime.
  */
class SuggestActionParserTest extends AnyFunSuite with Matchers {

  // --- parseStructuredSuggestions ---

  test("parseStructuredSuggestions should parse suggestions from ToolArgs") {
    val args: ResponseParser.ToolArgs = Map(
      "suggestions" -> ResponseParser.JsonValue("""["by simp","by auto","by blast"]""")
    )
    val result = SuggestAction.parseStructuredSuggestions(args)
    result should contain("by simp")
    result should contain("by auto")
    result should contain("by blast")
    result should have length 3
  }

  test("parseStructuredSuggestions should handle extra whitespace") {
    val args: ResponseParser.ToolArgs = Map(
      "suggestions" -> ResponseParser.JsonValue("""["  by (simp add: foo_def)  "]""")
    )
    val result = SuggestAction.parseStructuredSuggestions(args)
    result should contain("by (simp add: foo_def)")
  }

  test("parseStructuredSuggestions should deduplicate suggestions") {
    val args: ResponseParser.ToolArgs = Map(
      "suggestions" -> ResponseParser.JsonValue("""["by simp","by simp","by auto"]""")
    )
    val result = SuggestAction.parseStructuredSuggestions(args)
    result.count(_ == "by simp") shouldBe 1
    result should have length 2
  }

  test("parseStructuredSuggestions should return empty for missing key") {
    val args: ResponseParser.ToolArgs = Map.empty
    SuggestAction.parseStructuredSuggestions(args) shouldBe empty
  }

  test("parseStructuredSuggestions should filter non-proof items") {
    val args: ResponseParser.ToolArgs = Map(
      "suggestions" -> ResponseParser.JsonValue("""["by simp","This is not a proof method","by auto"]""")
    )
    val result = SuggestAction.parseStructuredSuggestions(args)
    result should contain("by simp")
    result should contain("by auto")
    result should not contain "This is not a proof method"
  }

  // --- rankCandidates ---

  test("rankCandidates should sort Verified before Unverified") {
    val candidates = List(
      SuggestAction
        .Candidate("by auto", SuggestAction.LLM, VerificationBadge.Unverified),
      SuggestAction.Candidate(
        "by simp",
        SuggestAction.LLM,
        VerificationBadge.Verified(Some(100))
      )
    )
    val ranked = SuggestAction.rankCandidates(candidates)
    ranked.head.proof shouldBe "by simp"
  }

  test(
    "rankCandidates should sort Sledgehammer before Unverified but after Verified"
  ) {
    val candidates = List(
      SuggestAction
        .Candidate("by auto", SuggestAction.LLM, VerificationBadge.Unverified),
      SuggestAction.Candidate(
        "by smt",
        SuggestAction.Sledgehammer,
        VerificationBadge.Sledgehammer(Some(500))
      ),
      SuggestAction.Candidate(
        "by simp",
        SuggestAction.LLM,
        VerificationBadge.Verified(Some(100))
      )
    )
    val ranked = SuggestAction.rankCandidates(candidates)
    ranked(0).proof shouldBe "by simp"
    ranked(1).proof shouldBe "by smt"
    ranked(2).proof shouldBe "by auto"
  }

  test("rankCandidates should sort Failed last") {
    val candidates = List(
      SuggestAction.Candidate(
        "by fail",
        SuggestAction.LLM,
        VerificationBadge.Failed("type error")
      ),
      SuggestAction.Candidate(
        "by auto",
        SuggestAction.LLM,
        VerificationBadge.Unverified
      )
    )
    val ranked = SuggestAction.rankCandidates(candidates)
    ranked.head.proof shouldBe "by auto"
    ranked.last.proof shouldBe "by fail"
  }

  test("rankCandidates should sort by time within same badge type") {
    val candidates = List(
      SuggestAction.Candidate(
        "by auto",
        SuggestAction.LLM,
        VerificationBadge.Verified(Some(500)),
        timeMs = Some(500)
      ),
      SuggestAction.Candidate(
        "by simp",
        SuggestAction.LLM,
        VerificationBadge.Verified(Some(100)),
        timeMs = Some(100)
      )
    )
    val ranked = SuggestAction.rankCandidates(candidates)
    ranked.head.proof shouldBe "by simp" // faster
  }
}
