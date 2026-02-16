/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class SuggestActionTest extends AnyFunSuite with Matchers {

  test("deduplicateCandidates should keep one candidate per proof text") {
    val candidates = List(
      SuggestAction.Candidate("by simp", SuggestAction.LLM),
      SuggestAction.Candidate("by simp", SuggestAction.LLM),
      SuggestAction.Candidate("by auto", SuggestAction.LLM)
    )
    val deduped = SuggestAction.deduplicateCandidates(candidates)
    deduped.map(_.proof).toSet shouldBe Set("by simp", "by auto")
    deduped.length shouldBe 2
  }

  test("deduplicateCandidates should prefer sledgehammer candidate for duplicate proof") {
    val llm = SuggestAction.Candidate("by metis", SuggestAction.LLM, VerificationBadge.Unverified)
    val sh = SuggestAction.Candidate("by metis", SuggestAction.Sledgehammer, VerificationBadge.Sledgehammer(Some(80L)))
    val deduped = SuggestAction.deduplicateCandidates(List(llm, sh))
    deduped should have length 1
    deduped.head.source shouldBe SuggestAction.Sledgehammer
  }

  test("rankCandidates should prioritize verified candidates") {
    val candidates = List(
      SuggestAction.Candidate("failed", SuggestAction.LLM, VerificationBadge.Failed("error")),
      SuggestAction.Candidate("verified", SuggestAction.LLM, VerificationBadge.Verified(Some(100L))),
      SuggestAction.Candidate("unverified", SuggestAction.LLM, VerificationBadge.Unverified)
    )

    val ranked = SuggestAction.rankCandidates(candidates)
    ranked.head.proof shouldBe "verified"
    ranked.last.proof shouldBe "failed"
  }
}
