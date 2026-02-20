/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Boundary-condition tests for pure helper logic used by tool execution.
 */
class BoundaryConditionTest extends AnyFunSuite with Matchers {

  test("normalizeReadRange should clamp requests to valid line window") {
    AssistantTools.normalizeReadRange(totalLines = 10, requestedStart = 1, requestedEnd = 10) shouldBe (1, 10)
    AssistantTools.normalizeReadRange(totalLines = 10, requestedStart = -5, requestedEnd = 4) shouldBe (1, 4)
    AssistantTools.normalizeReadRange(totalLines = 10, requestedStart = 7, requestedEnd = 2) shouldBe (7, 7)
    AssistantTools.normalizeReadRange(totalLines = 10, requestedStart = 3, requestedEnd = -1) shouldBe (3, 10)
    AssistantTools.normalizeReadRange(totalLines = 0, requestedStart = 1, requestedEnd = 1) shouldBe (1, 0)
  }

  test("clampOffset should keep offsets inside buffer bounds") {
    AssistantTools.clampOffset(offset = -1, bufferLength = 5) shouldBe 0
    AssistantTools.clampOffset(offset = 0, bufferLength = 5) shouldBe 0
    AssistantTools.clampOffset(offset = 3, bufferLength = 5) shouldBe 3
    AssistantTools.clampOffset(offset = 5, bufferLength = 5) shouldBe 5
    AssistantTools.clampOffset(offset = 99, bufferLength = 5) shouldBe 5
  }

  test("proof-context keyword scan should detect unmatched openers") {
    GoalExtractor.isInProofContextFromKeywords(Seq("lemma", "proof", "have")) shouldBe true
    GoalExtractor.isInProofContextFromKeywords(Seq("proof", "qed")) shouldBe false
    GoalExtractor.isInProofContextFromKeywords(Seq("lemma", "proof", "next", "proof", "qed")) shouldBe true
    GoalExtractor.isInProofContextFromKeywords(Seq("text", "section")) shouldBe false
  }
}
