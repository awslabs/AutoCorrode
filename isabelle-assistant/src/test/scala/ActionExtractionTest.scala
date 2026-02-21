/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ActionExtractionTest extends AnyFunSuite with Matchers {

  test("ExtractLemmaAction.parseStructuredExtraction should parse valid ToolArgs") {
    val args: ResponseParser.ToolArgs = Map(
      "extracted_lemma" -> ResponseParser.StringValue("lemma helper_lemma: \"A ==> A\" by simp"),
      "updated_proof" -> ResponseParser.StringValue("proof - show ?thesis by (rule helper_lemma) qed")
    )
    val parsed = ExtractLemmaAction.parseStructuredExtraction(args)
    parsed should not be empty
    parsed.get.lemmaName shouldBe "helper_lemma"
    parsed.get.updatedProof should include("helper_lemma")
  }

  test("ExtractLemmaAction.parseStructuredExtraction should reject missing fields") {
    val args: ResponseParser.ToolArgs = Map(
      "updated_proof" -> ResponseParser.StringValue("proof - qed")
    )
    ExtractLemmaAction.parseStructuredExtraction(args) shouldBe None
  }

  test("ExtractLemmaAction.parseStructuredExtraction should handle NullValue fields") {
    val args: ResponseParser.ToolArgs = Map(
      "extracted_lemma" -> ResponseParser.NullValue,
      "updated_proof" -> ResponseParser.StringValue("proof")
    )
    val parsed = ExtractLemmaAction.parseStructuredExtraction(args)
    parsed shouldBe defined
    parsed.get.extractedLemma shouldBe ""
  }

  test("FindTheoremsAction.extractGoalPattern should prefer numbered subgoal line") {
    val goal =
      """goal (1 subgoal):
        |1. xs @ [] = xs""".stripMargin
    FindTheoremsAction.extractGoalPattern(goal) shouldBe Some("xs @ [] = xs")
  }
}
