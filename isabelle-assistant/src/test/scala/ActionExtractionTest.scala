/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ActionExtractionTest extends AnyFunSuite with Matchers {

  test("RefactorAction.extractCode should prefer JSON code field") {
    val response =
      """Result:
        |{"code":"proof -\n  show ?thesis by simp\nqed"}""".stripMargin
    RefactorAction.extractCode(response) should include("show ?thesis by simp")
  }

  test("TidyAction.extractCode should fall back to fenced Isabelle code") {
    val response =
      """Here is the tidied script:
        |```isabelle
        |lemma foo: True
        |  by simp
        |```""".stripMargin
    TidyAction.extractCode(response) should include("lemma foo: True")
  }

  test("ExtractLemmaAction.parseExtractionResponse should parse valid JSON payload") {
    val response =
      """{
        |  "extracted_lemma": "lemma helper_lemma: \"A ==> A\" by simp",
        |  "updated_proof": "proof - show ?thesis by (rule helper_lemma) qed"
        |}""".stripMargin

    val parsed = ExtractLemmaAction.parseExtractionResponse(response)
    parsed should not be empty
    parsed.get.lemmaName shouldBe "helper_lemma"
    parsed.get.updatedProof should include("helper_lemma")
  }

  test("ExtractLemmaAction.parseExtractionResponse should reject incomplete payloads") {
    val response = """{"updated_proof":"proof - qed"}"""
    ExtractLemmaAction.parseExtractionResponse(response) shouldBe None
  }

  test("FindTheoremsAction.extractGoalPattern should prefer numbered subgoal line") {
    val goal =
      """goal (1 subgoal):
        |1. xs @ [] = xs""".stripMargin
    FindTheoremsAction.extractGoalPattern(goal) shouldBe Some("xs @ [] = xs")
  }
}
