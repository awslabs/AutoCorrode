/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class GoalExtractorTest extends AnyFunSuite with Matchers {

  private def elem(name: String, props: Properties.T = Nil, body: List[XML.Tree] = Nil): XML.Tree =
    XML.Elem(Markup(name, props), body)

  test("analyzeGoalFromMessages should extract free vars/constants/subgoals from PIDE markup") {
    val messages = List(
      elem("subgoal", body = List(
        elem(Markup.FREE, List("name" -> "x")),
        elem("fixed", List("name" -> "y")),
        elem(Markup.CONSTANT, List("name" -> "List.map")),
        elem(Markup.CONSTANT, List("name" -> "Pure.all")),
        XML.Text("⊢ map f xs = ys")
      ))
    )

    val result = GoalExtractor.analyzeGoalFromMessages(messages, List("fallback"))
    result should not be empty
    val analysis = result.get
    analysis.text should include("⊢ map f xs = ys")
    analysis.freeVars should contain theSameElementsAs List("x", "y")
    analysis.constants should contain theSameElementsAs List("List.map")
    analysis.constants should not contain "Pure.all"
    analysis.numSubgoals shouldBe 1
  }

  test("analyzeGoalFromMessages should use fallback vars when FREE/fixed markup absent") {
    val messages = List(elem("subgoal", body = List(XML.Text("goal text"))))
    val result = GoalExtractor.analyzeGoalFromMessages(messages, List("n", "m"))
    result.get.freeVars should contain theSameElementsAs List("n", "m")
  }

  test("analyzeGoalFromMessages should return None for empty/blank output") {
    GoalExtractor.analyzeGoalFromMessages(Nil) shouldBe None
    GoalExtractor.analyzeGoalFromMessages(List(XML.Text("   "))) shouldBe None
  }

  test("isInProofContextFromKeywords should correctly track opener/closer depth") {
    GoalExtractor.isInProofContextFromKeywords(Seq.empty) shouldBe false
    GoalExtractor.isInProofContextFromKeywords(Seq("qed")) shouldBe false
    GoalExtractor.isInProofContextFromKeywords(Seq("proof")) shouldBe true
    GoalExtractor.isInProofContextFromKeywords(Seq("proof", "qed")) shouldBe false
    GoalExtractor.isInProofContextFromKeywords(Seq("proof", "next", "by")) shouldBe true
    GoalExtractor.isInProofContextFromKeywords(Seq("proof", "qed", "qed")) shouldBe false
  }
}
