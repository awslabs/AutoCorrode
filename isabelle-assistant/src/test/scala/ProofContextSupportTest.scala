/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ProofContextSupportTest extends AnyFunSuite with Matchers {

  test("extractNamesForFindTheorems should prefer constants from goal analysis") {
    val analysis = GoalExtractor.GoalAnalysis(
      text = "goal",
      freeVars = List("x"),
      constants = List("List.map", "List.filter", "List.map"),
      numSubgoals = 1
    )

    val names = ProofContextSupport.extractNamesForFindTheorems(
      "irrelevant fallback text",
      Some(analysis)
    )

    names shouldBe List("List.map", "List.filter")
  }

  test("extractNamesForFindTheorems should fall back to goal text heuristics") {
    val goalText =
      """goal (1 subgoal):
        |1. map f (xs @ ys) = map f xs @ map f ys""".stripMargin

    val names =
      ProofContextSupport.extractNamesForFindTheorems(goalText, None)

    names should contain("map")
    names should not contain "goal"
  }
}
