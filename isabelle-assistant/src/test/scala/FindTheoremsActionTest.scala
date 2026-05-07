/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Pure-helper coverage for `FindTheoremsAction.extractGoalPattern`. This is
  * the string manipulation the `:find` flow runs before pushing a query to
  * I/Q, and the only part of the action that does not require a live buffer
  * or Isabelle thread.
  */
class FindTheoremsActionTest extends AnyFunSuite with Matchers {

  test("extractGoalPattern picks the first numbered subgoal line") {
    val goal =
      """goal (2 subgoals):
        | 1. P x ⟹ Q x
        | 2. R y""".stripMargin
    FindTheoremsAction.extractGoalPattern(goal) shouldBe Some("P x ⟹ Q x")
  }

  test("extractGoalPattern falls back to the first non-goal, non-proof line") {
    // No numbered subgoal, but a bare conclusion line: the fallback should
    // skip the `goal` and `proof` chatter and pick the substantive line.
    val state =
      """goal:
        |proof (prove)
        |concluded: foo x y""".stripMargin
    FindTheoremsAction.extractGoalPattern(state) shouldBe Some("concluded: foo x y")
  }

  test("extractGoalPattern returns None for empty or whitespace input") {
    FindTheoremsAction.extractGoalPattern("")            shouldBe None
    FindTheoremsAction.extractGoalPattern("   \n\t\n  ") shouldBe None
  }

  test("extractGoalPattern caps output at MAX_RESPONSE_LENGTH characters") {
    val long = " 1. " + ("x" * (AssistantConstants.MAX_RESPONSE_LENGTH + 100))
    val out = FindTheoremsAction.extractGoalPattern(long)
    out.isDefined shouldBe true
    out.get.length should be <= AssistantConstants.MAX_RESPONSE_LENGTH
  }
}
