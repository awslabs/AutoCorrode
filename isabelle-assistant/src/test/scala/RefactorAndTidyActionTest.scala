/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Both `RefactorAction` and `TidyAction` use the same shape of Mustache
  * substitutions: a mandatory `proof`/`code` key plus optional goal_state,
  * local_facts, relevant_theorems, and context entries pulled from a
  * `ContextBundle`. The helpers are the only non-IO-heavy part of either
  * action, so this suite anchors their behaviour against accidental
  * drift (e.g. swapping the keys, dropping the extras map).
  */
class RefactorAndTidyActionTest extends AnyFunSuite with Matchers {

  private val emptyBundle = ProofContextSupport.ContextBundle()
  private val fullBundle = ProofContextSupport.ContextBundle(
    localFacts       = "foo: P x",
    relevantTheorems = "bar: Q x",
    definitions      = "def baz"
  )

  test("refactor: empty bundle yields just the proof key") {
    val out = RefactorAction.buildPromptSubstitutions(
      proofText = "apply simp\nby auto",
      goalState = None,
      bundle    = emptyBundle
    )
    out shouldBe Map("proof" -> "apply simp\nby auto")
  }

  test("refactor: all optional keys attach when goal state and bundle are populated") {
    val out = RefactorAction.buildPromptSubstitutions(
      proofText = "by auto",
      goalState = Some("⟦P x⟧ ⟹ Q x"),
      bundle    = fullBundle
    )
    out("proof") shouldBe "by auto"
    out("goal_state") shouldBe "⟦P x⟧ ⟹ Q x"
    out("local_facts") shouldBe "foo: P x"
    out("relevant_theorems") shouldBe "bar: Q x"
    out("context") shouldBe "def baz"
  }

  test("refactor: extra map entries override bundle keys when they collide") {
    // `extra` is applied last, so a caller that wants to stamp a specific
    // value (e.g. a custom `goal_state`) can do so without the bundle
    // quietly winning.
    val out = RefactorAction.buildPromptSubstitutions(
      proofText = "by auto",
      goalState = Some("inner"),
      bundle    = fullBundle,
      extra     = Map("goal_state" -> "overridden")
    )
    out("goal_state") shouldBe "overridden"
  }

  test("tidy: same shape with `code` instead of `proof`") {
    val out = TidyAction.buildPromptSubstitutions(
      code      = "lemma foo: True by auto",
      goalState = None,
      bundle    = emptyBundle
    )
    out shouldBe Map("code" -> "lemma foo: True by auto")
  }

  test("tidy: optional fields populate from bundle") {
    val out = TidyAction.buildPromptSubstitutions(
      code      = "lemma foo: True by auto",
      goalState = Some("True"),
      bundle    = fullBundle
    )
    out.keySet shouldBe Set("code", "goal_state", "local_facts", "relevant_theorems", "context")
  }
}
