/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ActionPromptContextTest extends AnyFunSuite with Matchers {

  private val richBundle = ProofContextSupport.ContextBundle(
    localFacts = "fact1: A",
    relevantTheorems = "thm1: A ==> A",
    definitions = "definition foo where ..."
  )

  test("RefactorAction prompt substitutions should include all available context and extras") {
    val subs = RefactorAction.buildPromptSubstitutions(
      proofText = "apply simp",
      goalState = Some("1. A"),
      bundle = richBundle,
      extra = Map("failed_attempt" -> "by simp", "error" -> "failed")
    )

    subs("proof") shouldBe "apply simp"
    subs("goal_state") shouldBe "1. A"
    subs("local_facts") should include("fact1")
    subs("relevant_theorems") should include("thm1")
    subs("context") should include("definition foo")
    subs("failed_attempt") shouldBe "by simp"
    subs("error") shouldBe "failed"
  }

  test("RefactorAction prompt substitutions should omit empty optional context keys") {
    val subs = RefactorAction.buildPromptSubstitutions(
      proofText = "by simp",
      goalState = None,
      bundle = ProofContextSupport.ContextBundle()
    )

    subs shouldBe Map("proof" -> "by simp")
  }

  test("TidyAction prompt substitutions should include all available context and extras") {
    val subs = TidyAction.buildPromptSubstitutions(
      code = "lemma x: True by simp",
      goalState = Some("1. True"),
      bundle = richBundle,
      extra = Map("failed_attempt" -> "by blast", "error" -> "timeout")
    )

    subs("code") should include("lemma x")
    subs("goal_state") shouldBe "1. True"
    subs("local_facts") should include("fact1")
    subs("relevant_theorems") should include("thm1")
    subs("context") should include("definition foo")
    subs("failed_attempt") shouldBe "by blast"
    subs("error") shouldBe "timeout"
  }

  test("SuggestAction prompt substitutions should include relevant_theorems only when non-empty") {
    val withContext = SuggestAction.buildPromptSubstitutions(
      commandText = "by simp",
      goalState = "1. A",
      contextInfo = "thm: A ==> A"
    )
    withContext("command") shouldBe "by simp"
    withContext("goal_state") shouldBe "1. A"
    withContext("relevant_theorems") should include("thm:")

    val withoutContext = SuggestAction.buildPromptSubstitutions(
      commandText = "by simp",
      goalState = "1. A",
      contextInfo = ""
    )
    withoutContext.contains("relevant_theorems") shouldBe false
  }
}

