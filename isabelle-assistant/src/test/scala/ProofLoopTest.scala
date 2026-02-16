/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * ProofLoop orchestration tests (orthogonal to ProofTextUtil text-manipulation tests).
 */
class ProofLoopTest extends AnyFunSuite with Matchers {

  test("inductionCandidatesForTest should produce 4 candidates per free variable") {
    val candidates = ProofLoop.inductionCandidatesForTest(List("n", "xs"))
    candidates.length shouldBe 8
    candidates should contain("by (induction n) auto")
    candidates should contain("by (cases xs) auto")
  }

  test("findReplacementForTest should extract replacement between old/new proof text") {
    val oldProof = "proof -\n  sorry\nqed"
    val newProof = "proof -\n  by simp\nqed"
    ProofLoop.findReplacementForTest(oldProof, newProof) shouldBe "by simp"
  }

  test("findReplacementForTest should return unknown marker when no sorry is present") {
    val oldProof = "proof -\n  show ?thesis by simp\nqed"
    val newProof = oldProof
    ProofLoop.findReplacementForTest(oldProof, newProof) shouldBe "(unknown method)"
  }
}

