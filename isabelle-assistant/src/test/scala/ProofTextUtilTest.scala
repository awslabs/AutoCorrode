/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ProofTextUtilTest extends AnyFunSuite with Matchers {

  test("extractCode should extract from markdown fences") {
    val response = "Here is the proof:\n```isabelle\nby simp\n```"
    ProofTextUtil.extractCode(response) shouldBe "by simp"
  }

  test("extractCode should handle bare proof methods") {
    val response = "by auto"
    ProofTextUtil.extractCode(response) shouldBe "by auto"
  }

  test("stripGoalRestatement should remove goal prefix") {
    val code = "⊢ P ⟹ Q\nproof -\n  show Q using assms by simp\nqed"
    val stripped = ProofTextUtil.stripGoalRestatement(code)
    stripped should startWith("proof -")
    stripped should not contain "⊢"
  }

  test("cleanProofText should remove trailing junk after closing keywords") {
    ProofTextUtil.cleanProofText("qed 123") shouldBe "qed"
    ProofTextUtil.cleanProofText("done 456") shouldBe "done"
    ProofTextUtil.cleanProofText("(by auto") shouldBe "by auto"
  }

  test("countSorries should count unfilled sorries") {
    ProofTextUtil.countSorries("proof sorry qed") shouldBe 1
    ProofTextUtil.countSorries("sorry sorry") shouldBe 2
    ProofTextUtil.countSorries("sorry (* unfilled *)") shouldBe 0  // marked as unfilled
  }

  test("countUnfilled should count marked sorries") {
    ProofTextUtil.countUnfilled("sorry (* unfilled *)") shouldBe 1
    ProofTextUtil.countUnfilled("sorry") shouldBe 0
  }

  test("splitAtSorry should split at nth sorry") {
    val proof = "proof\n  sorry\n  sorry\nqed"
    ProofTextUtil.splitAtSorry(proof, 0) match {
      case Some((before, after)) =>
        before should include("proof")
        after should include("sorry")
      case None => fail("Should split successfully")
    }
  }

  test("replaceSorry should replace nth sorry") {
    val proof = "proof sorry qed"
    ProofTextUtil.replaceSorry(proof, 0, "by simp") shouldBe Some("proof by simp qed")
  }

  test("markSorry should add markers") {
    val proof = "proof sorry qed"
    ProofTextUtil.markSorry(proof, 0) should include("<<< sorry >>>")
  }

  test("sorryify should replace by clauses with sorry") {
    val proof = "proof by simp qed"
    val result = ProofTextUtil.sorryify(proof)
    result should include("sorry")
    result should not contain "by simp"
  }

  test("sorryify should skip by inside cartouches") {
    val proof = """proof show ‹by example› by simp qed"""
    val result = ProofTextUtil.sorryify(proof)
    result should include("‹by example›")  // preserved
    result should include("sorry")  // replaced the actual by
  }

  test("sorryify should skip by inside string literals") {
    val proof = """proof have "by_label" by simp qed"""
    val result = ProofTextUtil.sorryify(proof)
    // The textual "by_label" must survive — the word boundary in the regex
    // already protects "by_label" because of the trailing _, but a bare "by"
    // inside a quoted literal must also survive.
    val proof2 = """proof have "prove by induction" by simp qed"""
    val result2 = ProofTextUtil.sorryify(proof2)
    result2 should include("\"prove by induction\"")
    result2 should include("sorry")
    result should include("by_label")
  }

  test("sorryify should replace each by-clause independently in a multi-step proof") {
    val proof = """proof
  have h1: P by simp
  have h2: Q by auto
  show ?thesis by (metis h1 h2)
qed"""
    val result = ProofTextUtil.sorryify(proof)
    // Every `by ...` clause should have become `sorry`.
    "\\bsorry\\b".r.findAllIn(result).length shouldBe 3
    result should include("h1")
    result should include("h2")
    result should not include "by simp"
    result should not include "by auto"
    result should not include "by (metis"
  }

  test("isStructurallyComplete should detect qed on final line") {
    ProofTextUtil.isStructurallyComplete("proof\n  sorry\nqed") shouldBe true
  }

  test("isStructurallyComplete should detect done on final line") {
    ProofTextUtil.isStructurallyComplete("proof\n  sorry\ndone") shouldBe true
  }

  test("isStructurallyComplete should detect by line") {
    ProofTextUtil.isStructurallyComplete("proof\n  sorry\nby simp") shouldBe true
  }

  test("isStructurallyComplete should handle single-line by") {
    ProofTextUtil.isStructurallyComplete("by simp") shouldBe true
  }

  test("isStructurallyComplete should reject incomplete proofs") {
    ProofTextUtil.isStructurallyComplete("proof\n  sorry") shouldBe false
  }

  test("extractLemmaStatement should extract statement without proof") {
    val response = """```isabelle
lemma foo: ‹P ⟹ Q›
proof -
  show Q by simp
qed
```"""
    val stmt = ProofTextUtil.extractLemmaStatement(response)
    stmt should include("lemma foo:")
    stmt should not contain "proof"
  }

  test("extractLemmaName should parse lemma name") {
    ProofTextUtil.extractLemmaName("lemma my_lemma: P") shouldBe "my_lemma"
    ProofTextUtil.extractLemmaName("theorem foo_bar [simp]: Q") shouldBe "foo_bar"
  }

  test("extractVarsFromStatement should find variable names") {
    val stmt = """lemma "foo x y = bar y x""""
    val vars = ProofTextUtil.extractVarsFromStatement(stmt)
    vars should contain allOf ("x", "y")
    // Note: Single-letter names like "f" may be included by the heuristic
    // This is acceptable as they're common variable names in math proofs
  }

  test("findReplacement should identify what was replaced") {
    val oldProof = "proof sorry qed"
    val newProof = "proof by simp qed"
    ProofTextUtil.findReplacement(oldProof, newProof) shouldBe "by simp"
  }
}