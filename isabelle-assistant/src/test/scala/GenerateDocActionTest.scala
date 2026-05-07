/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Pure-helper coverage for `GenerateDocAction.detectCommandType` — the
  * string-based fallback used when PIDE span lookup is unavailable.
  *
  * Exercising the fallback in isolation matters because every test that
  * loads a full Isabelle/jEdit runtime is prohibitively slow for unit-test
  * CI, yet the fallback is the only path reachable from a buffer-less
  * caller (context menus on unsaved text, LLM tool handlers that were
  * given source directly).
  */
class GenerateDocActionTest extends AnyFunSuite with Matchers {

  test("detectCommandType recognises core documentable keywords") {
    GenerateDocAction.detectCommandType("definition foo where ...") shouldBe Some("definition")
    GenerateDocAction.detectCommandType("lemma foo: ...")           shouldBe Some("lemma")
    GenerateDocAction.detectCommandType("theorem foo: ...")         shouldBe Some("theorem")
    GenerateDocAction.detectCommandType("datatype 'a tree = ...")   shouldBe Some("datatype")
    GenerateDocAction.detectCommandType("abbreviation foo where")   shouldBe Some("abbreviation")
    GenerateDocAction.detectCommandType("fun f where ...")          shouldBe Some("fun")
  }

  test("detectCommandType returns None for non-documentable or empty source") {
    GenerateDocAction.detectCommandType("apply auto")    shouldBe None
    GenerateDocAction.detectCommandType("by simp")       shouldBe None
    GenerateDocAction.detectCommandType("")              shouldBe None
    GenerateDocAction.detectCommandType("   \n\t   ")    shouldBe None
  }

  test("detectCommandType requires a token boundary, not a substring match") {
    // `automatic` must not match the `auto` proof method (documentable
    // keywords don't overlap with proof methods today, but guarding against
    // substring-matching regressions is cheap). Check with `lemmary`, which
    // would falsely match `lemma` if boundary handling broke.
    GenerateDocAction.detectCommandType("lemmary foo: ...")  shouldBe None
    GenerateDocAction.detectCommandType("definitional")      shouldBe None
  }
}
