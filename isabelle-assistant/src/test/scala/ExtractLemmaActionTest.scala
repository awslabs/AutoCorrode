/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Tests for `ExtractLemmaAction.parseStructuredExtraction` — the decoder
  * that maps the LLM's tool-use arguments back into an `ExtractionResult`.
  * This helper is the hinge between the Bedrock tool_choice response and
  * the downstream verification retry loop, so a regression would surface
  * as a silent "no lemma extracted" in the UI.
  */
class ExtractLemmaActionTest extends AnyFunSuite with Matchers {

  import ResponseParser._

  test("parseStructuredExtraction returns ExtractionResult with name from `lemma` keyword") {
    val args: ToolArgs = Map(
      "extracted_lemma" -> StringValue("lemma foo_aux: \"P x\" by simp"),
      "updated_proof"   -> StringValue("using foo_aux by blast")
    )
    val out = ExtractLemmaAction.parseStructuredExtraction(args)
    out.isDefined shouldBe true
    out.get.lemmaName shouldBe "foo_aux"
    out.get.extractedLemma should include("lemma foo_aux")
    out.get.updatedProof  shouldBe "using foo_aux by blast"
  }

  test("parseStructuredExtraction recognises `theorem` as well as `lemma`") {
    val args: ToolArgs = Map(
      "extracted_lemma" -> StringValue("theorem useful_thm: \"Q y\" ..."),
      "updated_proof"   -> StringValue("by (rule useful_thm)")
    )
    val out = ExtractLemmaAction.parseStructuredExtraction(args)
    out.get.lemmaName shouldBe "useful_thm"
  }

  test("parseStructuredExtraction defaults name to 'extracted' when no keyword is detected") {
    // Robustness: the LLM might return a bare statement without a leading
    // `lemma`/`theorem`. We still return a result but flag it via the
    // default name so the caller can decide what to do.
    val args: ToolArgs = Map(
      "extracted_lemma" -> StringValue("\"P x\" is the goal"),
      "updated_proof"   -> StringValue("sorry")
    )
    val out = ExtractLemmaAction.parseStructuredExtraction(args)
    out.get.lemmaName shouldBe "extracted"
  }

  test("parseStructuredExtraction returns None when required fields are missing") {
    ExtractLemmaAction.parseStructuredExtraction(Map.empty) shouldBe None
    ExtractLemmaAction.parseStructuredExtraction(
      Map("extracted_lemma" -> StringValue("lemma foo: True .."))
    ) shouldBe None
    ExtractLemmaAction.parseStructuredExtraction(
      Map("updated_proof" -> StringValue("by auto"))
    ) shouldBe None
  }
}
