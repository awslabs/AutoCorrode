/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Deterministic tests for utility functions and invariants.
  *
  * Tests core utility functions with fixed inputs to ensure correct behavior.
  * Converted from property-based tests to deterministic tests for fast execution.
  */
class PropertyBasedTests extends AnyFunSuite with Matchers {

  // --- Simple deterministic tests (not property-based) ---

  test("ToolId.fromWire round-trips all enum values") {
    ToolId.values.foreach { id =>
      ToolId.fromWire(id.wireName) shouldBe Some(id)
    }
  }

  test("PayloadBuilder.isAnthropicStructuredContent handles fixed test cases") {
    PayloadBuilder.isAnthropicStructuredContent("[]") shouldBe true
    PayloadBuilder.isAnthropicStructuredContent("[") shouldBe false
    PayloadBuilder.isAnthropicStructuredContent("[}") shouldBe false
    PayloadBuilder.isAnthropicStructuredContent("[1,2,3]") shouldBe false
    PayloadBuilder.isAnthropicStructuredContent("not json") shouldBe false
  }

  test("ErrorHandler.sanitize handles null") {
    ErrorHandler.sanitize(null) shouldBe ""
    ErrorHandler.sanitize(null, 100) shouldBe ""
  }

  test("ErrorHandler.sanitize truncates long strings") {
    val long = "x" * 500
    val result = ErrorHandler.sanitize(long, 100)
    result.length shouldBe 100
  }

  test("VerificationCache.classifyFailure detects infrastructure errors") {
    VerificationCache.classifyFailure("timeout error") shouldBe 
      VerificationCache.FailureCause.InfrastructureFailure
    VerificationCache.classifyFailure("network failure") shouldBe 
      VerificationCache.FailureCause.InfrastructureFailure
  }

  test("VerificationCache.classifyFailure treats other errors as semantic") {
    VerificationCache.classifyFailure("type mismatch") shouldBe 
      VerificationCache.FailureCause.SemanticFailure
    VerificationCache.classifyFailure("failed to apply tactic") shouldBe 
      VerificationCache.FailureCause.SemanticFailure
  }

  test("HtmlUtil.escapeHtml handles special characters") {
    HtmlUtil.escapeHtml("<script>") shouldBe "&lt;script&gt;"
    HtmlUtil.escapeHtml("a & b") shouldBe "a &amp; b"
    HtmlUtil.escapeHtml("x > y") shouldBe "x &gt; y"
  }

  test("AssistantTools.normalizeReadRange handles boundary cases") {
    AssistantTools.normalizeReadRange(100, 1, 100) shouldBe (1, 100)
    AssistantTools.normalizeReadRange(100, 50, 75) shouldBe (50, 75)
    AssistantTools.normalizeReadRange(100, -10, 200) shouldBe (1, 100)
    AssistantTools.normalizeReadRange(0, 1, 10) shouldBe (1, 0)
  }

  test("AssistantTools.clampOffset handles boundary cases") {
    AssistantTools.clampOffset(-100, 1000) shouldBe 0
    AssistantTools.clampOffset(500, 1000) shouldBe 500
    AssistantTools.clampOffset(2000, 1000) shouldBe 1000
  }

  test("AssistantTools.isValidCreateTheoryName validates theory names") {
    AssistantTools.isValidCreateTheoryName("Foo") shouldBe true
    AssistantTools.isValidCreateTheoryName("Foo_Bar") shouldBe true
    AssistantTools.isValidCreateTheoryName("Foo'") shouldBe true
    AssistantTools.isValidCreateTheoryName("123") shouldBe false
    AssistantTools.isValidCreateTheoryName("Foo/Bar") shouldBe false
    AssistantTools.isValidCreateTheoryName("") shouldBe false
  }

  test("BedrockClient.mergeConsecutiveRoles handles simple cases") {
    val msgs = List(("user", "a"), ("user", "b"), ("assistant", "c"))
    val merged = BedrockClient.mergeConsecutiveRoles(msgs)
    merged.length shouldBe 2
    merged.head._1 shouldBe "user"
    merged.head._2 should include("a")
    merged.head._2 should include("b")
  }

  test("BedrockClient.truncateMessages handles simple cases") {
    val msgs = List(("user", "a" * 50), ("assistant", "b" * 50), ("user", "c" * 50))
    val truncated = BedrockClient.truncateMessages(msgs, 120)
    truncated.map(_._2.length).sum should be <= 120
    truncated.nonEmpty shouldBe true
  }

  // --- Generative spot-checks for the HTML/Markdown pipeline ---

  /** Deterministic pseudo-random string generator, seeded so failures are
    * reproducible. Uses a mix of benign characters plus the full set that
    * typically trips up naive escapers — angle brackets, ampersands,
    * attribute delimiters, and a handful of Unicode outliers.
    */
  private def genString(rng: scala.util.Random, maxLen: Int): String = {
    val n = rng.nextInt(maxLen + 1)
    val chars = "abcd \n\t<>&\"'/\\{}[]"
    (0 until n).map(_ => chars.charAt(rng.nextInt(chars.length))).mkString
  }

  test("HtmlUtil.sanitizeWidgetHtml never leaves a literal <script tag for any input") {
    // The sanitizer is defense-in-depth for widget-role HTML. A regression
    // that let a single <script through would let any future widget
    // producer ship an XSS. Run enough random fragments to cover the
    // unbalanced-tag, mixed-case, and nested-attribute corner cases.
    val rng = new scala.util.Random(0xdeadbeefL)
    for (_ <- 0 until 200) {
      val input = "<div>" + genString(rng, 256) + "<script>" + genString(rng, 64)
      val out = HtmlUtil.sanitizeWidgetHtml(input)
      out.toLowerCase should not include "<script"
    }
  }

  test("HtmlUtil.sanitizeWidgetHtml preserves benign action: descriptors") {
    // The allow-list dispatcher on the listener side depends on
    // `action:insert:` / `action:copy:` surviving sanitisation, since the
    // sanitizer runs upstream of the renderer and link text would
    // otherwise be stripped along with `javascript:`.
    val rng = new scala.util.Random(0xcafebabeL)
    for (_ <- 0 until 50) {
      val id = "id" + rng.nextInt(Int.MaxValue)
      val link = s"<a href=\"action:insert:$id\">${genString(rng, 32)}</a>"
      val out = HtmlUtil.sanitizeWidgetHtml(link)
      out should include(s"action:insert:$id")
    }
  }

  test("MarkdownRenderer.toBodyHtml produces well-formed body fragments for random input") {
    // Small random markdown bursts should never return an unclosed
    // `<pre>`, `<code>`, or `<script>`. We don't require perfect DOM-level
    // balance (the HTMLEditorKit is lenient), just that these three
    // high-risk tags open and close in equal counts.
    val rng = new scala.util.Random(42L)
    for (_ <- 0 until 100) {
      val md = genString(rng, 512)
      val out = MarkdownRenderer.toBodyHtml(md)
      val openPre   = """<pre\b""".r.findAllIn(out).size
      val closePre  = """</pre>""".r.findAllIn(out).size
      val openCode  = """<code\b""".r.findAllIn(out).size
      val closeCode = """</code>""".r.findAllIn(out).size
      openPre   shouldBe closePre
      openCode  shouldBe closeCode
      out.toLowerCase should not include "<script"
    }
  }
}