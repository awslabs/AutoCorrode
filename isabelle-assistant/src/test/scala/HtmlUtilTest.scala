/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Tests for HtmlUtil.escapeHtml. XSS defence rests on ampersand being
  * escaped first so that later substitutions can't re-introduce live
  * entities, and on quotes being escaped so the output is safe inside
  * attribute values as well as text content. */
class HtmlUtilTest extends AnyFunSuite with Matchers {

  test("escapeHtml leaves plain text unchanged") {
    HtmlUtil.escapeHtml("hello world") shouldBe "hello world"
    HtmlUtil.escapeHtml("") shouldBe ""
  }

  test("escapeHtml converts each special character") {
    HtmlUtil.escapeHtml("<") shouldBe "&lt;"
    HtmlUtil.escapeHtml(">") shouldBe "&gt;"
    HtmlUtil.escapeHtml("\"") shouldBe "&quot;"
    HtmlUtil.escapeHtml("'") shouldBe "&#39;"
    HtmlUtil.escapeHtml("&") shouldBe "&amp;"
  }

  test("escapeHtml neutralises a script-tag injection attempt") {
    val payload = "<script>alert('xss')</script>"
    val escaped = HtmlUtil.escapeHtml(payload)
    escaped should not include "<script"
    escaped should not include "</script>"
    escaped should include("&lt;script&gt;")
    escaped should include("&lt;/script&gt;")
  }

  test("escapeHtml escapes attribute-breakers for quoted attribute contexts") {
    val payload = "\" onclick=\"alert(1)"
    val escaped = HtmlUtil.escapeHtml(payload)
    escaped should not include "\""
    escaped should include("&quot;")
    // Confirm the literal content is still recoverable in escaped form.
    escaped should include("onclick=")
  }

  test("escapeHtml escapes single quotes for single-quoted attribute contexts") {
    val payload = "' onload='x"
    val escaped = HtmlUtil.escapeHtml(payload)
    escaped should not include "'"
    escaped should include("&#39;")
  }

  test("escapeHtml escapes ampersand before consuming angle brackets") {
    // The order matters: if we escaped `<` before `&`, then an input like
    // `&<` would produce `&&lt;` and a subsequent innerHTML write could
    // re-decode a live entity. The ampersand-first rule keeps `&lt;`
    // literal in the output.
    HtmlUtil.escapeHtml("&<") shouldBe "&amp;&lt;"
    HtmlUtil.escapeHtml("&amp;") shouldBe "&amp;amp;"
  }

  test("escapeHtml handles a mixed realistic payload") {
    val payload = "Tom & Jerry said \"hi\" to <the> 'world'."
    HtmlUtil.escapeHtml(payload) shouldBe
      "Tom &amp; Jerry said &quot;hi&quot; to &lt;the&gt; &#39;world&#39;."
  }

  test("escapeHtml preserves non-ASCII characters unchanged") {
    // Non-special characters (including Unicode) are not touched.
    HtmlUtil.escapeHtml("λ-calculus ∀x.P(x)") shouldBe "λ-calculus ∀x.P(x)"
    HtmlUtil.escapeHtml("日本語") shouldBe "日本語"
  }

  test("escapeHtml is idempotent on already-escaped output for angle brackets") {
    val once = HtmlUtil.escapeHtml("<a>")
    val twice = HtmlUtil.escapeHtml(once)
    // The second escape doubles the ampersand in each entity, which is
    // the intended, reversible behaviour — reliably escaping shouldn't
    // silently drop characters, but it also must not leave a live
    // character intact. The key invariant is that `<` and `>` never
    // appear in the output.
    twice should not include "<"
    twice should not include ">"
  }

  test("accessibleGlyph marks the glyph as aria-hidden") {
    val html = HtmlUtil.accessibleGlyph("✓", "Done", "#4caf50")
    html should include("aria-hidden='true'")
    html should include("✓")
  }

  test("accessibleGlyph embeds the textual label for screen readers") {
    val html = HtmlUtil.accessibleGlyph("✗", "Irrelevant", "#616161")
    html should include("Irrelevant")
  }

  test("accessibleGlyph keeps the textual label off-screen via clip-rect") {
    val html = HtmlUtil.accessibleGlyph("●", "Next", "#1976d2")
    // The label span should be visually hidden so it doesn't affect layout.
    html should include("clip:rect(0 0 0 0)")
  }

  test("accessibleGlyph escapes HTML-special characters in the label") {
    val html = HtmlUtil.accessibleGlyph(">", "In progress <50%>", "#ff9800")
    html should include("&gt;")
    html should include("&lt;50%&gt;")
    html should not include "<50%>"
  }

  test("sanitizeWidgetHtml removes paired <script> elements") {
    val input = "<div>hi <script>alert(1)</script> there</div>"
    val out = HtmlUtil.sanitizeWidgetHtml(input)
    out should not include "<script"
    out should not include "alert(1)"
    out should include("<div>")
    out should include("there</div>")
  }

  test("sanitizeWidgetHtml removes unterminated <script> tags") {
    val input = "<div>hi <script src='evil.js'>"
    val out = HtmlUtil.sanitizeWidgetHtml(input)
    out should not include "<script"
    out should include("<div>")
  }

  test("sanitizeWidgetHtml removes <iframe> elements") {
    val input = "<iframe src='//evil'></iframe>ok"
    val out = HtmlUtil.sanitizeWidgetHtml(input)
    out should not include "<iframe"
    out should include("ok")
  }

  test("sanitizeWidgetHtml neutralises javascript: URL schemes") {
    val input = "<a href='javascript:alert(1)'>click</a>"
    val out = HtmlUtil.sanitizeWidgetHtml(input)
    out should not include "javascript:"
    out should include("blocked:")
    out should include("click")
  }

  test("sanitizeWidgetHtml strips inline event-handler attributes") {
    val input = "<div onclick='doit()'>x</div>"
    val out = HtmlUtil.sanitizeWidgetHtml(input)
    out should not include "onclick="
    out should include("data-blocked=")
    out should include(">x</div>")
  }

  test("sanitizeWidgetHtml preserves legitimate action: links untouched") {
    val input = "<a href='action:insert:abc123'>Run</a>"
    val out = HtmlUtil.sanitizeWidgetHtml(input)
    out shouldBe input
  }

  test("sanitizeWidgetHtml handles null/empty input safely") {
    HtmlUtil.sanitizeWidgetHtml(null) shouldBe ""
    HtmlUtil.sanitizeWidgetHtml("") shouldBe ""
  }

  test("sanitizeWidgetHtml is case-insensitive for tag names and schemes") {
    val input = "<SCRIPT>x</SCRIPT><a href='JavaScript:1'>L</a><div OnClick='y'>z</div>"
    val out = HtmlUtil.sanitizeWidgetHtml(input)
    out should not include "SCRIPT"
    out should not include "JavaScript:"
    out should not include "OnClick="
  }
}
