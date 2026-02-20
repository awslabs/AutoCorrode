/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class MarkdownRendererTest extends AnyFunSuite with Matchers {

  test("bold rendering") {
    val html = MarkdownRenderer.toBodyHtml("**bold**")
    html should include("<b>bold</b>")
  }

  test("italic rendering") {
    val html = MarkdownRenderer.toBodyHtml("*italic*")
    html should include("<i>italic</i>")
  }

  test("inline code rendering") {
    val html = MarkdownRenderer.toBodyHtml("`code`")
    html should include("<code")
    html should include("code</code>")
  }

  test("nested bold and italic") {
    val html = MarkdownRenderer.toBodyHtml("**bold *italic* text**")
    html should include("<b>bold <i>italic</i> text</b>")
  }

  test("code fence rendering") {
    val md = "```\nsome code\n```"
    val html = MarkdownRenderer.toBodyHtml(md)
    html should include("<pre")
    html should include("some code")
  }

  test("heading rendering") {
    MarkdownRenderer.toBodyHtml("# H1") should include("<h1")
    MarkdownRenderer.toBodyHtml("## H2") should include("<h2")
    MarkdownRenderer.toBodyHtml("### H3") should include("<h3")
  }

  test("bullet list rendering") {
    val html = MarkdownRenderer.toBodyHtml("- item")
    html should include("•")
    html should include("item")
  }

  test("HTML escaping") {
    val html = MarkdownRenderer.toBodyHtml("<script>alert('xss')</script>")
    html should not include "<script>"
    html should include("&lt;script&gt;")
  }

  test("action code block") {
    val md = "```action:abc123\nby simp\n```"
    val html = MarkdownRenderer.toBodyHtml(md)
    html should include("action:insert:abc123")
    // Check for both keywords (may be syntax highlighted with span tags)
    html should include("by")
    html should include("simp")
  }

  test("mermaid code block should render image or graceful fallback") {
    val prop = "assistant.mermaid.disable_subprocess"
    val prev = Option(System.getProperty(prop))
    System.setProperty(prop, "true")
    val md = "```mermaid\ngraph TD\n  A --> B\n```"
    try {
      val html = MarkdownRenderer.toBodyHtml(md)
      (html.contains("src='mermaid://") ||
        html.contains("Mermaid rendering unavailable")) shouldBe true
    } finally {
      prev match {
        case Some(v) => System.setProperty(prop, v)
        case None    => System.clearProperty(prop)
      }
    }
  }

  test("synthetic image URL detection") {
    MarkdownRenderer.isSyntheticImageUrl("latex://12") shouldBe true
    MarkdownRenderer.isSyntheticImageUrl("mermaid://34") shouldBe true
    MarkdownRenderer.isSyntheticImageUrl("https://example.com/x.png") shouldBe false
  }
}
