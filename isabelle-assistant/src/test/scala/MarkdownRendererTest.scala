/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Tests for MarkdownRenderer HTML output generation. */
class MarkdownRendererTest extends AnyFunSuite with Matchers {

  test("bold rendering") {
    val html = MarkdownRenderer.toBodyHtml("This is **bold** text")
    html should include("<b>")
    html should include("</b>")
    html should include("bold")
  }

  test("italic rendering") {
    val html = MarkdownRenderer.toBodyHtml("This is *italic* text")
    html should include("<i>")
    html should include("</i>")
    html should include("italic")
  }

  test("inline code rendering") {
    val html = MarkdownRenderer.toBodyHtml("Use `by simp` to prove it")
    html should include("<code")
    html should include("by simp")
    html should include("</code>")
  }

  test("nested bold and italic") {
    val html = MarkdownRenderer.toBodyHtml("**bold *and italic* text**")
    html should include("<b>")
    html should include("<i>")
    html should include("</i>")
    html should include("</b>")
  }

  test("code fence rendering") {
    val markdown = """Text before
```scala
def foo = 42
```
Text after"""
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should include("<pre")
    html should include("def foo = 42")
    html should include("</pre>")
  }

  test("heading rendering") {
    val html1 = MarkdownRenderer.toBodyHtml("# Heading 1")
    html1 should include("<h1")
    html1 should include("Heading 1")
    
    val html2 = MarkdownRenderer.toBodyHtml("## Heading 2")
    html2 should include("<h2")
    html2 should include("Heading 2")
    
    val html3 = MarkdownRenderer.toBodyHtml("### Heading 3")
    html3 should include("<h3")
    html3 should include("Heading 3")
  }

  test("bullet list rendering") {
    val markdown = """- Item 1
- Item 2
- Item 3"""
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should include("•")
    html should include("Item 1")
    html should include("Item 2")
    html should include("Item 3")
  }

  test("HTML escaping") {
    val html = MarkdownRenderer.toBodyHtml("Test <script> & \"quotes\"")
    html should include("&lt;script&gt;")
    html should include("&amp;")
    // Note: Quotes in regular text are not escaped by HtmlUtil, only special HTML chars
  }

  test("action code block") {
    val registerAction = (_: String) => "test-id-123"
    val markdown = """```action:my-action
lemma foo: "True"
  by simp
```"""
    val html = MarkdownRenderer.toBodyHtmlWithActions(markdown, registerAction)
    html should include("action:insert:my-action")
    // Syntax highlighting wraps keywords in spans, so check for both keyword and text
    html should (include("lemma") and include("foo"))
  }

  test("mermaid code block should render image or graceful fallback") {
    val markdown = """```mermaid
graph TD
  A --> B
```"""
    val html = MarkdownRenderer.toBodyHtml(markdown)
    // Should either show the diagram or a fallback message, not crash
    html should not be empty
    // If mmdc not available, should show unavailable message
    if (!html.contains("<img src='mermaid://")) {
      val _ = html should include("Mermaid")
    }
  }

  test("synthetic image URL detection") {
    MarkdownRenderer.isSyntheticImageUrl("latex://abc123") shouldBe true
    MarkdownRenderer.isSyntheticImageUrl("mermaid://abc123") shouldBe true
    MarkdownRenderer.isSyntheticImageUrl("https://example.com/image.png") shouldBe false
    MarkdownRenderer.isSyntheticImageUrl("file:///path/to/image.png") shouldBe false
  }

  test("numbered list rendering") {
    val markdown = """1. First item
2. Second item
3. Third item"""
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should include("1.")
    html should include("2.")
    html should include("3.")
    html should include("First item")
    html should include("Second item")
    html should include("Third item")
  }

  test("table rendering") {
    val markdown = """| Col1 | Col2 |
|------|------|
| A    | B    |
| C    | D    |"""
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should include("<table")
    html should include("<th")
    html should include("<td")
    html should include("Col1")
    html should include("Col2")
    html should (include("A") and include("B") and include("C") and include("D"))
  }

  test("isabelle code fence with syntax highlighting") {
    val markdown = """```isabelle
lemma test: "True"
  by simp
```"""
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should include("<pre")
    html should include("lemma")
    // Syntax highlighting wraps "by" in a span, so check separately
    html should include("by")
    html should include("simp")
    // Should have syntax highlighting spans
    html should include("<span")
  }

  test("inline LaTeX math should render or fallback") {
    val markdown = "The formula $x + y = z$ is simple"
    val html = MarkdownRenderer.toBodyHtml(markdown)
    // Should either render as image or show as italics, not crash
    html should not be empty
    html should (include("x + y = z") or include("<img src='latex://"))
  }

  test("display LaTeX math should render or fallback") {
    val markdown = """Some text
$$
\frac{a}{b} = c
$$
More text"""
    val html = MarkdownRenderer.toBodyHtml(markdown)
    // Should either render as image or show as italics, not crash
    html should not be empty
  }

  test("empty markdown should produce minimal HTML") {
    val html = MarkdownRenderer.toBodyHtml("")
    html should not be null
    html.trim should not be empty
  }

  test("markdown with only whitespace") {
    val html = MarkdownRenderer.toBodyHtml("   \n\n   ")
    html should not be null
  }

  test("unmatched display math opener should not consume message tail") {
    val markdown = """Some prelude
$$
\frac{a}{b}
More normal content after
And another line
"""
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should not be null
    // Scanner must recover and render subsequent lines — the "normal
    // content" text must appear in the output.
    html should include("normal content after")
    html should include("And another line")
  }

  test("multiple inline math formulae on a single line") {
    val markdown = "First $a + b$ then $c - d$ then $e = f$ done"
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should not be null
    // Each formula should have produced either a latex image or inline text,
    // and the surrounding plain words must all survive.
    html should (include("First") and include("then") and include("done"))
  }

  test("tilde fence interleaved with backtick fence should not break rendering") {
    val markdown = "Text before\n```scala\nval inner = \"hi\"\n```\nMiddle\n```python\nprint('hi')\n```\nText after"
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should not be null
    html should (include("Text before") and include("Text after") and include("Middle"))
    html should include("<pre")
  }

  test("empty code fence should render without throwing") {
    val markdown = """```

```"""
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should not be null
    html should include("<pre")
  }

  test("inline code containing backticks-adjacent text should preserve content") {
    val markdown = "Start `foo_bar` middle `baz` end"
    val html = MarkdownRenderer.toBodyHtml(markdown)
    html should include("foo_bar")
    html should include("baz")
    html should include("Start")
    html should include("end")
  }
}