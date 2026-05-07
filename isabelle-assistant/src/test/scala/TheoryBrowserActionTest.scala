/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Pure-helper coverage for `TheoryBrowserAction`. The happy-path run
  * paths all dispatch to `IQMcpClient`, which is infeasible to exercise
  * without a live Isabelle server, but the string-shaping helpers are all
  * side-effect-free and easy to nail down.
  */
class TheoryBrowserActionTest extends AnyFunSuite with Matchers {

  test("baseName strips directory components") {
    TheoryBrowserAction.baseName("/tmp/foo/Bar.thy") shouldBe "Bar.thy"
    TheoryBrowserAction.baseName("Bar.thy")          shouldBe "Bar.thy"
  }

  test("stripNumberPrefixes drops leading '\\d+:' and a highlight arrow") {
    // Highlighted lines come back from MCP prefixed with `→ N:`; untouched
    // lines just as `N:`. The helper peels both to return human-readable
    // source for display in the chat panel.
    val raw =
      """1: theory Foo
        |→ 2: begin
        |3: lemma bar: True by auto""".stripMargin
    val cleaned = TheoryBrowserAction.stripNumberPrefixes(raw)
    cleaned shouldBe
      """ theory Foo
        | begin
        | lemma bar: True by auto""".stripMargin
  }

  test("stripNumberPrefixes leaves lines that do not look like a numbered listing") {
    val text = "lemma foo: True by auto"
    TheoryBrowserAction.stripNumberPrefixes(text) shouldBe text
  }

  test("firstHighlightedOrFirstLine prefers the arrow-prefixed line") {
    val text =
      """1: theory Foo
        |→ 2: imports Main
        |3: begin""".stripMargin
    // The arrow line wins regardless of position; the numeric prefix is
    // stripped from the returned payload.
    TheoryBrowserAction.firstHighlightedOrFirstLine(text) shouldBe "imports Main"
  }

  test("firstHighlightedOrFirstLine falls back to the first line when no arrow") {
    val text =
      """1: theory Foo
        |2: imports Main""".stripMargin
    TheoryBrowserAction.firstHighlightedOrFirstLine(text) shouldBe "theory Foo"
  }

  test("firstHighlightedOrFirstLine returns empty string for empty input") {
    TheoryBrowserAction.firstHighlightedOrFirstLine("")          shouldBe ""
    TheoryBrowserAction.firstHighlightedOrFirstLine("   \n\t  ") shouldBe ""
  }
}
