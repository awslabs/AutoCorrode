/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Parser that pulls suggested Isabelle-style identifiers out of an LLM
  * response formatted as `NAME: <ident>`. The parser drops malformed lines
  * rather than failing the whole call, and caps results to avoid a runaway
  * bubble.
  */
class SuggestNameActionTest extends AnyFunSuite with Matchers {

  test("parseNameSuggestions extracts NAME: entries in order and deduplicates") {
    val response =
      """Some preamble.
        |NAME: foo
        |NAME: bar_baz
        |NAME: foo    # duplicate — should be dropped
        |more prose
        |NAME: qux'
        |""".stripMargin
    SuggestNameAction.parseNameSuggestions(response) shouldBe List("foo", "bar_baz", "qux'")
  }

  test("parseNameSuggestions rejects non-identifier-shaped names") {
    // Identifiers must start with a letter and contain only word chars or
    // primes; `9bad` and `_under` both fail the leading-char rule.
    val response =
      """NAME: 9bad
        |NAME: _under
        |NAME: goodname
        |""".stripMargin
    SuggestNameAction.parseNameSuggestions(response) shouldBe List("goodname")
  }

  test("parseNameSuggestions caps at 5 suggestions") {
    val response = (1 to 10).map(i => s"NAME: name$i").mkString("\n")
    val out = SuggestNameAction.parseNameSuggestions(response)
    out.length shouldBe 5
    out shouldBe List("name1", "name2", "name3", "name4", "name5")
  }

  test("parseNameSuggestions returns empty for a response with no NAME: entries") {
    SuggestNameAction.parseNameSuggestions("no matches here") shouldBe Nil
    SuggestNameAction.parseNameSuggestions("")                 shouldBe Nil
  }
}
