/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class TargetParserTest extends AnyFunSuite with Matchers {

  test("parse cursor keywords") {
    TargetParser.parseTarget("cursor", null) shouldBe Some(TargetParser.CurrentCursor)
    TargetParser.parseTarget("current", null) shouldBe Some(TargetParser.CurrentCursor)
  }

  test("parse selection keyword") {
    TargetParser.parseTarget("selection", null) shouldBe Some(TargetParser.CurrentSelection)
  }

  test("parse file:line") {
    TargetParser.parseTarget("Foo.thy:42", null) shouldBe Some(TargetParser.FileLine("Foo.thy", 42))
  }

  test("parse file:range") {
    TargetParser.parseTarget("Foo.thy:10-20", null) shouldBe Some(TargetParser.FileRange("Foo.thy", 10, 20))
  }

  test("parse named element") {
    TargetParser.parseTarget("Foo.thy:my_lemma", null) shouldBe Some(TargetParser.NamedElement("Foo.thy", "my_lemma"))
  }

  test("parse relative position") {
    TargetParser.parseTarget("cursor+5", null) shouldBe Some(TargetParser.RelativePosition(TargetParser.CurrentCursor, 5))
    TargetParser.parseTarget("cursor-3", null) shouldBe Some(TargetParser.RelativePosition(TargetParser.CurrentCursor, -3))
  }

  test("reject invalid target") {
    TargetParser.parseTarget("nonsense", null) shouldBe None
  }

  test("namedElementMatches treats regex metacharacters in the name as literal") {
    val keywords = Seq("lemma")
    // Without Pattern.quote `lem.*` would act as a wildcard matching any
    // lemma name beginning with "lem". With quoting the name must match
    // byte-for-byte, so the call returns false.
    TargetParser.namedElementMatches("lemma lemma_one: x = y", keywords, "lem.*") shouldBe false
    TargetParser.namedElementMatches("lemma lem_one: x = y", keywords, "lem.*") shouldBe false
    // Sanity check: a well-formed name still matches the expected line.
    TargetParser.namedElementMatches("lemma lemma_one: x = y", keywords, "lemma_one") shouldBe true
  }

  test("namedElementMatches requires a word boundary after the name") {
    val keywords = Seq("lemma")
    // "foo" should not match "foobar" even without regex metacharacters.
    TargetParser.namedElementMatches("lemma foobar: x = y", keywords, "foo") shouldBe false
    TargetParser.namedElementMatches("lemma foo: x = y", keywords, "foo") shouldBe true
  }

  test("buildNamedElementPattern matches any of multiple keywords") {
    val keywords = Seq("lemma", "theorem", "definition")
    val pattern = TargetParser.buildNamedElementPattern(keywords, "my_thing")
    pattern.matcher("lemma my_thing: x").matches() shouldBe true
    pattern.matcher("theorem my_thing: x").matches() shouldBe true
    pattern.matcher("definition my_thing :: nat").matches() shouldBe true
    pattern.matcher("corollary my_thing: x").matches() shouldBe false
  }

  test("buildNamedElementPattern escapes metacharacters in keyword strings too") {
    // Not a real scenario for entityKeywords, but defensive: a hypothetical
    // keyword containing `.` should match literally, not as any-char.
    val keywords = Seq("le.mma")
    val pattern = TargetParser.buildNamedElementPattern(keywords, "foo")
    pattern.matcher("le.mma foo: x").matches() shouldBe true
    pattern.matcher("leXmma foo: x").matches() shouldBe false
  }

  test("formatTarget round-trips") {
    val targets = List(
      TargetParser.CurrentCursor,
      TargetParser.CurrentSelection,
      TargetParser.FileLine("T.thy", 5),
      TargetParser.FileRange("T.thy", 1, 10)
    )
    for (t <- targets) {
      TargetParser.formatTarget(t) should not be empty
    }
  }
}
