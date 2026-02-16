/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle.Path
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class PromptLoaderTest extends AnyFunSuite with Matchers {

  test("assistantHomeFrom should return home when environment is set") {
    var warned = false
    val home = PromptLoader.assistantHomeFrom(
      _ => "/tmp/assistant-home",
      _ => warned = true
    )
    home shouldBe Some("/tmp/assistant-home")
    warned shouldBe false
  }

  test("assistantHomeFrom should warn and return None when environment is missing") {
    var warning: Option[String] = None
    val home = PromptLoader.assistantHomeFrom(
      _ => "",
      msg => warning = Some(msg)
    )
    home shouldBe None
    warning should not be empty
    warning.get should include("ISABELLE_ASSISTANT_HOME")
  }

  test("loadSystemPromptFromHome should concatenate sorted markdown files only") {
    val root = "/virtual/home"
    val systemDir = Path.explode(root) + Path.explode("prompts") + Path.explode("system")
    val files = Map(
      "02-b.md" -> "B",
      "01-a.md" -> "A",
      "notes.txt" -> "ignore"
    )

    val rendered = PromptLoader.loadSystemPromptFromHome(
      Some(root),
      dir => dir == systemDir,
      _ => files.keys.toList,
      path => files(path.implode.split('/').last)
    )

    rendered shouldBe "A\n\nB"
  }

  test("loadSystemPromptFromHome should return empty when home missing or system dir absent") {
    PromptLoader.loadSystemPromptFromHome(None, _ => true, _ => Nil, _ => "x") shouldBe ""
    PromptLoader.loadSystemPromptFromHome(Some("/h"), _ => false, _ => Nil, _ => "x") shouldBe ""
  }

  test("renderTemplate should substitute placeholders deterministically") {
    val rendered = PromptLoader.renderTemplate("Hello {{name}} from {{place}}", Map(
      "name" -> "Isabelle",
      "place" -> "AutoCorrode"
    ))
    rendered shouldBe "Hello Isabelle from AutoCorrode"
  }
}
