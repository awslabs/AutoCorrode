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

  test("loadSystemPromptFromHome should honor _index.txt ordering when present") {
    val root = "/virtual/home"
    val systemDir =
      Path.explode(root) + Path.explode("prompts") + Path.explode("system")
    val files = Map(
      "_index.txt" -> "02-b.md\n01-a.md\n",
      "02-b.md" -> "B",
      "01-a.md" -> "A",
      "99-extra.md" -> "EXTRA"
    )

    val rendered = PromptLoader.loadSystemPromptFromHome(
      Some(root),
      dir => dir == systemDir,
      _ => files.keys.toList,
      path => files(path.implode.split('/').last)
    )

    rendered shouldBe "B\n\nA"
  }

  test("loadSystemPromptFromHome should return empty when home missing or system dir absent") {
    PromptLoader.loadSystemPromptFromHome(None, _ => true, _ => Nil, _ => "x") shouldBe ""
    PromptLoader.loadSystemPromptFromHome(Some("/h"), _ => false, _ => Nil, _ => "x") shouldBe ""
  }

  test("parseSystemPromptIndex should ignore blank lines and comments") {
    val parsed = PromptLoader.parseSystemPromptIndex(
      """
        |# comment
        |00_core_operating_rules.md
        |
        |01_isabelle_style.md
        |  # another comment
        |02_tools.md
        |""".stripMargin
    )
    parsed shouldBe List(
      "00_core_operating_rules.md",
      "01_isabelle_style.md",
      "02_tools.md"
    )
  }

  test("loadSystemPromptFromSources should use classpath fallback when home prompts unavailable") {
    var warnings = List.empty[String]
    val resources = Map(
      "prompts/system/_index.txt" ->
        "00_core_operating_rules.md\n01_isabelle_style.md\n",
      "prompts/system/00_core_operating_rules.md" -> "CORE",
      "prompts/system/01_isabelle_style.md" -> "STYLE"
    )

    val rendered = PromptLoader.loadSystemPromptFromSources(
      home = None,
      isDir = _ => false,
      readDir = _ => Nil,
      readFile = _ => "",
      readResource = resources.get,
      warn = msg => warnings = warnings :+ msg
    )

    rendered shouldBe "CORE\n\nSTYLE"
    warnings.exists(_.contains("classpath fallback")) shouldBe true
  }

  test("loadSystemPromptFromSources should fall back to built-in prompt when no sources exist") {
    var warning: Option[String] = None
    val rendered = PromptLoader.loadSystemPromptFromSources(
      home = None,
      isDir = _ => false,
      readDir = _ => Nil,
      readFile = _ => "",
      readResource = _ => None,
      warn = msg => warning = Some(msg)
    )

    rendered should include("Isabelle/HOL proof assistant")
    warning.get should include("built-in fallback")
  }

  test("renderTemplate should substitute placeholders deterministically") {
    val rendered = PromptLoader.renderTemplate("Hello {{name}} from {{place}}", Map(
      "name" -> "Isabelle",
      "place" -> "AutoCorrode"
    ))
    rendered shouldBe "Hello Isabelle from AutoCorrode"
  }
}
