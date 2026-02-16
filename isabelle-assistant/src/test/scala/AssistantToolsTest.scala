/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for AssistantTools input sanitization and tool definitions.
 * Tests the tool definition structure without requiring jEdit runtime.
 */
class AssistantToolsTest extends AnyFunSuite with Matchers {

  test("tool definitions should have unique names") {
    val names = AssistantTools.tools.map(_.name)
    names.distinct.length shouldBe names.length
  }

  test("all tools should have non-empty descriptions") {
    for (tool <- AssistantTools.tools) {
      tool.description should not be empty
    }
  }

  test("required params should have descriptions") {
    for (tool <- AssistantTools.tools; param <- tool.params if param.required) {
      param.description should not be empty
    }
  }

  test("tool param types should be valid JSON schema types") {
    val validTypes = Set("string", "integer", "number", "boolean", "array", "object")
    for (tool <- AssistantTools.tools; param <- tool.params) {
      validTypes should contain(param.typ)
    }
  }

  test("expected tools should be defined") {
    val toolNames = AssistantTools.tools.map(_.name).toSet
    toolNames should contain("read_theory")
    toolNames should contain("list_theories")
    toolNames should contain("search_in_theory")
    toolNames should contain("get_goal_state")
    toolNames should contain("get_proof_context")
    toolNames should contain("find_theorems")
    toolNames should contain("verify_proof")
    toolNames should contain("run_sledgehammer")
  }

  test("read_theory should require theory param") {
    val tool = AssistantTools.tools.find(_.name == "read_theory").get
    val required = tool.params.filter(_.required).map(_.name)
    required should contain("theory")
  }

  test("verify_proof should require proof param") {
    val tool = AssistantTools.tools.find(_.name == "verify_proof").get
    val required = tool.params.filter(_.required).map(_.name)
    required should contain("proof")
  }

  test("run_nitpick should exist and require no params") {
    val tool = AssistantTools.tools.find(_.name == "run_nitpick")
    tool should not be empty
    tool.get.params shouldBe empty
  }

  test("run_quickcheck should exist and require no params") {
    val tool = AssistantTools.tools.find(_.name == "run_quickcheck")
    tool should not be empty
    tool.get.params shouldBe empty
  }

  test("get_type should exist and require no params") {
    val tool = AssistantTools.tools.find(_.name == "get_type")
    tool should not be empty
    tool.get.params shouldBe empty
  }

  test("get_command_text should exist and require no params") {
    val tool = AssistantTools.tools.find(_.name == "get_command_text")
    tool should not be empty
    tool.get.params shouldBe empty
  }

  test("get_errors should exist and require no params") {
    val tool = AssistantTools.tools.find(_.name == "get_errors")
    tool should not be empty
    tool.get.params shouldBe empty
  }

  test("get_definitions should exist and require names param") {
    val tool = AssistantTools.tools.find(_.name == "get_definitions")
    tool should not be empty
    val required = tool.get.params.filter(_.required).map(_.name)
    required should contain("names")
    required.length shouldBe 1
  }

  test("execute_step should exist and require proof param") {
    val tool = AssistantTools.tools.find(_.name == "execute_step")
    tool should not be empty
    val required = tool.get.params.filter(_.required).map(_.name)
    required should contain("proof")
    required.length shouldBe 1
  }

  test("trace_simplifier should exist with optional method param") {
    val tool = AssistantTools.tools.find(_.name == "trace_simplifier")
    tool should not be empty
    val params = tool.get.params
    params.length shouldBe 1
    params.head.name shouldBe "method"
    params.head.required shouldBe false
  }

  test("all tools should have exactly 28 entries") {
    AssistantTools.tools.length shouldBe 28
  }

  test("tool names should follow naming convention") {
    val validNamePattern = "^[a-z_]+$".r
    for (tool <- AssistantTools.tools) {
      validNamePattern.findFirstIn(tool.name) should not be empty
    }
  }

  test("no tool should have duplicate param names") {
    for (tool <- AssistantTools.tools) {
      val paramNames = tool.params.map(_.name)
      paramNames.distinct.length shouldBe paramNames.length
    }
  }

  test("all required params should be of string or integer type") {
    for (tool <- AssistantTools.tools; param <- tool.params if param.required) {
      Set("string", "integer") should contain(param.typ)
    }
  }

  test("tools with no params should have empty param list not null") {
    val noParamTools = List("list_theories", "get_goal_state", "get_proof_context",
      "run_sledgehammer", "run_nitpick", "run_quickcheck", "get_type",
      "get_command_text", "get_errors")
    for (toolName <- noParamTools) {
      val tool = AssistantTools.tools.find(_.name == toolName).get
      tool.params should not be null
      tool.params shouldBe empty
    }
  }

  test("tools with optional params should not mark them as required") {
    val tool = AssistantTools.tools.find(_.name == "read_theory").get
    val optionalParams = tool.params.filterNot(_.required)
    optionalParams should not be empty
    optionalParams.map(_.name) should contain("start_line")
    optionalParams.map(_.name) should contain("end_line")
  }

  test("search_in_theory should have exactly 2 required and 1 optional param") {
    val tool = AssistantTools.tools.find(_.name == "search_in_theory").get
    tool.params.length shouldBe 3
    tool.params.count(_.required) shouldBe 2
    tool.params.count(!_.required) shouldBe 1
  }

  test("find_theorems should have 1 required and 1 optional param") {
    val tool = AssistantTools.tools.find(_.name == "find_theorems").get
    tool.params.length shouldBe 2
    tool.params.count(_.required) shouldBe 1
    tool.params.find(_.required).get.name shouldBe "pattern"
    tool.params.find(!_.required).get.name shouldBe "max_results"
  }

  test("integer params should be for pagination, limits, or line numbers") {
    val integerParams = for {
      tool <- AssistantTools.tools
      param <- tool.params if param.typ == "integer"
    } yield (tool.name, param.name)

    integerParams should not be empty
    for ((toolName, paramName) <- integerParams) {
      val validIntParams = Set("start_line", "end_line", "max_results", "line")
      validIntParams should contain(paramName)
    }
  }

  test("all string params should have non-empty descriptions") {
    for {
      tool <- AssistantTools.tools
      param <- tool.params if param.typ == "string"
    } {
      param.description should not be empty
      param.description.length should be > 10
    }
  }

  test("tools descriptions should mention I/Q requirement if needed") {
    val iqTools = List("find_theorems", "verify_proof", "run_sledgehammer",
      "run_nitpick", "run_quickcheck", "get_definitions", "execute_step", "trace_simplifier")
    for (toolName <- iqTools) {
      val tool = AssistantTools.tools.find(_.name == toolName).get
      tool.description.toLowerCase should (include("i/q") or include("requires i/q"))
    }
  }

  test("tools not requiring I/Q should not mention it") {
    val nonIqTools = List("read_theory", "list_theories", "search_in_theory",
      "get_goal_state", "get_type", "get_command_text", "get_errors")
    for (toolName <- nonIqTools) {
      val tool = AssistantTools.tools.find(_.name == toolName).get
      tool.description.toLowerCase should not include "i/q"
    }
  }

  test("get_proof_context should mention I/Q in description") {
    val tool = AssistantTools.tools.find(_.name == "get_proof_context").get
    tool.description should not include "I/Q"
  }

  test("get_proof_block should exist and require no params") {
    val tool = AssistantTools.tools.find(_.name == "get_proof_block")
    tool should not be empty
    tool.get.params shouldBe empty
  }

  test("get_context_info should exist and require no params") {
    val tool = AssistantTools.tools.find(_.name == "get_context_info")
    tool should not be empty
    tool.get.params shouldBe empty
  }

  test("search_all_theories should exist with required pattern and optional max_results") {
    val tool = AssistantTools.tools.find(_.name == "search_all_theories")
    tool should not be empty
    val params = tool.get.params
    params.length shouldBe 2
    val required = params.filter(_.required)
    required.length shouldBe 1
    required.head.name shouldBe "pattern"
    val optional = params.filterNot(_.required)
    optional.length shouldBe 1
    optional.head.name shouldBe "max_results"
  }

  test("get_dependencies should exist and require theory param") {
    val tool = AssistantTools.tools.find(_.name == "get_dependencies")
    tool should not be empty
    val required = tool.get.params.filter(_.required).map(_.name)
    required should contain("theory")
    required.length shouldBe 1
  }

  test("get_warnings should exist and require no params") {
    val tool = AssistantTools.tools.find(_.name == "get_warnings")
    tool should not be empty
    tool.get.params shouldBe empty
  }

  test("set_cursor_position should exist and require line param") {
    val tool = AssistantTools.tools.find(_.name == "set_cursor_position")
    tool should not be empty
    val required = tool.get.params.filter(_.required).map(_.name)
    required should contain("line")
    required.length shouldBe 1
    val lineParam = tool.get.params.find(_.name == "line").get
    lineParam.typ shouldBe "integer"
  }

  test("navigation tools should not require I/Q") {
    val navTools = List("get_proof_block", "get_context_info", "search_all_theories",
      "get_dependencies", "get_warnings", "set_cursor_position")
    for (toolName <- navTools) {
      val tool = AssistantTools.tools.find(_.name == toolName).get
      tool.description.toLowerCase should not include "i/q"
    }
  }

  test("tools with integer params for line numbers should validate properly") {
    val lineParamTools = List("set_cursor_position")
    for (toolName <- lineParamTools) {
      val tool = AssistantTools.tools.find(_.name == toolName).get
      val lineParam = tool.params.find(_.name == "line")
      lineParam should not be empty
      lineParam.get.typ shouldBe "integer"
      lineParam.get.required shouldBe true
    }
  }

  test("search tools should all have pattern param") {
    val searchTools = List("search_in_theory", "search_all_theories", "find_theorems")
    for (toolName <- searchTools) {
      val tool = AssistantTools.tools.find(_.name == toolName).get
      val patternParam = tool.params.find(_.name == "pattern")
      patternParam should not be empty
      patternParam.get.required shouldBe true
      patternParam.get.typ shouldBe "string"
    }
  }

  test("dependency tool should have theory param") {
    val tool = AssistantTools.tools.find(_.name == "get_dependencies").get
    val theoryParam = tool.params.find(_.name == "theory")
    theoryParam should not be empty
    theoryParam.get.required shouldBe true
  }

  test("edit_theory should exist with required params") {
    val tool = AssistantTools.tools.find(_.name == "edit_theory")
    tool should not be empty
    val required = tool.get.params.filter(_.required).map(_.name).toSet
    required should contain("theory")
    required should contain("operation")
    required should contain("start_line")
    required.size shouldBe 3
  }

  test("edit_theory should have optional end_line and text params") {
    val tool = AssistantTools.tools.find(_.name == "edit_theory").get
    val optional = tool.params.filterNot(_.required).map(_.name).toSet
    optional should contain("end_line")
    optional should contain("text")
  }

  test("try_methods should exist and require methods param") {
    val tool = AssistantTools.tools.find(_.name == "try_methods")
    tool should not be empty
    val required = tool.get.params.filter(_.required).map(_.name)
    required should contain("methods")
    required.length shouldBe 1
    tool.get.description.toLowerCase should include("i/q")
  }

  test("get_entities should exist and require theory param") {
    val tool = AssistantTools.tools.find(_.name == "get_entities")
    tool should not be empty
    val required = tool.get.params.filter(_.required).map(_.name)
    required should contain("theory")
    required.length shouldBe 1
  }

  test("web_search should exist with required query and optional max_results") {
    val tool = AssistantTools.tools.find(_.name == "web_search")
    tool should not be empty
    val params = tool.get.params
    params.length shouldBe 2
    val required = params.filter(_.required)
    required.length shouldBe 1
    required.head.name shouldBe "query"
    val optional = params.filterNot(_.required)
    optional.head.name shouldBe "max_results"
  }

  test("create_theory should exist with required name param") {
    val tool = AssistantTools.tools.find(_.name == "create_theory")
    tool should not be empty
    val required = tool.get.params.filter(_.required).map(_.name)
    required should contain("name")
    required.length shouldBe 1
    val optional = tool.get.params.filterNot(_.required).map(_.name).toSet
    optional should contain("imports")
    optional should contain("content")
  }

  test("open_theory should exist and require path param") {
    val tool = AssistantTools.tools.find(_.name == "open_theory")
    tool should not be empty
    val required = tool.get.params.filter(_.required).map(_.name)
    required should contain("path")
    required.length shouldBe 1
  }

  test("write tools should not mention I/Q") {
    val writeTools = List("edit_theory", "create_theory", "open_theory")
    for (toolName <- writeTools) {
      val tool = AssistantTools.tools.find(_.name == toolName).get
      tool.description.toLowerCase should not include "i/q"
    }
  }

  test("batch tools should mention efficiency") {
    val tool = AssistantTools.tools.find(_.name == "try_methods").get
    tool.description.toLowerCase should (include("efficient") or include("multiple"))
  }

  test("web_search should not require I/Q") {
    val tool = AssistantTools.tools.find(_.name == "web_search").get
    tool.description.toLowerCase should not include "i/q"
  }
}
