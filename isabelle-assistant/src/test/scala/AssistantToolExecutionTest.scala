/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import java.util.concurrent.atomic.AtomicInteger

class AssistantToolExecutionTest
    extends AnyFunSuite
    with Matchers
    with BeforeAndAfterEach {

  override protected def beforeEach(): Unit = {
    super.beforeEach()
    ToolPermissions.clearSession()
    ToolPermissions.resetToDefaults()
  }

  test("executeTool should return clear error for unknown tool") {
    AssistantTools.executeTool("definitely_unknown_tool", Map.empty, null) shouldBe
      "Unknown tool: definitely_unknown_tool"
  }

  test("executeTool should validate web_search query before any network call") {
    AssistantTools.executeTool("web_search", Map.empty, null) shouldBe
      "Error: query required"
  }

  test("executeTool should validate set_cursor_position arguments before touching view state") {
    AssistantTools.executeTool(
      "set_cursor_position",
      Map("line" -> ResponseParser.IntValue(-1)),
      null
    ) shouldBe "Error: line must be a positive integer"
  }

  test("executeToolWithPermission should deny tools configured as Deny") {
    ToolPermissions.setConfiguredLevel("web_search", ToolPermissions.Deny)
    AssistantTools.executeToolWithPermission("web_search", Map.empty, null) shouldBe
      "Permission denied: tool 'web_search' is not allowed."
  }

  test("executeToolWithPermission should respect user denial from prompt") {
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => Some("Deny (for this session)")) {
      AssistantTools.executeToolWithPermission("web_search", Map.empty, null) shouldBe
        "Permission denied: user declined tool 'web_search'."
    }
  }

  test("AskAlways tools should prompt on every invocation") {
    val prompts = new AtomicInteger(0)
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => {
      prompts.incrementAndGet()
      Some("Allow Once")
    }) {
      AssistantTools.executeToolWithPermission("web_search", Map.empty, null) shouldBe
        "Error: query required"
      AssistantTools.executeToolWithPermission("web_search", Map.empty, null) shouldBe
        "Error: query required"
    }
    prompts.get shouldBe 2
  }

  test("AskAtFirstUse tools should prompt once when session-allowed") {
    ToolPermissions.setConfiguredLevel("web_search", ToolPermissions.AskAtFirstUse)
    val prompts = new AtomicInteger(0)
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => {
      prompts.incrementAndGet()
      Some("Allow (for this session)")
    }) {
      AssistantTools.executeToolWithPermission("web_search", Map.empty, null) shouldBe
        "Error: query required"
      AssistantTools.executeToolWithPermission("web_search", Map.empty, null) shouldBe
        "Error: query required"
    }
    prompts.get shouldBe 1
  }

  test("AskAtFirstUse tools denied for session should not re-prompt") {
    ToolPermissions.setConfiguredLevel("web_search", ToolPermissions.AskAtFirstUse)
    val prompts = new AtomicInteger(0)
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => {
      prompts.incrementAndGet()
      Some("Deny (for this session)")
    }) {
      AssistantTools.executeToolWithPermission("web_search", Map.empty, null) shouldBe
        "Permission denied: user declined tool 'web_search'."
      AssistantTools.executeToolWithPermission("web_search", Map.empty, null) shouldBe
        "Permission denied: tool 'web_search' is not allowed."
    }
    prompts.get shouldBe 1
  }
}

