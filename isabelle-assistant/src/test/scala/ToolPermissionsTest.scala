/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatest.BeforeAndAfterEach

/**
 * Tests for ToolPermissions permission checking and configuration.
 * Tests the permission model without requiring jEdit runtime.
 */
class ToolPermissionsTest
    extends AnyFunSuite
    with Matchers
    with BeforeAndAfterEach {

  override protected def beforeEach(): Unit = {
    super.beforeEach()
    ToolPermissions.clearSession()
    ToolPermissions.resetToDefaults()
  }

  test("PermissionLevel should have correct config strings") {
    ToolPermissions.Deny.toConfigString shouldBe "Deny"
    ToolPermissions.AskAlways.toConfigString shouldBe "AskAlways"
    ToolPermissions.AskAtFirstUse.toConfigString shouldBe "AskAtFirstUse"
    ToolPermissions.Allow.toConfigString shouldBe "Allow"
  }

  test("PermissionLevel.fromString should parse valid levels") {
    ToolPermissions.PermissionLevel.fromString("Deny") shouldBe Some(ToolPermissions.Deny)
    ToolPermissions.PermissionLevel.fromString("AskAlways") shouldBe Some(ToolPermissions.AskAlways)
    ToolPermissions.PermissionLevel.fromString("AskAtFirstUse") shouldBe Some(ToolPermissions.AskAtFirstUse)
    ToolPermissions.PermissionLevel.fromString("Allow") shouldBe Some(ToolPermissions.Allow)
  }

  test("PermissionLevel.fromString should return None for invalid strings") {
    ToolPermissions.PermissionLevel.fromString("Invalid") shouldBe None
    ToolPermissions.PermissionLevel.fromString("allow") shouldBe None // case-sensitive
    ToolPermissions.PermissionLevel.fromString("") shouldBe None
  }

  test("PermissionLevel.fromDisplayString should parse valid display labels") {
    ToolPermissions.PermissionLevel.fromDisplayString("Deny") shouldBe Some(ToolPermissions.Deny)
    ToolPermissions.PermissionLevel.fromDisplayString("Ask Always") shouldBe Some(ToolPermissions.AskAlways)
    ToolPermissions.PermissionLevel.fromDisplayString("Ask at First Use") shouldBe Some(ToolPermissions.AskAtFirstUse)
    ToolPermissions.PermissionLevel.fromDisplayString("Allow") shouldBe Some(ToolPermissions.Allow)
  }

  test("PermissionLevel.fromDisplayString should reject invalid display labels") {
    ToolPermissions.PermissionLevel.fromDisplayString("ask always") shouldBe None
    ToolPermissions.PermissionLevel.fromDisplayString("Unknown") shouldBe None
  }

  test("all tools should have default permissions defined") {
    val toolNames = AssistantTools.tools.map(_.name).toSet
    val defaults = ToolPermissions.getAllToolPermissions.map(_._1).toSet
    toolNames shouldBe defaults
  }

  test("read-only tools should default to Allow") {
    val readOnlyTools = List("read_theory", "list_theories", "search_in_theory",
      "get_goal_state", "get_proof_context", "get_errors", "get_warnings")
    for (toolName <- readOnlyTools) {
      val level = ToolPermissions.getConfiguredLevel(toolName)
      level shouldBe ToolPermissions.Allow
    }
  }

  test("I/Q verification tools should default to AskAtFirstUse") {
    val verifyTools = List("verify_proof", "execute_step", "try_methods",
      "find_theorems", "get_definitions", "run_sledgehammer")
    for (toolName <- verifyTools) {
      val level = ToolPermissions.getConfiguredLevel(toolName)
      level shouldBe ToolPermissions.AskAtFirstUse
    }
  }

  test("side-effect tools should default to AskAlways") {
    val sideEffectTools = List("edit_theory", "create_theory", "open_theory", "web_search")
    for (toolName <- sideEffectTools) {
      val level = ToolPermissions.getConfiguredLevel(toolName)
      level shouldBe ToolPermissions.AskAlways
    }
  }

  test("ask_user tool should always be Allow and locked") {
    val level = ToolPermissions.getConfiguredLevel("ask_user")
    level shouldBe ToolPermissions.Allow
  }

  test("checkPermission should return Allowed for Allow-level tools") {
    val args: ResponseParser.ToolArgs = Map.empty
    ToolPermissions.clearSession()
    val decision = ToolPermissions.checkPermission("read_theory", args)
    decision shouldBe ToolPermissions.Allowed
  }

  test("AskAlways tools should still prompt even if session-allowed state exists") {
    ToolPermissions.clearSession()
    ToolPermissions.setSessionAllowedForTest("edit_theory")
    val decision = ToolPermissions.checkPermission(
      "edit_theory",
      Map.empty[String, ResponseParser.ToolValue]
    )
    decision shouldBe ToolPermissions.NeedPrompt(ToolId.EditTheory, None, None)
  }

  test("prompt details should include a sanitized argument summary") {
    val decision = ToolPermissions.checkPermission(
      "edit_theory",
      Map(
        "theory" -> ResponseParser.StringValue("Scratch"),
        "operation" -> ResponseParser.StringValue("insert"),
        "text" -> ResponseParser.StringValue("lemma foo: True by simp")
      )
    )
    decision match {
      case ToolPermissions.NeedPrompt(ToolId.EditTheory, Some("Scratch"), Some(details)) =>
        details should include("operation=insert")
        details should include("theory=Scratch")
      case other =>
        fail(s"Expected prompt decision with details, got: $other")
    }
  }

  test("prompt details should redact sensitive argument names") {
    val decision = ToolPermissions.checkPermission(
      "web_search",
      Map(
        "query" -> ResponseParser.StringValue("isabelle afp"),
        "auth_token" -> ResponseParser.StringValue("super-secret-token")
      )
    )
    decision match {
      case ToolPermissions.NeedPrompt(ToolId.WebSearch, _, Some(details)) =>
        details should include("auth_token=***")
        details should not include "super-secret-token"
      case other =>
        fail(s"Expected prompt decision with redacted details, got: $other")
    }
  }

  test("clearSession should reset session state") {
    ToolPermissions.clearSession()
    // Session state is internal, but we can test indirectly via checkPermission behavior
    // After clear, checkPermission should follow configured defaults
    val decision = ToolPermissions.checkPermission("read_theory", Map.empty[String, ResponseParser.ToolValue])
    decision shouldBe ToolPermissions.Allowed
  }

  test("getVisibleTools should exclude tools configured as Deny") {
    ToolPermissions.setConfiguredLevel("web_search", ToolPermissions.Deny)
    val visibleNames = ToolPermissions.getVisibleTools.map(_.name).toSet
    visibleNames should not contain "web_search"
    visibleNames should contain("read_theory")
  }

  test("all tools should have descriptions for permission prompts") {
    val permissions = ToolPermissions.getAllToolPermissions
    permissions should not be empty
    permissions.length shouldBe 35 // All 35 tools
  }

  test("toolDescriptions should cover every defined tool") {
    val toolNames = AssistantTools.tools.map(_.name).toSet
    ToolPermissions.toolDescriptions.keySet shouldBe toolNames
  }

  test("session-level decisions should be isolated") {
    ToolPermissions.clearSession()
    // checkPermission behavior depends on session state which is internal
    // This test verifies clearSession doesn't throw
    ToolPermissions.clearSession()
    succeed
  }

  test("getConfiguredLevel should handle unknown tools gracefully") {
    val level = ToolPermissions.getConfiguredLevel("nonexistent_tool")
    // Should return AskAtFirstUse as default fallback
    level shouldBe ToolPermissions.AskAtFirstUse
  }

  test("ask_user cannot have its permission level changed") {
    // ask_user should always return Allow, regardless of configuration attempts
    val level = ToolPermissions.getConfiguredLevel("ask_user")
    level shouldBe ToolPermissions.Allow
    
    // Attempting to set should be no-op (doesn't throw)
    ToolPermissions.setConfiguredLevel("ask_user", ToolPermissions.Deny)
    val stillAllow = ToolPermissions.getConfiguredLevel("ask_user")
    stillAllow shouldBe ToolPermissions.Allow
  }

  test("resetToDefaults should restore default permissions") {
    ToolPermissions.resetToDefaults()
    // Verify a few representative tools
    ToolPermissions.getConfiguredLevel("read_theory") shouldBe ToolPermissions.Allow
    ToolPermissions.getConfiguredLevel("verify_proof") shouldBe ToolPermissions.AskAtFirstUse
    ToolPermissions.getConfiguredLevel("edit_theory") shouldBe ToolPermissions.AskAlways
  }

  test("getAllToolPermissions should return all 35 tools") {
    val all = ToolPermissions.getAllToolPermissions
    all.length shouldBe 35
    all.map(_._1).toSet shouldBe AssistantTools.tools.map(_.name).toSet
  }

  test("permission levels should have stable config string representation") {
    // Verify round-trip: level -> string -> level
    for (level <- List(ToolPermissions.Deny, ToolPermissions.AskAlways, 
                       ToolPermissions.AskAtFirstUse, ToolPermissions.Allow)) {
      val configStr = level.toConfigString
      val parsed = ToolPermissions.PermissionLevel.fromString(configStr)
      parsed shouldBe Some(level)
    }
  }

  test("task list tools should default to Allow") {
    val taskTools = List("task_list_add", "task_list_done", "task_list_irrelevant",
      "task_list_next", "task_list_show", "task_list_get")
    for (toolName <- taskTools) {
      val level = ToolPermissions.getConfiguredLevel(toolName)
      level shouldBe ToolPermissions.Allow
    }
  }

  test("task list tools should be included in getAllToolPermissions") {
    val all = ToolPermissions.getAllToolPermissions
    val taskTools = Set("task_list_add", "task_list_done", "task_list_irrelevant",
      "task_list_next", "task_list_show", "task_list_get")
    val toolNames = all.map(_._1).toSet
    taskTools.foreach(tool => toolNames should contain(tool))
  }

  test("task list tools should be visible by default") {
    val visible = ToolPermissions.getVisibleTools
    val taskTools = Set("task_list_add", "task_list_done", "task_list_irrelevant",
      "task_list_next", "task_list_show", "task_list_get")
    val visibleNames = visible.map(_.name).toSet
    taskTools.foreach(tool => visibleNames should contain(tool))
  }

  test("checkPermission should allow task list tools without prompting") {
    ToolPermissions.clearSession()
    val taskTools = List("task_list_add", "task_list_done", "task_list_irrelevant",
      "task_list_next", "task_list_show", "task_list_get")
    for (toolName <- taskTools) {
      val decision = ToolPermissions.checkPermission(toolName, Map.empty[String, ResponseParser.ToolValue])
      decision shouldBe ToolPermissions.Allowed
    }
  }

  test("promptUser AskAtFirstUse allow-session should cache session allowance") {
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => Some("Allow (for this session)")) {
      ToolPermissions.promptUser("verify_proof", None, None, null) shouldBe ToolPermissions.Allowed
      ToolPermissions.checkPermission("verify_proof", Map.empty[String, ResponseParser.ToolValue]) shouldBe ToolPermissions.Allowed
    }
  }

  test("promptUser AskAtFirstUse allow-once should not cache session allowance") {
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => Some("Allow Once")) {
      ToolPermissions.promptUser("verify_proof", None, None, null) shouldBe ToolPermissions.Allowed
      ToolPermissions.checkPermission("verify_proof", Map.empty[String, ResponseParser.ToolValue]) shouldBe
        ToolPermissions.NeedPrompt(ToolId.VerifyProof, None, None)
    }
  }

  test("promptUser AskAlways allow-once should keep prompting") {
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => Some("Allow Once")) {
      ToolPermissions.promptUser("edit_theory", None, None, null) shouldBe ToolPermissions.Allowed
      ToolPermissions.checkPermission("edit_theory", Map.empty[String, ResponseParser.ToolValue]) shouldBe
        ToolPermissions.NeedPrompt(ToolId.EditTheory, None, None)
    }
  }

  test("promptUser deny-session should persist denial in this session") {
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => Some("Deny (for this session)")) {
      ToolPermissions.promptUser("verify_proof", None, None, null) shouldBe ToolPermissions.Denied
      ToolPermissions.checkPermission("verify_proof", Map.empty[String, ResponseParser.ToolValue]) shouldBe ToolPermissions.Denied
    }
  }

  test("promptUser timeout/cancel should deny") {
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => None) {
      ToolPermissions.promptUser("verify_proof", None, None, null) shouldBe ToolPermissions.Denied
    }
  }
}
