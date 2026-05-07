/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for PayloadBuilder: Anthropic-only JSON payload construction.
 *
 * Payloads must never include a `temperature` field — Opus 4.7+ rejects
 * the deprecated field, and earlier Claude models default sensibly without it.
 */
class PayloadBuilderTest extends AnyFunSuite with Matchers {

  // --- Payload construction ---

  test("buildChatPayload for Anthropic should include system prompt separately") {
    val payload = PayloadBuilder.buildChatPayload(
      "You are helpful", List(("user", "Hi")), 2000)
    payload should include("system")
    payload should include("You are helpful")
    payload should include("messages")
    payload should include("Hi")
  }

  test("buildChatPayload should handle multiple messages") {
    val messages = List(("user", "Hello"), ("assistant", "Hi there"), ("user", "Help me"))
    val payload = PayloadBuilder.buildChatPayload("System", messages, 2000)
    payload should include("Hello")
    payload should include("Hi there")
    payload should include("Help me")
  }

  test("buildChatPayload should never emit a temperature field") {
    val payload = PayloadBuilder.buildChatPayload("System", List(("user", "Hi")), 2000)
    payload should not include "temperature"
  }

  test("isAnthropicStructuredContent should accept valid content block arrays") {
    PayloadBuilder.isAnthropicStructuredContent(
      """[{"type":"text","text":"hello"},{"type":"tool_result","tool_use_id":"x","content":"ok"}]"""
    ) shouldBe true
  }

  test("isAnthropicStructuredContent should reject non-JSON and non-block arrays") {
    PayloadBuilder.isAnthropicStructuredContent("[not valid json") shouldBe false
    PayloadBuilder.isAnthropicStructuredContent("""[{"text":"missing type"}]""") shouldBe false
    PayloadBuilder.isAnthropicStructuredContent("""["plain text"]""") shouldBe false
  }

  test("buildAnthropicToolPayload should serialize bracket-prefixed plain text as string content") {
    val payload = PayloadBuilder.buildAnthropicToolPayload(
      "System",
      List(("user", "[this is plain text, not JSON blocks]")),
      2000
    )
    payload should include("\"content\":\"[this is plain text, not JSON blocks]\"")
  }

  test("buildAnthropicToolPayload should never emit a temperature field") {
    val payload = PayloadBuilder.buildAnthropicToolPayload(
      "System", List(("user", "Hi")), 2000
    )
    payload should not include "temperature"
  }

  test("buildPlanningAgentToolPayload should never emit a temperature field") {
    val payload = PayloadBuilder.buildPlanningAgentToolPayload(
      "System", List(("user", "Explore")), 2000
    )
    payload should not include "temperature"
  }

  test("writeJson should produce valid JSON") {
    val json = PayloadBuilder.writeJson { g =>
      g.writeStringField("key", "value")
      g.writeNumberField("num", 42)
      g.writeBooleanField("flag", true)
    }
    json should include("\"key\"")
    json should include("\"value\"")
    json should include("42")
    json should include("true")
  }

  // --- Structured output payload ---

  test("buildAnthropicStructuredPayload should include tool_choice forcing") {
    val schema = StructuredResponseSchema(
      "return_code", "Return code",
      """{"type":"object","properties":{"code":{"type":"string"}},"required":["code"]}"""
    )
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "System prompt", List(("user", "Refactor this")), schema, 2000
    )
    payload should include("tool_choice")
    payload should include("\"type\":\"tool\"")
    payload should include("\"name\":\"return_code\"")
  }

  test("buildAnthropicStructuredPayload should include single tool definition with schema") {
    val schema = StructuredResponseSchema(
      "return_suggestions", "Return suggestions",
      """{"type":"object","properties":{"suggestions":{"type":"array","items":{"type":"string"}}},"required":["suggestions"]}"""
    )
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "System", List(("user", "Suggest")), schema, 1000
    )
    payload should include("\"name\":\"return_suggestions\"")
    payload should include("input_schema")
    payload should include("suggestions")
    // Should include only the schema tool, not agentic tools
    payload should not include "read_theory"
    payload should not include "verify_proof"
  }

  test("buildAnthropicStructuredPayload should include anthropic_version and messages") {
    val schema = StructuredResponseSchema(
      "test_tool", "Test",
      """{"type":"object","properties":{"x":{"type":"string"}},"required":["x"]}"""
    )
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "Sys", List(("user", "Hello")), schema, 500
    )
    payload should include("anthropic_version")
    payload should include("bedrock-2023-05-31")
    payload should include("messages")
    payload should include("Hello")
  }

  test("buildAnthropicStructuredPayload should handle empty system prompt") {
    val schema = StructuredResponseSchema(
      "test_tool", "Test",
      """{"type":"object","properties":{"x":{"type":"string"}},"required":["x"]}"""
    )
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "", List(("user", "Hello")), schema, 500
    )
    payload should not include "\"system\""
  }

  test("buildAnthropicStructuredPayload should handle structured content in messages") {
    val schema = StructuredResponseSchema(
      "test_tool", "Test",
      """{"type":"object","properties":{"x":{"type":"string"}},"required":["x"]}"""
    )
    val structuredContent = """[{"type":"text","text":"hello"}]"""
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "Sys", List(("user", structuredContent)), schema, 500
    )
    // Structured content should be raw JSON, not string-escaped
    payload should include(""""content":[{"type":"text","text":"hello"}]""")
  }

  test("buildAnthropicStructuredPayload should never emit a temperature field") {
    val schema = StructuredResponseSchema(
      "test_tool", "Test",
      """{"type":"object","properties":{"x":{"type":"string"}},"required":["x"]}"""
    )
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "Sys", List(("user", "Hello")), schema, 500
    )
    payload should not include "temperature"
  }
}
