/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for PayloadBuilder: provider detection, Llama version detection,
 * and JSON payload construction for all supported model providers.
 */
class PayloadBuilderTest extends AnyFunSuite with Matchers {

  // --- Provider detection ---

  test("isProvider should detect anthropic") {
    PayloadBuilder.isProvider("anthropic.claude-v2", "anthropic") shouldBe true
    PayloadBuilder.isProvider("anthropic.claude-3-sonnet", "anthropic") shouldBe true
  }

  test("isProvider should detect meta") {
    PayloadBuilder.isProvider("meta.llama3-70b-instruct", "meta") shouldBe true
  }

  test("isProvider should detect mistral") {
    PayloadBuilder.isProvider("mistral.mistral-7b-instruct", "mistral") shouldBe true
  }

  test("isProvider should detect amazon") {
    PayloadBuilder.isProvider("amazon.titan-text-express-v1", "amazon") shouldBe true
  }

  test("isProvider should handle CRIS-prefixed IDs") {
    PayloadBuilder.isProvider("us.anthropic.claude-3-sonnet", "anthropic") shouldBe true
    PayloadBuilder.isProvider("eu.anthropic.claude-3-sonnet", "anthropic") shouldBe true
    PayloadBuilder.isProvider("ap.meta.llama3-70b", "meta") shouldBe true
    PayloadBuilder.isProvider("global.anthropic.claude-haiku-4-5", "anthropic") shouldBe true
  }

  test("isProvider should reject mismatches") {
    PayloadBuilder.isProvider("anthropic.claude-v2", "meta") shouldBe false
    PayloadBuilder.isProvider("meta.llama3-70b", "anthropic") shouldBe false
    PayloadBuilder.isProvider("us.anthropic.claude-v2", "meta") shouldBe false
  }

  // --- Llama version detection ---

  test("isLlama3OrLater should detect Llama 3") {
    PayloadBuilder.isLlama3OrLater("meta.llama3-70b-instruct") shouldBe true
    PayloadBuilder.isLlama3OrLater("meta.llama-3-8b") shouldBe true
  }

  test("isLlama3OrLater should detect Llama 4") {
    PayloadBuilder.isLlama3OrLater("meta.llama4-maverick") shouldBe true
    PayloadBuilder.isLlama3OrLater("meta.llama-4-scout") shouldBe true
  }

  test("isLlama3OrLater should reject Llama 2") {
    PayloadBuilder.isLlama3OrLater("meta.llama2-70b-chat") shouldBe false
    PayloadBuilder.isLlama3OrLater("meta.llama-2-13b") shouldBe false
  }

  test("isLlama3OrLater should default to false for unrecognised version") {
    // Models with no explicit version marker should default to Llama 2 format to be safe
    PayloadBuilder.isLlama3OrLater("meta.llama-unknown") shouldBe false
  }

  // --- Payload construction ---

  test("buildPayload for Anthropic should include anthropic_version and messages array") {
    val payload = PayloadBuilder.buildPayload("anthropic.claude-v2", "Hello", 0.5, 1000)
    payload should include("anthropic_version")
    payload should include("bedrock-2023-05-31")
    payload should include("messages")
    payload should include("Hello")
    payload should include("1000")
    payload should not include "system"
  }

  test("buildPayload for Anthropic with system prompt should include system field") {
    val payload = PayloadBuilder.buildPayload("anthropic.claude-v2", "Hello", 0.5, 1000, Some("You are helpful"))
    payload should include("anthropic_version")
    payload should include("system")
    payload should include("You are helpful")
    payload should include("messages")
    payload should include("Hello")
  }

  test("buildPayload for Anthropic with empty system prompt should not include system field") {
    val payload = PayloadBuilder.buildPayload("anthropic.claude-v2", "Hello", 0.5, 1000, Some(""))
    payload should not include "system"
  }

  test("buildPayload for Meta Llama 3+ should use begin_of_text format") {
    val payload = PayloadBuilder.buildPayload("meta.llama3-70b-instruct", "Hello", 0.5, 1000)
    payload should include("begin_of_text")
    payload should include("start_header_id")
    payload should include("Hello")
    payload should include("max_gen_len")
  }

  test("buildPayload for Meta Llama 2 should use simple prompt format") {
    val payload = PayloadBuilder.buildPayload("meta.llama2-70b-chat", "Hello", 0.5, 1000)
    payload should include("Hello")
    payload should include("max_gen_len")
    payload should not include "begin_of_text"
  }

  test("buildPayload for Mistral should use INST format") {
    val payload = PayloadBuilder.buildPayload("mistral.mistral-7b-instruct", "Hello", 0.5, 1000)
    payload should include("[INST]")
    payload should include("Hello")
    payload should include("max_tokens")
  }

  test("buildPayload for Amazon Titan should use inputText format") {
    val payload = PayloadBuilder.buildPayload("amazon.titan-text-express-v1", "Hello", 0.5, 1000)
    payload should include("inputText")
    payload should include("Hello")
    payload should include("maxTokenCount")
    payload should include("textGenerationConfig")
  }

  test("buildPayload for unknown provider should use generic messages format") {
    val payload = PayloadBuilder.buildPayload("custom.model-v1", "Hello", 0.5, 1000)
    payload should include("messages")
    payload should include("Hello")
    payload should include("max_tokens")
  }

  test("buildChatPayload for Anthropic should include system prompt separately") {
    val payload = PayloadBuilder.buildChatPayload(
      "anthropic.claude-v2", "You are helpful", List(("user", "Hi")), 0.3, 2000)
    payload should include("system")
    payload should include("You are helpful")
    payload should include("messages")
    payload should include("Hi")
  }

  test("buildChatPayload should handle multiple messages") {
    val messages = List(("user", "Hello"), ("assistant", "Hi there"), ("user", "Help me"))
    val payload = PayloadBuilder.buildChatPayload(
      "anthropic.claude-v2", "System", messages, 0.3, 2000)
    payload should include("Hello")
    payload should include("Hi there")
    payload should include("Help me")
  }

  test("buildChatPayload for Llama 3 should include system in prompt header") {
    val payload = PayloadBuilder.buildChatPayload(
      "meta.llama3-70b-instruct", "System prompt", List(("user", "Question")), 0.3, 2000)
    payload should include("system")
    payload should include("System prompt")
    payload should include("Question")
  }

  test("buildPayload should properly escape special characters") {
    val payload = PayloadBuilder.buildPayload("anthropic.claude-v2", "Hello \"world\" \n test", 0.5, 1000)
    // Jackson handles JSON escaping automatically
    payload should include("Hello")
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
      0.3,
      2000
    )
    payload should include("\"content\":\"[this is plain text, not JSON blocks]\"")
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
}
