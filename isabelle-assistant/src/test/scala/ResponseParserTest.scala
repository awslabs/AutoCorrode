/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for ResponseParser: JSON response parsing for all providers,
 * and the critical Anthropic content block parser that had zero test coverage.
 */
class ResponseParserTest extends AnyFunSuite with Matchers {

  // --- Basic response parsing ---

  test("parseResponse should extract text from Anthropic response") {
    val json = """{"content":[{"type":"text","text":"Hello world"}],"stop_reason":"end_turn"}"""
    ResponseParser.parseResponse("anthropic.claude-v2", json) shouldBe "Hello world"
  }

  test("parseResponse should extract generation from Meta response") {
    val json = """{"generation":"Hello from Llama","stop_reason":"stop"}"""
    ResponseParser.parseResponse("meta.llama3-70b", json) shouldBe "Hello from Llama"
  }

  test("parseResponse should extract outputText from Amazon Titan response") {
    val json = """{"results":[{"outputText":"Hello from Titan"}]}"""
    ResponseParser.parseResponse("amazon.titan-text-express-v1", json) shouldBe "Hello from Titan"
  }

  test("parseResponse should extract text from generic response") {
    val json = """{"text":"Generic response"}"""
    ResponseParser.parseResponse("custom.model-v1", json) shouldBe "Generic response"
  }

  test("parseResponse should throw on null input") {
    a [RuntimeException] should be thrownBy {
      ResponseParser.parseResponse("anthropic.claude-v2", null)
    }
  }

  test("parseResponse should throw on empty input") {
    a [RuntimeException] should be thrownBy {
      ResponseParser.parseResponse("anthropic.claude-v2", "")
    }
  }

  test("parseResponse should throw on whitespace-only input") {
    a [RuntimeException] should be thrownBy {
      ResponseParser.parseResponse("anthropic.claude-v2", "   ")
    }
  }

  test("parseResponse should throw on JSON with no text field") {
    a [RuntimeException] should be thrownBy {
      ResponseParser.parseResponse("anthropic.claude-v2", """{"id":"msg_123","model":"claude"}""")
    }
  }

  test("parseResponse should handle CRIS-prefixed model IDs") {
    val json = """{"content":[{"type":"text","text":"CRIS response"}],"stop_reason":"end_turn"}"""
    ResponseParser.parseResponse("us.anthropic.claude-3-sonnet", json) shouldBe "CRIS response"
  }

  test("parseResponse should collect multiple text blocks from Anthropic") {
    val json = """{"content":[{"type":"text","text":"Part 1"},{"type":"text","text":"Part 2"}],"stop_reason":"end_turn"}"""
    val result = ResponseParser.parseResponse("anthropic.claude-v2", json)
    result should include("Part 1")
    result should include("Part 2")
  }

  // --- Anthropic content block parsing ---

  test("parseAnthropicContentBlocks should parse text-only response") {
    val json = """{"content":[{"type":"text","text":"Hello world"}],"stop_reason":"end_turn"}"""
    val (blocks, stopReason) = ResponseParser.parseAnthropicContentBlocks(json)
    blocks should have length 1
    blocks.head shouldBe a [ResponseParser.TextBlock]
    blocks.head.asInstanceOf[ResponseParser.TextBlock].text shouldBe "Hello world"
    stopReason shouldBe "end_turn"
  }

  test("parseAnthropicContentBlocks should parse tool_use response") {
    val json = """{
      "content": [
        {"type": "text", "text": "Let me check that."},
        {"type": "tool_use", "id": "toolu_123", "name": "read_theory", "input": {"theory": "Foo.thy", "start_line": 1}}
      ],
      "stop_reason": "tool_use"
    }"""
    val (blocks, stopReason) = ResponseParser.parseAnthropicContentBlocks(json)
    blocks should have length 2
    blocks(0) shouldBe a [ResponseParser.TextBlock]
    blocks(0).asInstanceOf[ResponseParser.TextBlock].text shouldBe "Let me check that."
    blocks(1) shouldBe a [ResponseParser.ToolUseBlock]
    val toolUse = blocks(1).asInstanceOf[ResponseParser.ToolUseBlock]
    toolUse.id shouldBe "toolu_123"
    toolUse.name shouldBe "read_theory"
    toolUse.input("theory") shouldBe ResponseParser.StringValue("Foo.thy")
    toolUse.input("start_line") shouldBe ResponseParser.IntValue(1)
    stopReason shouldBe "tool_use"
  }

  test("parseAnthropicContentBlocks should handle empty content array") {
    val json = """{"content":[],"stop_reason":"end_turn"}"""
    val (blocks, stopReason) = ResponseParser.parseAnthropicContentBlocks(json)
    blocks shouldBe empty
    stopReason shouldBe "end_turn"
  }

  test("parseAnthropicContentBlocks should handle tool_use with string input") {
    val json = """{
      "content": [
        {"type": "tool_use", "id": "t1", "name": "verify_proof", "input": {"proof": "by simp"}}
      ],
      "stop_reason": "tool_use"
    }"""
    val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(json)
    blocks should have length 1
    val tu = blocks.head.asInstanceOf[ResponseParser.ToolUseBlock]
    tu.input("proof") shouldBe ResponseParser.StringValue("by simp")
  }

  test("parseAnthropicContentBlocks should handle tool_use with numeric input") {
    val json = """{
      "content": [
        {"type": "tool_use", "id": "t1", "name": "read_theory", "input": {"theory": "Foo", "start_line": 10, "end_line": 20}}
      ],
      "stop_reason": "tool_use"
    }"""
    val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(json)
    val tu = blocks.head.asInstanceOf[ResponseParser.ToolUseBlock]
    tu.input("theory") shouldBe ResponseParser.StringValue("Foo")
    tu.input("start_line") shouldBe ResponseParser.IntValue(10)
    tu.input("end_line") shouldBe ResponseParser.IntValue(20)
  }

  test("parseAnthropicContentBlocks should handle tool_use with boolean input") {
    val json = """{
      "content": [
        {"type": "tool_use", "id": "t1", "name": "search_in_theory", "input": {"theory": "Foo", "pattern": "lemma", "exact": true}}
      ],
      "stop_reason": "tool_use"
    }"""
    val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(json)
    val tu = blocks.head.asInstanceOf[ResponseParser.ToolUseBlock]
    tu.input("exact") shouldBe ResponseParser.BooleanValue(true)
  }

  test("parseAnthropicContentBlocks should handle multiple tool_use blocks") {
    val json = """{
      "content": [
        {"type": "tool_use", "id": "t1", "name": "read_theory", "input": {"theory": "Foo"}},
        {"type": "tool_use", "id": "t2", "name": "get_goal_state", "input": {}}
      ],
      "stop_reason": "tool_use"
    }"""
    val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(json)
    blocks should have length 2
    blocks(0).asInstanceOf[ResponseParser.ToolUseBlock].name shouldBe "read_theory"
    blocks(1).asInstanceOf[ResponseParser.ToolUseBlock].name shouldBe "get_goal_state"
  }

  test("parseAnthropicContentBlocks should handle nested object in tool input") {
    val json = """{
      "content": [
        {"type": "tool_use", "id": "t1", "name": "complex_tool", "input": {"config": {"key": "value", "nested": true}}}
      ],
      "stop_reason": "tool_use"
    }"""
    val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(json)
    val tu = blocks.head.asInstanceOf[ResponseParser.ToolUseBlock]
    // Nested objects are serialized as JSON strings
    ResponseParser.toolValueToDisplay(tu.input("config")) should include("key")
    ResponseParser.toolValueToDisplay(tu.input("config")) should include("value")
  }

  test("parseAnthropicContentBlocks should handle nested array in tool input") {
    val json = """{
      "content": [
        {"type": "tool_use", "id": "t1", "name": "array_tool", "input": {"items": [1, 2, 3]}}
      ],
      "stop_reason": "tool_use"
    }"""
    val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(json)
    val tu = blocks.head.asInstanceOf[ResponseParser.ToolUseBlock]
    ResponseParser.toolValueToDisplay(tu.input("items")) should include("1")
  }

  test("parseAnthropicContentBlocks should handle missing stop_reason") {
    val json = """{"content":[{"type":"text","text":"hello"}]}"""
    val (blocks, stop) = ResponseParser.parseAnthropicContentBlocks(json)
    blocks.length shouldBe 1
    stop shouldBe ""
  }

  test("parseAnthropicContentBlocks should coerce whole-number floats to Int") {
    val json = """{"content":[{"type":"tool_use","id":"x","name":"test","input":{"line":188.0,"valid":25.0}}]}"""
    val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(json)
    blocks.length shouldBe 1
    blocks.head match {
      case ResponseParser.ToolUseBlock(_, _, input) =>
        input("line") shouldBe ResponseParser.IntValue(188)  // Int not Double
        input("valid") shouldBe ResponseParser.IntValue(25)  // Int not Double
      case _ => fail("Expected ToolUseBlock")
    }
  }

  test("parseAnthropicContentBlocks should preserve actual decimal values") {
    val json = """{"content":[{"type":"tool_use","id":"x","name":"test","input":{"temp":0.5,"ratio":3.14}}]}"""
    val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(json)
    blocks.length shouldBe 1
    blocks.head match {
      case ResponseParser.ToolUseBlock(_, _, input) =>
        input("temp") shouldBe ResponseParser.DecimalValue(0.5)  // Double preserved
        input("ratio") shouldBe ResponseParser.DecimalValue(3.14)  // Double preserved
      case _ => fail("Expected ToolUseBlock")
    }
  }
}
