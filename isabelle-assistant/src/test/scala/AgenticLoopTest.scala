/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import software.amazon.awssdk.services.bedrockruntime.model.InvokeModelRequest

/** Tests for BedrockClient agentic tool-use loop using mocks.
  *
  * These tests verify the loop logic (stuck-loop detection, iteration limits,
  * text accumulation, cancellation) without requiring AWS credentials or a
  * running I/Q server.
  */
class AgenticLoopTest extends AnyFunSuite with Matchers {

  // Helper to build mock Anthropic responses
  private def buildMockTextResponse(text: String): String = {
    s"""{"content":[{"type":"text","text":"$text"}],"stop_reason":"end_turn"}"""
  }

  private def buildMockToolUseResponse(toolId: String, toolName: String, inputJson: String): String = {
    s"""{"content":[{"type":"tool_use","id":"$toolId","name":"$toolName","input":$inputJson}],"stop_reason":"tool_use"}"""
  }

  private def buildMockMixedResponse(text: String, toolId: String, toolName: String, inputJson: String): String = {
    s"""{"content":[{"type":"text","text":"$text"},{"type":"tool_use","id":"$toolId","name":"$toolName","input":$inputJson}],"stop_reason":"tool_use"}"""
  }

  test("invokeChatWithToolsTestable should return text from simple text-only response") {
    val invoker: InvokeModelRequest => String = _ => buildMockTextResponse("Hello, this is my response.")
    val toolExecutor: (String, ResponseParser.ToolArgs) => String = (_, _) => 
      throw new RuntimeException("Tool executor should not be called")

    val result = BedrockClient.invokeChatWithToolsTestable(
      modelId = "anthropic.claude-3-7-sonnet-20250219-v1:0",
      systemPrompt = "test",
      initialMessages = List.empty,
      maxTokens = 100,
      invoker = invoker,
      toolExecutor = toolExecutor
    )

    result should include("Hello, this is my response.")
  }

  test("invokeChatWithToolsTestable should execute tool and return final text") {
    var apiCallCount = 0
    val invoker: InvokeModelRequest => String = _ => {
      apiCallCount += 1
      if (apiCallCount == 1) {
        // First call: model requests a tool
        buildMockToolUseResponse("tool-1", "read_theory", """{"theory":"Foo"}""")
      } else {
        // Second call: model returns text after tool result
        buildMockTextResponse("I read the theory and found X.")
      }
    }
    
    var toolCallCount = 0
    val toolExecutor: (String, ResponseParser.ToolArgs) => String = (name, _) => {
      toolCallCount += 1
      name shouldBe "read_theory"
      "Theory Foo content"
    }

    val result = BedrockClient.invokeChatWithToolsTestable(
      modelId = "anthropic.claude-3-7-sonnet-20250219-v1:0",
      systemPrompt = "test",
      initialMessages = List.empty,
      maxTokens = 100,
      invoker = invoker,
      toolExecutor = toolExecutor
    )

    apiCallCount shouldBe 2
    toolCallCount shouldBe 1
    result should include("I read the theory and found X.")
  }

  test("invokeChatWithToolsTestable should accumulate text from multiple iterations") {
    var apiCallCount = 0
    val invoker: InvokeModelRequest => String = _ => {
      apiCallCount += 1
      apiCallCount match {
        case 1 => buildMockMixedResponse("First,", "tool-1", "read_theory", """{"theory":"Foo"}""")
        case 2 => buildMockMixedResponse("second,", "tool-2", "get_goal_state", """{}""")
        case 3 => buildMockTextResponse("and third.")
        case _ => buildMockTextResponse("unexpected call")
      }
    }
    
    val toolExecutor: (String, ResponseParser.ToolArgs) => String = (name, _) => s"Result from $name"

    val result = BedrockClient.invokeChatWithToolsTestable(
      modelId = "anthropic.claude-3-7-sonnet-20250219-v1:0",
      systemPrompt = "test",
      initialMessages = List.empty,
      maxTokens = 100,
      invoker = invoker,
      toolExecutor = toolExecutor
    )

    result should include("First,")
    result should include("second,")
    result should include("and third.")
  }

  test("invokeChatWithToolsTestable should detect stuck loops") {
    // Model always returns same tool call with same args
    val invoker: InvokeModelRequest => String = _ => 
      buildMockToolUseResponse("tool-1", "read_theory", """{"theory":"Foo"}""")
    
    val toolExecutor: (String, ResponseParser.ToolArgs) => String = (_, _) => {
      "result" // Tool always returns same result
    }

    val ex = intercept[RuntimeException] {
      BedrockClient.invokeChatWithToolsTestable(
        modelId = "anthropic.claude-3-7-sonnet-20250219-v1:0",
        systemPrompt = "test",
        initialMessages = List.empty,
        maxTokens = 100,
        invoker = invoker,
        toolExecutor = toolExecutor
      )
    }
    
    // Should hit stuck-loop detection (3 identical calls)
    ex.getMessage should include("Stuck in loop")
  }

  test("invokeChatWithToolsTestable should handle cancellation") {
    AssistantDockable.cancel()
    
    val invoker: InvokeModelRequest => String = _ => buildMockTextResponse("test")
    val toolExecutor: (String, ResponseParser.ToolArgs) => String = (_, _) => "result"
    
    val ex = intercept[RuntimeException] {
      BedrockClient.invokeChatWithToolsTestable(
        modelId = "anthropic.claude-3-7-sonnet-20250219-v1:0",
        systemPrompt = "test",
        initialMessages = List.empty,
        maxTokens = 100,
        invoker = invoker,
        toolExecutor = toolExecutor
      )
    }
    
    AssistantDockable.resetCancel()
    ex.getMessage should include("cancelled")
  }

  test("invokeChatWithToolsTestable should handle tool execution errors gracefully") {
    var apiCallCount = 0
    val invoker: InvokeModelRequest => String = _ => {
      apiCallCount += 1
      if (apiCallCount == 1) {
        buildMockToolUseResponse("tool-1", "read_theory", """{"theory":"Foo"}""")
      } else {
        // After error, model should be able to continue
        buildMockTextResponse("The tool failed, but here's my answer anyway.")
      }
    }

    val toolExecutor: (String, ResponseParser.ToolArgs) => String = (name, _) => {
      // Tool returns an error message (as a string result, not thrown exception)
      s"Error: tool $name failed"
    }

    val result = BedrockClient.invokeChatWithToolsTestable(
      modelId = "anthropic.claude-3-7-sonnet-20250219-v1:0",
      systemPrompt = "test",
      initialMessages = List.empty,
      maxTokens = 100,
      invoker = invoker,
      toolExecutor = toolExecutor
    )

    result should include("The tool failed, but here's my answer anyway.")
  }

  test("invokeChatWithToolsTestable should keep running when a tool handler throws") {
    var apiCallCount = 0
    val invoker: InvokeModelRequest => String = _ => {
      apiCallCount += 1
      if (apiCallCount == 1) {
        buildMockToolUseResponse("tool-1", "read_theory", """{"theory":"Foo"}""")
      } else {
        buildMockTextResponse("Recovered after tool crash.")
      }
    }

    var toolCallCount = 0
    val toolExecutor: (String, ResponseParser.ToolArgs) => String = (_, _) => {
      toolCallCount += 1
      throw new RuntimeException("handler boom")
    }

    val result = BedrockClient.invokeChatWithToolsTestable(
      modelId = "anthropic.claude-3-7-sonnet-20250219-v1:0",
      systemPrompt = "test",
      initialMessages = List.empty,
      maxTokens = 100,
      invoker = invoker,
      toolExecutor = toolExecutor
    )

    apiCallCount shouldBe 2
    toolCallCount shouldBe 1
    result should include("Recovered after tool crash.")
  }
}