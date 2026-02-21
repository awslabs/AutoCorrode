/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for BedrockClient helper methods.
 * Bedrock transport is exercised in integration environments; this suite keeps
 * only deterministic utility/error handling checks that do not require AWS.
 */
class BedrockClientTest extends AnyFunSuite with Matchers {

  test("ErrorHandler.makeUserFriendly handles credential errors") {
    val msg = ErrorHandler.makeUserFriendly("access denied for user", "test")
    msg should include("credentials")
  }

  test("ErrorHandler.makeUserFriendly handles network errors") {
    val msg = ErrorHandler.makeUserFriendly("connection refused to host", "test")
    msg should include("connection")
  }

  test("ErrorHandler.makeUserFriendly handles throttling") {
    val msg = ErrorHandler.makeUserFriendly("throttle limit exceeded", "test")
    msg should include("limit")
  }

  test("ErrorHandler.makeUserFriendly handles model not found") {
    val msg = ErrorHandler.makeUserFriendly("model xyz not found in region", "test")
    msg should include("model")
  }

  test("ErrorHandler.makeUserFriendly handles JSON parse errors") {
    val msg = ErrorHandler.makeUserFriendly("json parse error at position 42", "test")
    msg should include("invalid response")
  }

  test("ErrorHandler.sanitize truncates long strings") {
    val long = "x" * 20000
    val result = ErrorHandler.sanitize(long)
    result.length shouldBe AssistantConstants.MAX_RESPONSE_LENGTH
  }

  test("ErrorHandler.sanitize handles null") {
    ErrorHandler.sanitize(null) shouldBe ""
  }

  test("requireAnthropicModel accepts valid Anthropic model IDs") {
    noException should be thrownBy BedrockClient.requireAnthropicModel("anthropic.claude-3-7-sonnet-20250219-v1:0")
    noException should be thrownBy BedrockClient.requireAnthropicModel("us.anthropic.claude-3-7-sonnet-20250219-v1:0")
  }

  test("requireAnthropicModel rejects non-Anthropic model IDs") {
    val ex = intercept[IllegalArgumentException] {
      BedrockClient.requireAnthropicModel("meta.llama3-70b-instruct-v1:0")
    }
    ex.getMessage should include("Only Anthropic models are supported")
  }

  test("validateAnthropicModel reports missing model explicitly") {
    BedrockClient.validateAnthropicModel("") shouldBe
      Left(BedrockClient.ModelValidationError.MissingModel)
  }

  test("validateAnthropicModel rejects invalid model ID format") {
    val result = BedrockClient.validateAnthropicModel("anthropic.claude 3")
    result shouldBe Left(
      BedrockClient.ModelValidationError.InvalidFormat("anthropic.claude 3")
    )
  }

  test("validateAnthropicModel rejects non-Anthropic providers") {
    val modelId = "amazon.titan-text-express-v1"
    BedrockClient.validateAnthropicModel(modelId) shouldBe
      Left(BedrockClient.ModelValidationError.UnsupportedProvider(modelId))
  }

  test("prunedToolLoopMessages should keep newest messages within budget") {
    val messages = List(
      "user" -> ("a" * 80),
      "assistant" -> ("b" * 80),
      "user" -> ("c" * 80)
    )
    val pruned = BedrockClient.prunedToolLoopMessages(messages, 120)
    pruned.length should be <= 2
    pruned.last._2 should include("c")
  }

  test("prunedToolLoopMessages should trim a single oversized tail message") {
    val messages = List("assistant" -> ("x" * 500))
    val pruned = BedrockClient.prunedToolLoopMessages(messages, 100)
    pruned should have length 1
    pruned.head._2 should include("truncated due to context budget")
  }
}
