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
}
