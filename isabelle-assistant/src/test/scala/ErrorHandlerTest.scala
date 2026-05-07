/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ErrorHandlerTest extends AnyFunSuite with Matchers {
  
  test("validateInput should reject null input") {
    ErrorHandler.validateInput(null).isFailure shouldBe true
  }
  
  test("validateInput should reject empty input") {
    ErrorHandler.validateInput("").isFailure shouldBe true
  }
  
  test("validateInput should accept valid input") {
    ErrorHandler.validateInput("valid input").isSuccess shouldBe true
  }
  
  test("makeUserFriendly should convert timeout errors") {
    val result = ErrorHandler.makeUserFriendly("operation timed out", "test")
    result should include("timed out")
  }

  test("ChatAction.addErrorResponse round-trips error messages through makeUserFriendly") {
    // Anything containing "timed out" should come out the other end with the
    // actionable remediation hint ("Try again, increase the timeout…") so
    // the user sees the suggested fix, not the raw technical wording.
    ChatAction.clearHistory()
    ChatAction.addErrorResponse("sledgehammer timed out after 15000ms", "sledgehammer")

    val history = ChatAction.getHistory
    history.length shouldBe 1
    history.head.kind shouldBe ChatAction.ResponseKind.Error
    history.head.content should include(":set verify_timeout")
  }

  test("ChatAction.addErrorResponse translates credential errors to a credential-file hint") {
    ChatAction.clearHistory()
    ChatAction.addErrorResponse("The security token included in the request is invalid; unauthorized access denied", "chat")

    val history = ChatAction.getHistory
    history.length shouldBe 1
    history.head.kind shouldBe ChatAction.ResponseKind.Error
    history.head.content should (include("credentials") or include("AWS_ACCESS_KEY_ID"))
  }

  test("makeUserFriendly should handle null message") {
    val result = ErrorHandler.makeUserFriendly(null, "test")
    result should include("test failed")
    result should include("unknown error")
  }

  test("truncateError should handle long messages") {
    val long = "x" * 1000
    val result = ErrorHandler.truncateError(long)
    // take(N) then strip trailing whitespace and append a single-char ellipsis
    // leaves the overall budget within N + 1 characters.
    result.length should be <= (AssistantConstants.MAX_ERROR_MESSAGE_LENGTH + 1)
    result should endWith("…")
  }
}
