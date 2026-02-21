/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class IQMcpClientTest extends AnyFunSuite with Matchers {

  test("parseToolCallResponse should decode embedded JSON payload") {
    val response =
      """{"jsonrpc":"2.0","id":"1","result":{"content":[{"type":"text","text":"{\"success\":true,\"results\":\"Try this: by simp (10 ms)\",\"message\":\"ok\",\"timed_out\":false}"}]}}"""

    val parsed = IQMcpClient.parseToolCallResponse(response)

    parsed.isRight shouldBe true
    val payload = parsed.toOption.getOrElse(Map.empty[String, Any])
    payload.get("success") shouldBe Some(true)
    payload.get("message") shouldBe Some("ok")
    payload.get("timed_out") shouldBe Some(false)
  }

  test("parseToolCallResponse should surface JSON-RPC error messages") {
    val response =
      """{"jsonrpc":"2.0","id":"1","error":{"code":-32600,"message":"Unauthorized request"}}"""

    val parsed = IQMcpClient.parseToolCallResponse(response)

    parsed.isLeft shouldBe true
    parsed.swap.toOption.getOrElse("") should include("Unauthorized request")
  }

  test("decodeExploreResult should decode typed explore fields") {
    val result = IQMcpClient.decodeExploreResult(
      Map(
        "success" -> true,
        "results" -> "proof state",
        "message" -> "done",
        "timed_out" -> false,
        "error" -> ""
      )
    )

    result.success shouldBe true
    result.results shouldBe "proof state"
    result.message shouldBe "done"
    result.timedOut shouldBe false
    result.error shouldBe None
  }
}
