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

  test("decodeResolvedCommandTarget should decode selection and command metadata") {
    val decoded = IQMcpClient.decodeResolvedCommandTarget(
      Map(
        "selection" -> Map(
          "command_selection" -> "file_offset",
          "path" -> "/tmp/Foo.thy",
          "requested_offset" -> 15,
          "normalized_offset" -> 12
        ),
        "command" -> Map(
          "id" -> 42,
          "length" -> 10,
          "source" -> "lemma foo: True",
          "keyword" -> "lemma",
          "node_path" -> "/tmp/Foo.thy",
          "start_offset" -> 8,
          "end_offset" -> 18
        )
      )
    )

    decoded.selection shouldBe IQMcpClient.FileOffsetSelection(
      path = "/tmp/Foo.thy",
      requestedOffset = Some(15),
      normalizedOffset = Some(12)
    )
    decoded.command.id shouldBe 42L
    decoded.command.keyword shouldBe "lemma"
    decoded.command.nodePath shouldBe Some("/tmp/Foo.thy")
    decoded.command.startOffset shouldBe Some(8)
    decoded.command.endOffset shouldBe Some(18)
  }

  test("decodeGoalStateResult should decode structured goal information") {
    val decoded = IQMcpClient.decodeGoalStateResult(
      Map(
        "selection" -> Map("command_selection" -> "current"),
        "command" -> Map(
          "id" -> 7,
          "length" -> 5,
          "source" -> "apply simp",
          "keyword" -> "apply"
        ),
        "goal" -> Map(
          "has_goal" -> true,
          "goal_text" -> "1. x = x",
          "num_subgoals" -> 1,
          "free_vars" -> List("x"),
          "constants" -> List("HOL.eq")
        )
      )
    )

    decoded.selection shouldBe IQMcpClient.CurrentSelection
    decoded.goal.hasGoal shouldBe true
    decoded.goal.goalText shouldBe "1. x = x"
    decoded.goal.numSubgoals shouldBe 1
    decoded.goal.freeVars shouldBe List("x")
    decoded.goal.constants shouldBe List("HOL.eq")
  }

  test("decodeDiagnosticsResult should decode selection-scope diagnostics payload") {
    val decoded = IQMcpClient.decodeDiagnosticsResult(
      Map(
        "scope" -> "selection",
        "severity" -> "warning",
        "count" -> 1,
        "selection" -> Map("command_selection" -> "current"),
        "command" -> Map(
          "id" -> 11,
          "length" -> 6,
          "source" -> "by simp",
          "keyword" -> "by"
        ),
        "diagnostics" -> List(
          Map(
            "line" -> 12,
            "start_offset" -> 140,
            "end_offset" -> 145,
            "message" -> "Potentially redundant simp rule"
          )
        )
      )
    )

    decoded.scope shouldBe IQMcpClient.DiagnosticScope.Selection
    decoded.severity shouldBe IQMcpClient.DiagnosticSeverity.Warning
    decoded.count shouldBe 1
    decoded.selection shouldBe Some(IQMcpClient.CurrentSelection)
    decoded.command.map(_.id) shouldBe Some(11L)
    decoded.diagnostics should have size 1
    decoded.diagnostics.head.line shouldBe 12
    decoded.diagnostics.head.message should include("redundant")
  }
}
