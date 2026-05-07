/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class IQMcpClientTest extends AnyFunSuite with Matchers {

  test("callExplore should short-circuit with the cancelled marker when the token is already cancelled") {
    // When the caller trips the token before invoking the MCP call, the
    // cancellable path must short-circuit without attempting any I/O and
    // return the documented marker string so callers (IQIntegration) can
    // recognise cancellation and distinguish it from real errors.
    val token = new CancellationToken
    token.cancel()

    val result = IQMcpClient.callExplore(
      query = IQMcpClient.ExploreQueryType.Proof,
      arguments = "by simp",
      timeoutMs = 100L,
      token = Some(token)
    )

    result shouldBe Left(IQMcpClient.CancelledErrorMessage)
  }

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

  test(
    "parseToolCallResponse should provide actionable mutation-root guidance for denied writes"
  ) {
    val response =
      """{"jsonrpc":"2.0","id":"1","error":{"code":-32603,"message":"Tool execution error: Path '/tmp/forbidden/Foo.thy' is outside allowed mutation roots: /Users/dominic/Programming.nosync/AutoCorrode"}}"""

    val parsed = IQMcpClient.parseToolCallResponse(
      response,
      toolName = Some("write_file")
    )

    parsed.isLeft shouldBe true
    val message = parsed.swap.toOption.getOrElse("")
    message should include("Tool 'write_file' failed.")
    message should include("outside allowed mutation roots")
    message should include("Plugins -> Plugin Options -> I/Q -> Security")
    message should include("no Isabelle/jEdit restart")
  }

  test(
    "parseToolCallResponse should provide actionable read-root guidance for denied reads"
  ) {
    val response =
      """{"jsonrpc":"2.0","id":"1","error":{"code":-32603,"message":"Path '/tmp/forbidden/Foo.thy' is outside allowed read roots: /Users/dominic/Programming.nosync/AutoCorrode"}}"""

    val parsed = IQMcpClient.parseToolCallResponse(
      response,
      toolName = Some("read_file")
    )

    parsed.isLeft shouldBe true
    val message = parsed.swap.toOption.getOrElse("")
    message should include("Tool 'read_file' failed.")
    message should include("outside allowed read roots")
    message should include("Plugins -> Plugin Options -> I/Q -> Security")
    message should include("no Isabelle/jEdit restart")
  }

  test("decodeExploreResult should decode typed explore fields") {
    val result = IQMcpDecoder.decodeExploreResult(
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
    val decoded = IQMcpDecoder.decodeResolvedCommandTarget(
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

  test("decodeContextInfoResult should decode structured goal information") {
    val decoded = IQMcpDecoder.decodeContextInfoResult(
      Map(
        "selection" -> Map("command_selection" -> "current"),
        "command" -> Map(
          "id" -> 7,
          "length" -> 5,
          "source" -> "apply simp",
          "keyword" -> "apply"
        ),
        "in_proof_context" -> true,
        "has_goal" -> true,
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
    decoded.inProofContext shouldBe true
    decoded.hasGoal shouldBe true
    decoded.goal.hasGoal shouldBe true
    decoded.goal.goalText shouldBe "1. x = x"
    decoded.goal.numSubgoals shouldBe 1
    decoded.goal.freeVars shouldBe List("x")
    decoded.goal.constants shouldBe List("HOL.eq")
  }

  test("decodeDiagnosticsResult should decode selection-scope diagnostics payload") {
    val decoded = IQMcpDecoder.decodeDiagnosticsResult(
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

  test("decodeOpenFileResult should surface every server field including tracked") {
    val payload: Map[String, Any] = Map(
      "path" -> "/tmp/Foo.thy",
      "created" -> true,
      "overwritten" -> false,
      "opened" -> true,
      "in_view" -> true,
      "tracked" -> true,
      "message" -> "File opened successfully"
    )

    val result = IQMcpDecoder.decodeOpenFileResult(payload)

    result.path shouldBe "/tmp/Foo.thy"
    result.created shouldBe true
    result.overwritten shouldBe false
    result.opened shouldBe true
    result.inView shouldBe true
    result.tracked shouldBe true
    result.message shouldBe "File opened successfully"
  }

  test("decodeOpenFileResult should default tracked to false when server omits it") {
    val payload: Map[String, Any] = Map(
      "path" -> "/tmp/Foo.thy",
      "created" -> true,
      "opened" -> true,
      "in_view" -> true,
      "message" -> ""
    )

    val result = IQMcpDecoder.decodeOpenFileResult(payload)

    result.tracked shouldBe false
  }

  test(
    "decodeOpenFileResult should capture partial-success response with tracking timeout"
  ) {
    val payload: Map[String, Any] = Map(
      "path" -> "/tmp/Slow.thy",
      "created" -> true,
      "overwritten" -> false,
      "opened" -> true,
      "in_view" -> true,
      "tracked" -> false,
      "message" -> "File open was requested but tracking did not stabilize before timeout"
    )

    val result = IQMcpDecoder.decodeOpenFileResult(payload)

    result.created shouldBe true
    result.opened shouldBe true
    result.tracked shouldBe false
    result.message should include("tracking did not stabilize")
  }
}
