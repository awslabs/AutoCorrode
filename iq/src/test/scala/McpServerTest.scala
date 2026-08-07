/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/* Standalone tests for the generic MCP server (McpServer / McpToolRegistry /
   McpProtocol / McpTool). No jEdit, no IQ tools — exercises the transport,
   registration, and dispatch in isolation, driving the server through
   processRequestForTest (no sockets). */

// McpServer/McpProtocol/McpTool/ErrorCodes now live in `package isabelle`.
import isabelle._

object McpServerTest {
  private def assertThat(cond: Boolean, msg: String): Unit =
    if (!cond) throw new RuntimeException(msg)

  private val Token = "secret-token"

  /** JSON codec backed by isabelle.JSON, same as the IQ host. */
  private val codec: McpJsonCodec = new McpJsonCodec {
    def parse(line: String): JSON.T = JSON.parse(line)
    def format(value: Any): String = JSON.Format(value)
  }

  private def config = McpServerConfig(port = 0, authToken = Token, maxClientThreads = 2)

  private def echoTool(name: String): McpTool =
    McpTool(name, s"echo $name", Map("type" -> "object"),
      params => Right(McpToolResult.fromMap(Map("text" -> s"$name:${params.toMap.getOrElse("x", "")}"))))

  private def server(tools: List[McpTool] = Nil,
                     paramTransform: Map[String, Any] => Map[String, Any] = identity): McpServer = {
    val reg = new McpToolRegistry()
    val s = new McpServer(config, codec, registry = reg, paramTransform = paramTransform)
    tools.foreach(t => assertThat(s.register(t).isRight, s"register ${t.name} failed"))
    s
  }

  private def call(s: McpServer, req: String): String =
    s.processRequestForTest(req).getOrElse("<none>")


  /* ---- McpToolRegistry ---- */

  private def testRegistryRegisterAndGet(): Unit = {
    val r = new McpToolRegistry()
    assertThat(r.register(echoTool("a")).isRight, "register a")
    assertThat(r.get("a").isDefined, "get a")
    assertThat(r.get("missing").isEmpty, "get missing")
  }

  private def testRegistryRejectsDuplicate(): Unit = {
    val r = new McpToolRegistry()
    assertThat(r.register(echoTool("dup")).isRight, "first register")
    r.register(echoTool("dup")) match {
      case Left(m) => assertThat(m.contains("already registered"), s"dup msg: $m")
      case Right(_) => throw new RuntimeException("duplicate register should fail")
    }
  }

  private def testRegistryReservesAuthenticate(): Unit = {
    val r = new McpToolRegistry()
    r.register(echoTool("authenticate")) match {
      case Left(m) => assertThat(m.contains("reserved"), s"reserved msg: $m")
      case Right(_) => throw new RuntimeException("authenticate must be reserved")
    }
  }

  private def testRegistryRejectsEmptyName(): Unit = {
    val r = new McpToolRegistry()
    assertThat(r.register(echoTool("  ")).isLeft, "empty name must fail")
  }

  private def testRegistryUnregister(): Unit = {
    val r = new McpToolRegistry()
    val _ = r.register(echoTool("x"))
    r.unregister("x")
    assertThat(r.get("x").isEmpty, "x gone after unregister")
  }

  private def testRegistryRegistrationOrder(): Unit = {
    val r = new McpToolRegistry()
    List("zebra", "alpha", "middle").foreach(n => { val _ = r.register(echoTool(n)) })
    val names = r.toolDefinitions.map(_("name").asInstanceOf[String])
    assertThat(names == List("zebra", "alpha", "middle"),
      s"toolDefinitions must keep registration order (not sorted): $names")
  }

  private def testRegistryRegisterAllStopsAtFirstFailure(): Unit = {
    val r = new McpToolRegistry()
    val _ = r.register(echoTool("b"))
    r.registerAll(List(echoTool("a"), echoTool("b"), echoTool("c"))) match {
      case Left(m) => assertThat(m.contains("b"), s"registerAll should fail on b: $m")
      case Right(_) => throw new RuntimeException("registerAll should fail on duplicate b")
    }
    assertThat(r.get("a").isDefined, "a registered before the failure")
    assertThat(r.get("c").isEmpty, "c not registered after the failure")
  }

  private def testRegistryInvokeUnknown(): Unit = {
    val r = new McpToolRegistry()
    r.invoke("nope", McpToolParams.empty) match {
      case Left(McpInvocationError.UnknownTool(n)) => assertThat(n == "nope", s"unknown name: $n")
      case other => throw new RuntimeException(s"expected UnknownTool, got $other")
    }
  }

  private def testRegistryInvokeDoesNotCatch(): Unit = {
    val r = new McpToolRegistry()
    val _ = r.register(McpTool("boom", "d", Map("type" -> "object"),
      _ => throw new RuntimeException("kaboom")))
    try {
      val _ = r.invoke("boom", McpToolParams.empty)
      throw new RuntimeException("invoke must NOT catch handler exceptions")
    } catch {
      case e: RuntimeException if e.getMessage == "kaboom" => () // expected: propagated
    }
  }


  /* ---- McpProtocol decode ---- */

  private def testDecodeRequestValid(): Unit = {
    McpProtocol.decodeJsonRpcRequest(JSON.parse(
      """{"jsonrpc":"2.0","id":"7","method":"tools/list","params":{"a":1}}""")) match {
      case Right(r) =>
        assertThat(r.method == "tools/list", "method")
        assertThat(r.id.contains("7"), "id")
      case Left(m) => throw new RuntimeException(s"valid request rejected: $m")
    }
  }

  private def testDecodeRequestErrors(): Unit = {
    def err(s: String): String =
      McpProtocol.decodeJsonRpcRequest(JSON.parse(s)).left.getOrElse("")
    assertThat(err("""{"id":"1"}""").contains("missing 'method'"), "missing method")
    assertThat(err("""{"method":123}""").contains("must be a string"), "method type")
    assertThat(err("""{"method":"m","params":5}""").contains("'params' must be an object"), "params type")
    assertThat(err("""[]""").contains("must be a JSON object"), "non-object payload")
  }

  private def testDecodeToolCall(): Unit = {
    def tc(s: String) = McpProtocol.decodeJsonRpcRequest(JSON.parse(s)).flatMap(McpProtocol.decodeToolCall)
    tc("""{"method":"tools/call","id":"1","params":{"name":"foo","arguments":{"k":"v"}}}""") match {
      case Right(c) => assertThat(c.toolName == "foo" && c.arguments.contains("k"), "tool call decode")
      case Left(m) => throw new RuntimeException(s"valid tool call rejected: $m")
    }
    assertThat(tc("""{"method":"tools/call","id":"1","params":{}}""").left.getOrElse("")
      .contains("missing required field 'name'"), "missing name")
    assertThat(tc("""{"method":"tools/call","id":"1","params":{"name":"x","arguments":5}}""").left.getOrElse("")
      .contains("'arguments' must be an object"), "arguments type")
  }


  /* ---- McpServer end-to-end (processRequestForTest) ---- */

  private def testInitialize(): Unit = {
    val p = call(server(), """{"jsonrpc":"2.0","id":"1","method":"initialize","params":{}}""")
    assertThat(p.contains("\"protocolVersion\":\"2024-11-05\""), s"protocolVersion: $p")
    assertThat(p.contains("\"name\":\"isabelle-mcp-server\""), s"serverInfo name: $p")
  }

  private def testPing(): Unit = {
    val p = call(server(), """{"jsonrpc":"2.0","id":"1","method":"ping"}""")
    assertThat(p.contains("\"status\":\"ok\"") && p.contains("\"timestamp\""), s"ping: $p")
  }

  private def testToolsListPrependsAuthenticateThenOrder(): Unit = {
    val s = server(List(echoTool("tool_b"), echoTool("tool_a")))
    val p = call(s, """{"jsonrpc":"2.0","id":"1","method":"tools/list"}""")
    val iAuth = p.indexOf("\"name\":\"authenticate\"")
    val iB = p.indexOf("\"name\":\"tool_b\"")
    val iA = p.indexOf("\"name\":\"tool_a\"")
    assertThat(iAuth >= 0 && iB >= 0 && iA >= 0, s"all present: $p")
    assertThat(iAuth < iB && iB < iA, s"order authenticate, tool_b, tool_a: $p")
  }

  private def testToolsListReflectsRuntimeRegistration(): Unit = {
    val s = server()
    assertThat(!call(s, """{"jsonrpc":"2.0","id":"1","method":"tools/list"}""").contains("\"late\""),
      "tool 'late' should be absent before registration")
    assertThat(s.register(echoTool("late")).isRight, "register late")
    assertThat(call(s, """{"jsonrpc":"2.0","id":"2","method":"tools/list"}""").contains("\"name\":\"late\""),
      "tool 'late' should appear after runtime registration")
  }

  private def testToolCallSuccess(): Unit = {
    val s = server(List(echoTool("echo")))
    val p = call(s, """{"jsonrpc":"2.0","id":"1","method":"tools/call","params":{"name":"echo","arguments":{"x":"hi"}}}""")
    assertThat(p.contains("\"result\"") && p.contains("echo:hi"), s"tool success: $p")
    assertThat(!p.contains("\"isError\""), s"success must not be isError: $p")
  }

  private def testToolCallValidationIsError(): Unit = {
    val bad = McpTool("bad", "d", Map("type" -> "object"), _ => Left("bad params here"))
    val p = call(server(List(bad)), """{"jsonrpc":"2.0","id":"1","method":"tools/call","params":{"name":"bad","arguments":{}}}""")
    assertThat(p.contains("\"isError\":true") && p.contains("bad params here"), s"isError result: $p")
    assertThat(!p.contains("\"error\""), s"validation must not be a JSON-RPC error: $p")
  }

  private def testToolCallUnknown(): Unit = {
    val p = call(server(), """{"jsonrpc":"2.0","id":"1","method":"tools/call","params":{"name":"ghost","arguments":{}}}""")
    assertThat(p.contains("\"error\"") && p.contains("-32601") && p.contains("Unknown tool: ghost"), s"unknown tool: $p")
  }

  private def testToolCallExceptionIsInternalError(): Unit = {
    val boom = McpTool("boom", "d", Map("type" -> "object"), _ => throw new RuntimeException("explode"))
    val p = call(server(List(boom)), """{"jsonrpc":"2.0","id":"99","method":"tools/call","params":{"name":"boom","arguments":{}}}""")
    assertThat(p.contains("\"error\"") && p.contains("-32603"), s"internal error code: $p")
    assertThat(p.contains("\"99\""), s"id preserved: $p")
    assertThat(p.contains("explode"), s"message surfaced: $p")
  }

  private def testAuthenticateBuiltinAcceptAndReject(): Unit = {
    val ok = call(server(), s"""{"jsonrpc":"2.0","id":"1","method":"tools/call","params":{"name":"authenticate","arguments":{"token":"$Token"}}}""")
    assertThat(ok.contains("\"result\"") && ok.contains("Authenticated successfully"), s"auth ok: $ok")
    val bad = call(server(), """{"jsonrpc":"2.0","id":"2","method":"tools/call","params":{"name":"authenticate","arguments":{"token":"wrong"}}}""")
    assertThat(bad.contains("\"error\"") && bad.contains("Invalid authentication token"), s"auth bad: $bad")
    val missing = call(server(), """{"jsonrpc":"2.0","id":"3","method":"tools/call","params":{"name":"authenticate","arguments":{}}}""")
    assertThat(missing.contains("\"error\""), s"auth missing: $missing")
  }

  private def testInvalidMethodType(): Unit = {
    val p = call(server(), """{"jsonrpc":"2.0","id":"1","method":123}""")
    assertThat(p.contains("\"error\"") && p.contains("'method' must be a string"), s"invalid method type: $p")
  }

  private def testParamTransformApplied(): Unit = {
    // transform upper-cases the "x" arg; the handler echoes it back.
    val tf: Map[String, Any] => Map[String, Any] = m =>
      m.map { case (k, v: String) => k -> v.toUpperCase; case other => other }
    val s = server(List(echoTool("echo")), paramTransform = tf)
    val p = call(s, """{"jsonrpc":"2.0","id":"1","method":"tools/call","params":{"name":"echo","arguments":{"x":"hi"}}}""")
    assertThat(p.contains("echo:HI"), s"paramTransform should upcase before handler: $p")
  }

  private def testNotificationNoResponse(): Unit = {
    val r = server().processRequestForTest("""{"jsonrpc":"2.0","method":"notifications/initialized"}""")
    assertThat(r.isEmpty, s"notification must produce no response: $r")
  }

  /* ---- progress notifications ---- */

  /** A progress-aware tool that emits two progress dicts before returning. */
  private def progressTool(name: String): McpTool =
    McpTool(name, s"progress $name", Map("type" -> "object"),
      (_: McpToolParams, sink: McpProgress.Sink) => {
        sink(JSON.Object("progress" -> 1, "total" -> 2, "message" -> "half"))
        sink(JSON.Object("progress" -> 2, "total" -> 2, "message" -> "done"))
        Right(McpToolResult.fromMap(Map("text" -> "ok")))
      })

  private def testProgressEmittedWhenTokenPresent(): Unit = {
    val s = server(List(progressTool("prog")))
    val (sent, resp) = s.processRequestForTestCapturing(
      """{"jsonrpc":"2.0","id":"7","method":"tools/call",""" +
      """"params":{"name":"prog","arguments":{},"_meta":{"progressToken":"pt-7"}}}""")
    // Two progress notifications, each carrying the injected token and our dict.
    assertThat(sent.length == 2, s"expected 2 progress notifications, got ${sent.length}: $sent")
    assertThat(sent.forall(_.contains("notifications/progress")), s"wrong method: $sent")
    assertThat(sent.forall(_.contains("\"progressToken\"")), s"token not injected: $sent")
    assertThat(sent.forall(_.contains("pt-7")), s"token value wrong: $sent")
    assertThat(sent(0).contains("\"message\"") && sent(0).contains("half"), s"dict not passed through: ${sent(0)}")
    assertThat(sent(1).contains("done"), s"second dict not passed through: ${sent(1)}")
    // The final result is still returned normally, after the notifications.
    assertThat(resp.exists(r => r.contains("\"id\"") && r.contains("ok")), s"final result missing: $resp")
  }

  private def testNoProgressWithoutToken(): Unit = {
    val s = server(List(progressTool("prog")))
    // Same tool, but no _meta.progressToken: the sink is a no-op, so nothing is
    // pushed — only the final result comes back.
    val (sent, resp) = s.processRequestForTestCapturing(
      """{"jsonrpc":"2.0","id":"8","method":"tools/call","params":{"name":"prog","arguments":{}}}""")
    assertThat(sent.isEmpty, s"no progress expected without a token, got: $sent")
    assertThat(resp.exists(_.contains("ok")), s"final result missing: $resp")
  }

  private def testProgressTokenInjectionOverridesHostKey(): Unit = {
    // A tool that puts its own bogus progressToken in the dict — the wire token
    // must win (the server injects the canonical one last).
    val tool = McpTool("ptok", "d", Map("type" -> "object"),
      (_: McpToolParams, sink: McpProgress.Sink) => {
        sink(JSON.Object("progress" -> 1, "progressToken" -> "BOGUS"))
        Right(McpToolResult.fromMap(Map("text" -> "ok")))
      })
    val (sent, _) = server(List(tool)).processRequestForTestCapturing(
      """{"jsonrpc":"2.0","id":"9","method":"tools/call",""" +
      """"params":{"name":"ptok","arguments":{},"_meta":{"progressToken":42}}}""")
    assertThat(sent.length == 1, s"expected 1 notification: $sent")
    assertThat(sent.head.contains("42") && !sent.head.contains("BOGUS"),
      s"wire token must override host key: ${sent.head}")
  }

  def main(args: Array[String]): Unit = {
    testRegistryRegisterAndGet()
    testRegistryRejectsDuplicate()
    testRegistryReservesAuthenticate()
    testRegistryRejectsEmptyName()
    testRegistryUnregister()
    testRegistryRegistrationOrder()
    testRegistryRegisterAllStopsAtFirstFailure()
    testRegistryInvokeUnknown()
    testRegistryInvokeDoesNotCatch()
    testDecodeRequestValid()
    testDecodeRequestErrors()
    testDecodeToolCall()
    testInitialize()
    testPing()
    testToolsListPrependsAuthenticateThenOrder()
    testToolsListReflectsRuntimeRegistration()
    testToolCallSuccess()
    testToolCallValidationIsError()
    testToolCallUnknown()
    testToolCallExceptionIsInternalError()
    testAuthenticateBuiltinAcceptAndReject()
    testInvalidMethodType()
    testParamTransformApplied()
    testNotificationNoResponse()
    testProgressEmittedWhenTokenPresent()
    testNoProgressWithoutToken()
    testProgressTokenInjectionOverridesHostKey()
    println("McpServerTest: all tests passed")
  }
}
