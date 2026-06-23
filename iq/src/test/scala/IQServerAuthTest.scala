/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.nio.file.Files

object IQServerAuthTest {
  private def assertThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  /** Assert a tool-handler validation failure: a successful JSON-RPC response
    * carrying an MCP tool result flagged with isError:true (NOT a JSON-RPC
    * protocol-level "error"). Tool handlers forward their Left(msg) this way so
    * the message is surfaced to the LLM rather than swallowed by the client. */
  private def assertToolError(payload: String, context: String): Unit = {
    assertThat(
      payload.contains("\"isError\":true"),
      s"$context: expected tool error result (isError:true): $payload"
    )
    assertThat(
      !payload.contains("\"error\""),
      s"$context: handler validation should not be a JSON-RPC error: $payload"
    )
  }

  private val TestToken = "test-token"

  private def mkServer(
      root: java.nio.file.Path,
      token: String = TestToken
  ): IQServer = {
    mkServerWithRegistry(root, token, None)
  }

  private def mkServerWithRegistry(
      root: java.nio.file.Path,
      token: String = TestToken,
      registry: Option[McpToolRegistry]
  ): IQServer = {
    val config = IQServerSecurityConfig(
      authToken = token,
      allowedMutationRoots = List(root),
      allowedReadRoots = List(root),
      maxClientThreads = 2
    )
    new IQServer(
      port = 0,
      securityConfig = config,
      registryOverride = registry
    )
  }

  private def testInternalToolFailurePreservesRequestId(): Unit = {
    val root = Files.createTempDirectory("iq-server-internal-id-root").toRealPath()
    // Register a throwing 'explore' tool. McpToolRegistry.invoke does not catch
    // handler exceptions, so the throw propagates to McpServer.handleToolCall's
    // try/catch and surfaces as INTERNAL_ERROR with the id preserved.
    val crashingRegistry = new McpToolRegistry()
    val _ = crashingRegistry.register(McpTool(
      "explore", "crash for test", Map("type" -> "object"),
      _ => throw new RuntimeException("forced-test-failure")))
    val server = mkServerWithRegistry(root, registry = Some(crashingRegistry))
    val request =
      """{"jsonrpc":"2.0","id":"req-internal-1","method":"tools/call","params":{"name":"explore","arguments":{"query":"sledgehammer","command_selection":"current"}}}"""
    val response = server.processRequestForTest(request)

    assertThat(
      response.nonEmpty,
      "internal tool failure should return an error response"
    )
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
    assertThat(
      payload.contains("req-internal-1"),
      s"internal error response must preserve request id: $payload"
    )
    assertThat(
      payload.contains("forced-test-failure"),
      s"internal error should include underlying failure message: $payload"
    )
  }

  private def testToolsListIncludesResolveCommandTarget(): Unit = {
    val root = Files.createTempDirectory("iq-server-tools-list-root").toRealPath()
    val server = mkServer(root)
    val request = """{"jsonrpc":"2.0","id":"req-tools","method":"tools/list"}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "tools/list should return response")
    val payload = response.get
    assertThat(
      payload.contains("\"name\":\"resolve_command_target\""),
      s"tools/list should expose resolve_command_target: $payload"
    )
    assertThat(
      !payload.contains("\"name\":\"get_goal_state\""),
      s"tools/list should not expose deprecated get_goal_state: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_context_info\""),
      s"tools/list should expose get_context_info: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_entities\""),
      s"tools/list should expose get_entities: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_type_at_selection\""),
      s"tools/list should expose get_type_at_selection: $payload"
    )
    assertThat(
      !payload.contains("\"name\":\"get_proof_block\""),
      s"tools/list should not expose deprecated get_proof_block: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_proof_blocks\""),
      s"tools/list should expose get_proof_blocks: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_proof_context\""),
      s"tools/list should expose get_proof_context: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_definitions\""),
      s"tools/list should expose get_definitions: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_diagnostics\""),
      s"tools/list should expose get_diagnostics: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"set_auto_save\""),
      s"tools/list should expose set_auto_save: $payload"
    )
  }

  private def testResolveCommandTargetRejectsInvalidSelection(): Unit = {
    val root = Files.createTempDirectory("iq-server-resolve-invalid-target-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-resolve-invalid","method":"tools/call","params":{"name":"resolve_command_target","arguments":{"command_selection":"bogus"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "invalid selection should return a response")
    val payload = response.get
    assertToolError(payload, "resolve_command_target invalid selection")
    assertThat(payload.contains("Invalid target"), s"expected invalid target message: $payload")
  }

  private def testResolveCommandTargetRequiresPathAndOffsetForFileOffset(): Unit = {
    val root = Files.createTempDirectory("iq-server-resolve-file-offset-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-resolve-missing","method":"tools/call","params":{"name":"resolve_command_target","arguments":{"command_selection":"file_offset"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing file_offset parameters should return a response")
    val payload = response.get
    assertToolError(payload, "resolve_command_target file_offset params")
    assertThat(
      payload.contains("file_offset target requires path and offset parameters"),
      s"expected file_offset parameter validation message: $payload"
    )
  }

  private def testGetContextInfoRejectsInvalidSelection(): Unit = {
    val root = Files.createTempDirectory("iq-server-context-invalid-target-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-context-invalid","method":"tools/call","params":{"name":"get_context_info","arguments":{"command_selection":"bogus"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "invalid selection should return a response")
    val payload = response.get
    assertToolError(payload, "get_context_info invalid selection")
    assertThat(payload.contains("Invalid target"), s"expected invalid target message: $payload")
  }

  private def testGetContextInfoRequiresFileOffsetParameters(): Unit = {
    val root = Files.createTempDirectory("iq-server-context-file-offset-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-context-missing","method":"tools/call","params":{"name":"get_context_info","arguments":{"command_selection":"file_offset"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing file_offset parameters should return a response")
    val payload = response.get
    assertToolError(payload, "get_context_info file_offset params")
    assertThat(
      payload.contains("file_offset target requires path and offset parameters"),
      s"expected file_offset parameter validation message: $payload"
    )
  }

  private def testGetEntitiesRequiresPath(): Unit = {
    val root = Files.createTempDirectory("iq-server-entities-missing-path-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-entities-missing","method":"tools/call","params":{"name":"get_entities","arguments":{}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing path should return a response")
    val payload = response.get
    assertToolError(payload, "get_entities missing path")
    assertThat(
      payload.contains("Missing required parameter: path"),
      s"expected missing path validation message: $payload"
    )
  }

  private def testGetTypeAtSelectionRejectsInvalidSelection(): Unit = {
    val root = Files.createTempDirectory("iq-server-type-invalid-target-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-type-invalid","method":"tools/call","params":{"name":"get_type_at_selection","arguments":{"command_selection":"bogus"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "invalid selection should return a response")
    val payload = response.get
    assertToolError(payload, "get_type_at_selection invalid selection")
    assertThat(payload.contains("Invalid target"), s"expected invalid target message: $payload")
  }

  private def testGetProofBlocksSelectionRequiresFileOffsetParameters(): Unit = {
    val root = Files.createTempDirectory("iq-server-proof-blocks-selection-file-offset-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-proof-blocks-selection-missing","method":"tools/call","params":{"name":"get_proof_blocks","arguments":{"scope":"selection","command_selection":"file_offset"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing file_offset parameters should return a response")
    val payload = response.get
    assertToolError(payload, "get_proof_blocks selection file_offset params")
    assertThat(
      payload.contains("file_offset target requires path and offset parameters"),
      s"expected file_offset parameter validation message: $payload"
    )
  }

  private def testGetProofBlocksRequiresPath(): Unit = {
    val root = Files.createTempDirectory("iq-server-proof-blocks-missing-path-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-proof-blocks-missing","method":"tools/call","params":{"name":"get_proof_blocks","arguments":{"scope":"file"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing path should return a response")
    val payload = response.get
    assertToolError(payload, "get_proof_blocks missing path")
    assertThat(
      payload.contains("scope='file' requires parameter: path"),
      s"expected missing path validation message: $payload"
    )
  }

  private def testGetDefinitionsRequiresNames(): Unit = {
    val root = Files.createTempDirectory("iq-server-definitions-missing-names-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-defs-missing","method":"tools/call","params":{"name":"get_definitions","arguments":{"command_selection":"current"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing names should return a response")
    val payload = response.get
    assertToolError(payload, "get_definitions missing names")
    assertThat(
      payload.contains("Missing required parameter: names"),
      s"expected missing names validation message: $payload"
    )
  }

  private def testGetDiagnosticsRejectsInvalidSeverity(): Unit = {
    val root = Files.createTempDirectory("iq-server-diagnostics-invalid-severity-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-diag-bad-severity","method":"tools/call","params":{"name":"get_diagnostics","arguments":{"severity":"info"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "invalid severity should return a response")
    val payload = response.get
    assertToolError(payload, "get_diagnostics invalid severity")
    assertThat(
      payload.contains("Parameter 'severity' must be either 'error' or 'warning'"),
      s"expected severity validation message: $payload"
    )
  }

  private def testGetDiagnosticsFileScopeRequiresPath(): Unit = {
    val root = Files.createTempDirectory("iq-server-diagnostics-file-scope-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-diag-missing-path","method":"tools/call","params":{"name":"get_diagnostics","arguments":{"severity":"error","scope":"file"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "file scope without path should return a response")
    val payload = response.get
    assertToolError(payload, "get_diagnostics file scope missing path")
    assertThat(
      payload.contains("scope='file' requires parameter: path"),
      s"expected missing path validation message: $payload"
    )
  }

  private def testServerAuthorizeMutationPathRespectsRoots(): Unit = {
    val root = Files.createTempDirectory("iq-server-authz-mutation-root").toRealPath()
    val server = mkServer(root)
    val inside = root.resolve("ok").resolve("Demo.thy").toString
    val outside = root.resolve("..").resolve("escape.thy").normalize().toString

    assertThat(
      server.authorizeMutationPathForTest("open_file(create_if_missing=true)", inside).isRight,
      "mutation path inside allowed root should be accepted"
    )
    assertThat(
      server.authorizeMutationPathForTest("open_file(create_if_missing=true)", outside).isLeft,
      "mutation path outside allowed root should be rejected"
    )
  }

  private def testServerAuthorizeReadPathRespectsRoots(): Unit = {
    val root = Files.createTempDirectory("iq-server-authz-read-root").toRealPath()
    val server = mkServer(root)
    val inside = root.resolve("session").resolve("Theory.thy").toString
    val outside = root.resolve("..").resolve("outside.thy").normalize().toString

    assertThat(
      server.authorizeReadPathForTest("read_file", inside).isRight,
      "read path inside allowed root should be accepted"
    )
    assertThat(
      server.authorizeReadPathForTest("read_file", outside).isLeft,
      "read path outside allowed root should be rejected"
    )
  }

  private def testInvalidRequestMethodTypeRejected(): Unit = {
    val root = Files.createTempDirectory("iq-server-invalid-method-type-root").toRealPath()
    val server = mkServer(root)
    val request = """{"jsonrpc":"2.0","id":"req-invalid-method","method":123}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "invalid method type should return error response")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
    assertThat(
      payload.contains("'method' must be a string"),
      s"expected invalid method type message: $payload"
    )
  }

  private def testOpenFileRejectsInvalidBooleanParam(): Unit = {
    val root = Files.createTempDirectory("iq-server-open-file-bool-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-open-bool","method":"tools/call","params":{"name":"open_file","arguments":{"path":"demo.thy","create_if_missing":"maybe"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "invalid boolean parameter should return a response")
    val payload = response.get
    assertToolError(payload, "open_file invalid boolean param")
    assertThat(
      payload.contains("Invalid parameter 'create_if_missing': expected boolean"),
      s"expected boolean validation message: $payload"
    )
  }

  private def testAuthenticateToolAcceptsCorrectToken(): Unit = {
    val root = Files.createTempDirectory("iq-server-auth-tool-ok-root").toRealPath()
    val server = mkServer(root)
    val request =
      s"""{"jsonrpc":"2.0","id":"req-auth-ok","method":"tools/call","params":{"name":"authenticate","arguments":{"token":"$TestToken"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "authenticate with correct token should return response")
    val payload = response.get
    assertThat(payload.contains("\"result\""), s"expected success result: $payload")
    assertThat(payload.contains("Authenticated successfully"), s"expected success message: $payload")
  }

  private def testAuthenticateToolRejectsWrongToken(): Unit = {
    val root = Files.createTempDirectory("iq-server-auth-tool-bad-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-auth-bad","method":"tools/call","params":{"name":"authenticate","arguments":{"token":"wrong-token"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "authenticate with wrong token should return error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
    assertThat(payload.contains("Invalid authentication token"), s"expected invalid token message: $payload")
  }

  private def testAuthenticateToolRejectsMissingToken(): Unit = {
    val root = Files.createTempDirectory("iq-server-auth-tool-missing-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-auth-missing","method":"tools/call","params":{"name":"authenticate","arguments":{}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "authenticate with missing token should return error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
  }

  private def testToolsListIncludesAuthenticate(): Unit = {
    val root = Files.createTempDirectory("iq-server-auth-tool-list-root").toRealPath()
    val server = mkServer(root)
    val request = """{"jsonrpc":"2.0","id":"req-tools-auth","method":"tools/list"}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "tools/list should return response")
    val payload = response.get
    assertThat(payload.contains("\"name\":\"authenticate\""),
      s"tools/list should include authenticate tool: $payload")
  }

  /** Guards tools/list ELEMENT ORDER after the registry extraction: a
    * sortBy(name) or unordered map would reorder the array on the wire. The
    * existing contains-only checks cannot catch this. authenticate must be
    * first; the IQ tools then follow in source order, then the repl_* tools. */
  private def testToolsListPreservesOrder(): Unit = {
    val root = Files.createTempDirectory("iq-server-tools-order-root").toRealPath()
    val server = mkServer(root)
    val request = """{"jsonrpc":"2.0","id":"req-order","method":"tools/list"}"""
    val payload = server.processRequestForTest(request).get
    // Indices of each name's first occurrence must be strictly increasing.
    val expected = List(
      "authenticate", "list_files", "get_command_info", "get_document_info",
      "open_file", "read_file", "write_file", "resolve_command_target",
      "get_context_info", "get_entities", "get_type_at_selection",
      "get_proof_blocks", "get_proof_context", "get_definitions",
      "get_diagnostics", "explore", "save_file", "set_auto_save",
      "get_processing_status", "get_sorry_positions",
      "repl_connect", "repl_init", "repl_init_from_source", "repl_fork",
      "repl_step", "repl_show", "repl_state", "repl_text", "repl_edit",
      "repl_replay", "repl_truncate", "repl_back", "repl_merge", "repl_remove",
      "repl_list", "repl_sledgehammer", "repl_find_theorems", "repl_timeout",
      "repl_raw")
    val positions = expected.map(n => n -> payload.indexOf("\"name\":\"" + n + "\""))
    positions.foreach { case (n, i) =>
      assertThat(i >= 0, s"tools/list missing tool $n: $payload")
    }
    positions.sliding(2).foreach {
      case List((a, ia), (b, ib)) =>
        assertThat(ia < ib, s"tools/list order wrong: $a (@$ia) must precede $b (@$ib)")
      case _ =>
    }
  }

  /** Guards that the I/R tools' required-parameter validation survived the move
    * to IRTools (a silent-default extractor would dispatch step(repl,"") instead
    * of returning a validation error). */
  private def testReplStepRequiresIsarText(): Unit = {
    val root = Files.createTempDirectory("iq-server-repl-step-missing-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-repl-step-missing","method":"tools/call","params":{"name":"repl_step","arguments":{"repl":"R"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing isar_text should return a response")
    val payload = response.get
    assertToolError(payload, "repl_step missing isar_text")
    assertThat(
      payload.contains("Missing required parameter: isar_text"),
      s"expected missing isar_text validation message: $payload"
    )
  }

  def main(args: Array[String]): Unit = {
    testAuthenticateToolAcceptsCorrectToken()
    testAuthenticateToolRejectsWrongToken()
    testAuthenticateToolRejectsMissingToken()
    testToolsListIncludesAuthenticate()
    testToolsListPreservesOrder()
    testReplStepRequiresIsarText()
    testInternalToolFailurePreservesRequestId()
    testToolsListIncludesResolveCommandTarget()
    testResolveCommandTargetRejectsInvalidSelection()
    testResolveCommandTargetRequiresPathAndOffsetForFileOffset()
    testGetContextInfoRejectsInvalidSelection()
    testGetContextInfoRequiresFileOffsetParameters()
    testGetEntitiesRequiresPath()
    testGetTypeAtSelectionRejectsInvalidSelection()
    testGetProofBlocksSelectionRequiresFileOffsetParameters()
    testGetProofBlocksRequiresPath()
    testGetDefinitionsRequiresNames()
    testGetDiagnosticsRejectsInvalidSeverity()
    testGetDiagnosticsFileScopeRequiresPath()
    testServerAuthorizeMutationPathRespectsRoots()
    testServerAuthorizeReadPathRespectsRoots()
    testInvalidRequestMethodTypeRejected()
    testOpenFileRejectsInvalidBooleanParam()
    println("IQServerAuthTest: all tests passed")
  }
}
