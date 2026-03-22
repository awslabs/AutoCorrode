/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.nio.file.Files

object IQServerAuthTest {
  private def assertThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  private val TestToken = "test-token"

  private def mkServer(
      root: java.nio.file.Path,
      token: String = TestToken
  ): IQServer = {
    mkServerWithBackend(root, token, None)
  }

  private def mkServerWithBackend(
      root: java.nio.file.Path,
      token: String = TestToken,
      capabilityBackend: Option[IQCapabilityBackend]
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
      capabilityBackendOverride = capabilityBackend
    )
  }

  private def testInternalToolFailurePreservesRequestId(): Unit = {
    val root = Files.createTempDirectory("iq-server-internal-id-root").toRealPath()
    val crashingBackend = new IQCapabilityBackend {
      override val toolNames: Set[IQToolName] = Set(IQToolName.Explore)
      override def invoke(
          toolName: IQToolName,
          params: IQToolParams
      ): Either[IQCapabilityInvocationError, IQToolResult] = {
        throw new RuntimeException("forced-test-failure")
      }
    }
    val server = mkServerWithBackend(root, capabilityBackend = Some(crashingBackend))
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
  }

  private def testResolveCommandTargetRejectsInvalidSelection(): Unit = {
    val root = Files.createTempDirectory("iq-server-resolve-invalid-target-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-resolve-invalid","method":"tools/call","params":{"name":"resolve_command_target","arguments":{"command_selection":"bogus"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "invalid selection should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
    assertThat(payload.contains("Invalid target"), s"expected invalid target message: $payload")
  }

  private def testResolveCommandTargetRequiresPathAndOffsetForFileOffset(): Unit = {
    val root = Files.createTempDirectory("iq-server-resolve-file-offset-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-resolve-missing","method":"tools/call","params":{"name":"resolve_command_target","arguments":{"command_selection":"file_offset"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing file_offset parameters should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
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
    assertThat(response.nonEmpty, "invalid selection should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
    assertThat(payload.contains("Invalid target"), s"expected invalid target message: $payload")
  }

  private def testGetContextInfoRequiresFileOffsetParameters(): Unit = {
    val root = Files.createTempDirectory("iq-server-context-file-offset-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-context-missing","method":"tools/call","params":{"name":"get_context_info","arguments":{"command_selection":"file_offset"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing file_offset parameters should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
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
    assertThat(response.nonEmpty, "missing path should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
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
    assertThat(response.nonEmpty, "invalid selection should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
    assertThat(payload.contains("Invalid target"), s"expected invalid target message: $payload")
  }

  private def testGetProofBlocksSelectionRequiresFileOffsetParameters(): Unit = {
    val root = Files.createTempDirectory("iq-server-proof-blocks-selection-file-offset-root").toRealPath()
    val server = mkServer(root)
    val request =
      """{"jsonrpc":"2.0","id":"req-proof-blocks-selection-missing","method":"tools/call","params":{"name":"get_proof_blocks","arguments":{"scope":"selection","command_selection":"file_offset"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "missing file_offset parameters should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
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
    assertThat(response.nonEmpty, "missing path should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
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
    assertThat(response.nonEmpty, "missing names should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
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
    assertThat(response.nonEmpty, "invalid severity should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
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
    assertThat(response.nonEmpty, "file scope without path should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
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
    assertThat(response.nonEmpty, "invalid boolean parameter should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
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

  def main(args: Array[String]): Unit = {
    testAuthenticateToolAcceptsCorrectToken()
    testAuthenticateToolRejectsWrongToken()
    testAuthenticateToolRejectsMissingToken()
    testToolsListIncludesAuthenticate()
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
