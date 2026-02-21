/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.nio.file.Files

object IQServerAuthTest {
  private def assertThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  private def mkServer(
      root: java.nio.file.Path,
      token: Option[String]
  ): IQServer = {
    val config = IQServerSecurityConfig(
      bindHost = "127.0.0.1",
      allowRemoteBind = false,
      authToken = token,
      allowedMutationRoots = List(root),
      allowedReadRoots = List(root),
      maxClientThreads = 2
    )
    new IQServer(port = 0, securityConfig = config)
  }

  private def testUnauthorizedRequestReturnsErrorWithId(): Unit = {
    val root = Files.createTempDirectory("iq-server-auth-root").toRealPath()
    val server = mkServer(root, Some("secret-token"))
    val request = """{"jsonrpc":"2.0","id":"req-1","method":"initialize"}"""
    val response = server.processRequestForTest(request)

    assertThat(response.nonEmpty, "unauthorized request with id should return an error response")
    val payload = response.get
    assertThat(payload.contains("Unauthorized request"), s"missing unauthorized message: $payload")
    assertThat(payload.contains("req-1"), s"response should preserve request id: $payload")
  }

  private def testUnauthorizedNotificationReturnsNone(): Unit = {
    val root = Files.createTempDirectory("iq-server-auth-notify-root").toRealPath()
    val server = mkServer(root, Some("secret-token"))
    val request = """{"jsonrpc":"2.0","method":"notifications/initialized"}"""
    val response = server.processRequestForTest(request)
    assertThat(response.isEmpty, s"unauthorized notification must not receive response: $response")
  }

  private def testAuthorizedRequestAcceptsTopLevelToken(): Unit = {
    val root = Files.createTempDirectory("iq-server-auth-top-token-root").toRealPath()
    val server = mkServer(root, Some("secret-token"))
    val request =
      """{"jsonrpc":"2.0","id":"req-2","method":"initialize","auth_token":"secret-token"}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "authorized initialize request should return response")
    val payload = response.get
    assertThat(payload.contains("\"result\""), s"expected successful result payload: $payload")
    assertThat(!payload.contains("Unauthorized request"), s"request should not be rejected: $payload")
  }

  private def testAuthorizedRequestAcceptsParamsToken(): Unit = {
    val root = Files.createTempDirectory("iq-server-auth-params-token-root").toRealPath()
    val server = mkServer(root, Some("secret-token"))
    val request =
      """{"jsonrpc":"2.0","id":"req-3","method":"tools/list","params":{"auth_token":"secret-token"}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "authorized tools/list request should return response")
    val payload = response.get
    assertThat(payload.contains("\"result\""), s"expected successful tools/list result payload: $payload")
  }

  private def testNoAuthConfiguredAllowsRequests(): Unit = {
    val root = Files.createTempDirectory("iq-server-auth-disabled-root").toRealPath()
    val server = mkServer(root, None)
    val request = """{"jsonrpc":"2.0","id":"req-4","method":"initialize"}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "request should pass when auth token is disabled")
    assertThat(response.get.contains("\"result\""), s"expected successful result payload: ${response.get}")
  }

  private def testToolsListIncludesResolveCommandTarget(): Unit = {
    val root = Files.createTempDirectory("iq-server-tools-list-root").toRealPath()
    val server = mkServer(root, None)
    val request = """{"jsonrpc":"2.0","id":"req-tools","method":"tools/list"}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "tools/list should return response")
    val payload = response.get
    assertThat(
      payload.contains("\"name\":\"resolve_command_target\""),
      s"tools/list should expose resolve_command_target: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_goal_state\""),
      s"tools/list should expose get_goal_state: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_context_info\""),
      s"tools/list should expose get_context_info: $payload"
    )
    assertThat(
      payload.contains("\"name\":\"get_entities\""),
      s"tools/list should expose get_entities: $payload"
    )
  }

  private def testResolveCommandTargetRejectsInvalidSelection(): Unit = {
    val root = Files.createTempDirectory("iq-server-resolve-invalid-target-root").toRealPath()
    val server = mkServer(root, None)
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
    val server = mkServer(root, None)
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

  private def testGetGoalStateRejectsInvalidSelection(): Unit = {
    val root = Files.createTempDirectory("iq-server-goal-invalid-target-root").toRealPath()
    val server = mkServer(root, None)
    val request =
      """{"jsonrpc":"2.0","id":"req-goal-invalid","method":"tools/call","params":{"name":"get_goal_state","arguments":{"command_selection":"bogus"}}}"""
    val response = server.processRequestForTest(request)
    assertThat(response.nonEmpty, "invalid selection should return JSON-RPC error")
    val payload = response.get
    assertThat(payload.contains("\"error\""), s"expected error payload: $payload")
    assertThat(payload.contains("Invalid target"), s"expected invalid target message: $payload")
  }

  private def testGetContextInfoRequiresFileOffsetParameters(): Unit = {
    val root = Files.createTempDirectory("iq-server-context-file-offset-root").toRealPath()
    val server = mkServer(root, None)
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
    val server = mkServer(root, None)
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

  private def testServerAuthorizeMutationPathRespectsRoots(): Unit = {
    val root = Files.createTempDirectory("iq-server-authz-mutation-root").toRealPath()
    val server = mkServer(root, None)
    val inside = root.resolve("ok").resolve("Demo.thy").toString
    val outside = root.resolve("..").resolve("escape.thy").normalize().toString

    assertThat(
      server.authorizeMutationPathForTest("create_file", inside).isRight,
      "mutation path inside allowed root should be accepted"
    )
    assertThat(
      server.authorizeMutationPathForTest("create_file", outside).isLeft,
      "mutation path outside allowed root should be rejected"
    )
  }

  private def testServerAuthorizeReadPathRespectsRoots(): Unit = {
    val root = Files.createTempDirectory("iq-server-authz-read-root").toRealPath()
    val server = mkServer(root, None)
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

  def main(args: Array[String]): Unit = {
    testUnauthorizedRequestReturnsErrorWithId()
    testUnauthorizedNotificationReturnsNone()
    testAuthorizedRequestAcceptsTopLevelToken()
    testAuthorizedRequestAcceptsParamsToken()
    testNoAuthConfiguredAllowsRequests()
    testToolsListIncludesResolveCommandTarget()
    testResolveCommandTargetRejectsInvalidSelection()
    testResolveCommandTargetRequiresPathAndOffsetForFileOffset()
    testGetGoalStateRejectsInvalidSelection()
    testGetContextInfoRequiresFileOffsetParameters()
    testGetEntitiesRequiresPath()
    testServerAuthorizeMutationPathRespectsRoots()
    testServerAuthorizeReadPathRespectsRoots()
    println("IQServerAuthTest: all tests passed")
  }
}
