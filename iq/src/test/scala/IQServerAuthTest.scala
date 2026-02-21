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
    testServerAuthorizeMutationPathRespectsRoots()
    testServerAuthorizeReadPathRespectsRoots()
    println("IQServerAuthTest: all tests passed")
  }
}

