/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.nio.file.Files

object IQSecurityTest {
  private def assertThat(condition: Boolean, message: String): Unit = {
    if (!condition) {
      throw new RuntimeException(message)
    }
  }

  private def testDefaultConfig(): Unit = {
    val config = IQSecurity.fromEnvironment(
      readEnv = _ => None,
      cwdProvider = () => "/tmp/iq-default-root"
    )

    assertThat(config.bindHost == "127.0.0.1", "default bind host should be loopback")
    assertThat(!config.allowRemoteBind, "remote bind should be disabled by default")
    assertThat(config.authToken.isEmpty, "auth token should be disabled by default")
    assertThat(config.allowedMutationRoots.nonEmpty, "default mutation root should be set")
    assertThat(config.allowedReadRoots.nonEmpty, "default read root should be set")
    assertThat(config.allowedReadRoots == config.allowedMutationRoots, "default read roots should match mutation roots")
    assertThat(config.maxClientThreads >= 2, "max client threads should be bounded and positive")
  }

  private def testPathAllowlist(): Unit = {
    val root = Files.createTempDirectory("iq-security-root").toRealPath()

    val insidePath = root.resolve("theories").resolve("Demo.thy").toString
    val insideResult = IQSecurity.resolveMutationPath(insidePath, List(root))
    assertThat(insideResult.isRight, s"expected in-root path to be allowed: $insideResult")

    val outsidePath = root.resolve("..").resolve("escape.thy").normalize().toString
    val outsideResult = IQSecurity.resolveMutationPath(outsidePath, List(root))
    assertThat(outsideResult.isLeft, s"expected out-of-root path to be rejected: $outsideResult")
  }

  private def testReadPathAllowlist(): Unit = {
    val root = Files.createTempDirectory("iq-security-read-root").toRealPath()

    val insidePath = root.resolve("session").resolve("Theory.thy").toString
    val insideResult = IQSecurity.resolveReadPath(insidePath, List(root))
    assertThat(insideResult.isRight, s"expected in-read-root path to be allowed: $insideResult")

    val outsidePath = root.resolve("..").resolve("outside.thy").normalize().toString
    val outsideResult = IQSecurity.resolveReadPath(outsidePath, List(root))
    assertThat(outsideResult.isLeft, s"expected out-of-read-root path to be rejected: $outsideResult")
  }

  private def testTokenAuthorization(): Unit = {
    assertThat(IQSecurity.isTokenAuthorized(None, None), "requests should pass when auth is disabled")
    assertThat(!IQSecurity.isTokenAuthorized(Some("secret"), None), "missing token should be rejected")
    assertThat(!IQSecurity.isTokenAuthorized(Some("secret"), Some("wrong")), "wrong token should be rejected")
    assertThat(IQSecurity.isTokenAuthorized(Some("secret"), Some("secret")), "matching token should pass")
  }

  private def testTokenRedaction(): Unit = {
    val input = """{"jsonrpc":"2.0","auth_token":"super-secret","method":"initialize"}"""
    val redacted = IQSecurity.redactAuthToken(input)
    assertThat(!redacted.contains("super-secret"), "logs should not contain auth token")
    assertThat(redacted.contains("\"auth_token\":\"***\""), "auth token should be masked in logs")
  }

  def main(args: Array[String]): Unit = {
    testDefaultConfig()
    testPathAllowlist()
    testReadPathAllowlist()
    testTokenAuthorization()
    testTokenRedaction()
    println("IQSecurityTest: all tests passed")
  }
}
