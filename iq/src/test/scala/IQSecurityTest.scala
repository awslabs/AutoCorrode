/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.nio.file.Files

object IQSecurityTest {
  private def assertThat(condition: Boolean, message: String): Unit = {
    if (!condition) {
      throw new RuntimeException(message)
    }
  }

  private def leftMessage[A](value: Either[String, A], context: String): String =
    value match {
      case Left(msg) => msg
      case Right(other) =>
        throw new RuntimeException(s"expected Left for $context, got Right($other)")
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

  private def testPathValidationEdgeCases(): Unit = {
    val root = Files.createTempDirectory("iq-security-path-edge-root").toRealPath()
    val nested = root.resolve("nested").resolve("new_file.thy")
    val insideNonExisting = IQSecurity.resolveMutationPath(nested.toString, List(root))
    assertThat(
      insideNonExisting.isRight,
      s"non-existing path under allowed root should still be authorized: $insideNonExisting"
    )

    val emptyPath = IQSecurity.resolveMutationPath("   ", List(root))
    assertThat(emptyPath.isLeft, "blank path should be rejected")
    assertThat(
      leftMessage(emptyPath, "blank mutation path").contains("path parameter is required"),
      s"blank-path error should be explicit: $emptyPath"
    )
  }

  private def testBindResolution(): Unit = {
    val loopback = IQSecurity.resolveBindAddress("127.0.0.1")
    assertThat(loopback.isRight, s"loopback bind should resolve: $loopback")

    val invalid = IQSecurity.resolveBindAddress("invalid host name !!!")
    assertThat(invalid.isLeft, "invalid host should fail resolution")
  }

  private def testEnvironmentParsingWithExplicitRootsAndBounds(): Unit = {
    val mutationRoot = Files.createTempDirectory("iq-security-env-mutation-root").toRealPath()
    val readRoot = Files.createTempDirectory("iq-security-env-read-root").toRealPath()

    val config = IQSecurity.fromEnvironment(
      readEnv = {
        case "IQ_MCP_BIND_HOST" => Some("127.0.0.1")
        case "IQ_MCP_ALLOW_REMOTE_BIND" => Some("true")
        case "IQ_MCP_AUTH_TOKEN" => Some(" abc123 ")
        case "IQ_MCP_ALLOWED_ROOTS" => Some(mutationRoot.toString)
        case "IQ_MCP_ALLOWED_READ_ROOTS" => Some(readRoot.toString)
        case "IQ_MCP_MAX_CLIENT_THREADS" => Some("1")
        case _ => None
      },
      cwdProvider = () => "/tmp/ignored-default-root"
    )

    assertThat(config.allowRemoteBind, "remote bind env flag should be parsed")
    assertThat(config.authToken.contains("abc123"), "auth token should be trimmed")
    assertThat(
      config.allowedMutationRoots == List(mutationRoot),
      s"explicit mutation root should be honored: ${config.allowedMutationRoots}"
    )
    assertThat(
      config.allowedReadRoots == List(readRoot),
      s"explicit read root should be honored: ${config.allowedReadRoots}"
    )
    assertThat(config.maxClientThreads == 2, "thread count should be clamped to minimum of 2")
  }

  private def testUiConfiguredRootsWhenEnvMissing(): Unit = {
    val mutationRootA = Files.createTempDirectory("iq-security-ui-mutation-a").toRealPath()
    val mutationRootB = Files.createTempDirectory("iq-security-ui-mutation-b").toRealPath()
    val readRoot = Files.createTempDirectory("iq-security-ui-read").toRealPath()

    val config = IQSecurity.fromEnvironment(
      readEnv = _ => None,
      cwdProvider = () => "/tmp/ignored-default-root",
      readUiMutationRoots = () => Some(s"${mutationRootA}\n${mutationRootB}"),
      readUiReadRoots = () => Some(readRoot.toString)
    )

    assertThat(
      config.allowedMutationRoots == List(mutationRootA, mutationRootB),
      s"UI mutation roots should be used when env is unset: ${config.allowedMutationRoots}"
    )
    assertThat(
      config.allowedReadRoots == List(readRoot),
      s"UI read roots should be used when env is unset: ${config.allowedReadRoots}"
    )
  }

  private def testEnvironmentRootsTakePrecedenceOverUiRoots(): Unit = {
    val envMutationRoot = Files.createTempDirectory("iq-security-env-first-mutation").toRealPath()
    val envReadRoot = Files.createTempDirectory("iq-security-env-first-read").toRealPath()
    val uiMutationRoot = Files.createTempDirectory("iq-security-env-first-ui-mutation").toRealPath()
    val uiReadRoot = Files.createTempDirectory("iq-security-env-first-ui-read").toRealPath()

    val config = IQSecurity.fromEnvironment(
      readEnv = {
        case "IQ_MCP_ALLOWED_ROOTS" => Some(envMutationRoot.toString)
        case "IQ_MCP_ALLOWED_READ_ROOTS" => Some(envReadRoot.toString)
        case _ => None
      },
      cwdProvider = () => "/tmp/ignored-default-root",
      readUiMutationRoots = () => Some(uiMutationRoot.toString),
      readUiReadRoots = () => Some(uiReadRoot.toString)
    )

    assertThat(
      config.allowedMutationRoots == List(envMutationRoot),
      s"environment mutation roots should override UI roots: ${config.allowedMutationRoots}"
    )
    assertThat(
      config.allowedReadRoots == List(envReadRoot),
      s"environment read roots should override UI roots: ${config.allowedReadRoots}"
    )
  }

  private def testEmptyEnvironmentRootsFallbackToUiRoots(): Unit = {
    val uiMutationRoot = Files.createTempDirectory("iq-security-empty-env-ui-mutation").toRealPath()
    val uiReadRoot = Files.createTempDirectory("iq-security-empty-env-ui-read").toRealPath()

    val config = IQSecurity.fromEnvironment(
      readEnv = {
        case "IQ_MCP_ALLOWED_ROOTS" => Some("   ")
        case "IQ_MCP_ALLOWED_READ_ROOTS" => Some("")
        case _ => None
      },
      cwdProvider = () => "/tmp/ignored-default-root",
      readUiMutationRoots = () => Some(uiMutationRoot.toString),
      readUiReadRoots = () => Some(uiReadRoot.toString)
    )

    assertThat(
      config.allowedMutationRoots == List(uiMutationRoot),
      s"empty env mutation roots should fall back to UI roots: ${config.allowedMutationRoots}"
    )
    assertThat(
      config.allowedReadRoots == List(uiReadRoot),
      s"empty env read roots should fall back to UI roots: ${config.allowedReadRoots}"
    )
  }

  def main(args: Array[String]): Unit = {
    testDefaultConfig()
    testPathAllowlist()
    testReadPathAllowlist()
    testTokenAuthorization()
    testTokenRedaction()
    testPathValidationEdgeCases()
    testBindResolution()
    testEnvironmentParsingWithExplicitRootsAndBounds()
    testUiConfiguredRootsWhenEnvMissing()
    testEnvironmentRootsTakePrecedenceOverUiRoots()
    testEmptyEnvironmentRootsFallbackToUiRoots()
    println("IQSecurityTest: all tests passed")
  }
}
