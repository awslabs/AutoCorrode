/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.io.File
import java.net.InetAddress
import java.nio.file.{Files, Path, Paths}

import scala.util.Try

/**
 * Security configuration and helper utilities for the I/Q MCP server.
 */
case class IQServerSecurityConfig(
  bindHost: String,
  allowRemoteBind: Boolean,
  authToken: Option[String],
  allowedMutationRoots: List[Path],
  allowedReadRoots: List[Path],
  maxClientThreads: Int
)

object IQSecurity {
  private val BindHostEnv = "IQ_MCP_BIND_HOST"
  private val AllowRemoteBindEnv = "IQ_MCP_ALLOW_REMOTE_BIND"
  private val AuthTokenEnv = "IQ_MCP_AUTH_TOKEN"
  private val AllowedRootsEnv = "IQ_MCP_ALLOWED_ROOTS"
  private val AllowedReadRootsEnv = "IQ_MCP_ALLOWED_READ_ROOTS"
  private val MaxClientThreadsEnv = "IQ_MCP_MAX_CLIENT_THREADS"

  private val TrueValues = Set("1", "true", "yes", "on")
  private val DefaultBindHost = "127.0.0.1"
  private val DefaultMaxClientThreads = 16

  private def parseBoolean(value: String, defaultValue: Boolean): Boolean = {
    val normalized = value.trim.toLowerCase
    if (normalized.isEmpty) defaultValue else TrueValues.contains(normalized)
  }

  private def canonicalizePath(path: Path): Path = {
    val absolute = if (path.isAbsolute) path else path.toAbsolutePath
    val normalized = absolute.normalize()

    if (Files.exists(normalized)) {
      normalized.toRealPath()
    } else {
      var ancestor: Path = normalized
      while (ancestor != null && !Files.exists(ancestor)) {
        ancestor = ancestor.getParent
      }

      if (ancestor == null) normalized
      else {
        val canonicalAncestor = ancestor.toRealPath()
        canonicalAncestor.resolve(ancestor.relativize(normalized)).normalize()
      }
    }
  }

  private def parsePathList(raw: Option[String]): List[Path] =
    raw.toList
      .flatMap(_.split("[\\n,]+").toList)
      .flatMap(_.split(java.util.regex.Pattern.quote(java.io.File.pathSeparator)).toList)
      .map(_.trim)
      .filter(_.nonEmpty)
      .map(path => canonicalizePath(Paths.get(path)))

  private def parsePositiveInt(raw: Option[String], defaultValue: Int): Int = {
    raw
      .flatMap(value => Try(value.trim.toInt).toOption)
      .filter(_ > 0)
      .getOrElse(defaultValue)
  }

  def fromEnvironment(
    readEnv: String => Option[String] = key => Option(System.getenv(key)),
    cwdProvider: () => String = () => new File(".").getAbsolutePath,
    readUiMutationRoots: () => Option[String] = () => None,
    readUiReadRoots: () => Option[String] = () => None
  ): IQServerSecurityConfig = {
    def nonEmpty(value: Option[String]): Option[String] =
      value.map(_.trim).filter(_.nonEmpty)

    val bindHost = readEnv(BindHostEnv).map(_.trim).filter(_.nonEmpty).getOrElse(DefaultBindHost)
    val allowRemoteBind = readEnv(AllowRemoteBindEnv).exists(v => parseBoolean(v, defaultValue = false))
    val authToken = readEnv(AuthTokenEnv).map(_.trim).filter(_.nonEmpty)

    val configuredMutationRoots =
      parsePathList(nonEmpty(readEnv(AllowedRootsEnv)).orElse(nonEmpty(readUiMutationRoots())))

    val defaultRoot = canonicalizePath(Paths.get(cwdProvider()))
    val allowedMutationRoots =
      if (configuredMutationRoots.nonEmpty) configuredMutationRoots.distinct
      else List(defaultRoot)
    val configuredReadRoots =
      parsePathList(nonEmpty(readEnv(AllowedReadRootsEnv)).orElse(nonEmpty(readUiReadRoots())))
    val allowedReadRoots =
      if (configuredReadRoots.nonEmpty) configuredReadRoots.distinct
      else allowedMutationRoots
    val maxClientThreads =
      math.max(2, parsePositiveInt(readEnv(MaxClientThreadsEnv), DefaultMaxClientThreads))

    IQServerSecurityConfig(
      bindHost = bindHost,
      allowRemoteBind = allowRemoteBind,
      authToken = authToken,
      allowedMutationRoots = allowedMutationRoots,
      allowedReadRoots = allowedReadRoots,
      maxClientThreads = maxClientThreads
    )
  }

  private def resolveAuthorizedPath(
    rawPath: String,
    allowedRoots: List[Path],
    rootLabel: String
  ): Either[String, Path] = {
    val requested = rawPath.trim
    if (requested.isEmpty) return Left("path parameter is required")

    val canonicalPathTry = Try {
      canonicalizePath(Paths.get(requested))
    }

    canonicalPathTry.toEither.left.map(ex => s"Failed to resolve path '$requested': ${ex.getMessage}").flatMap { canonicalPath =>
      val isAllowed = allowedRoots.exists(root => canonicalPath.startsWith(root))
      if (isAllowed) Right(canonicalPath)
      else {
        val roots = allowedRoots.map(_.toString).mkString(", ")
        Left(s"Path '$canonicalPath' is outside allowed $rootLabel roots: $roots")
      }
    }
  }

  def resolveMutationPath(rawPath: String, allowedRoots: List[Path]): Either[String, Path] = {
    resolveAuthorizedPath(rawPath, allowedRoots, "mutation")
  }

  def resolveReadPath(rawPath: String, allowedRoots: List[Path]): Either[String, Path] = {
    resolveAuthorizedPath(rawPath, allowedRoots, "read")
  }

  def resolveBindAddress(bindHost: String): Either[String, InetAddress] = {
    Try(InetAddress.getByName(bindHost.trim))
      .toEither
      .left
      .map(ex => s"Failed to resolve bind host '$bindHost': ${ex.getMessage}")
  }

  def isTokenAuthorized(expectedToken: Option[String], providedToken: Option[String]): Boolean = {
    expectedToken match {
      case None => true
      case Some(expected) => providedToken.exists(_.trim == expected)
    }
  }

  def redactAuthToken(jsonLine: String): String = {
    jsonLine
      .replaceAll("\"auth_token\"\\s*:\\s*\"[^\"]*\"", "\"auth_token\":\"***\"")
  }
}
