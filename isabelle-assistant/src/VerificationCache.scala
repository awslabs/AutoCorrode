/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/**
 * LRU cache for I/Q proof verification results.
 * Keyed by (node name, command ID, command source, proof text) to avoid
 * collisions between identical command text at different document positions.
 * Uses Java LinkedHashMap with access-order for O(1) LRU eviction.
 *
 * Cache policy:
 * - Cache stable successful verification outcomes.
 * - Do not cache transient or infra outcomes (timeout, unavailable, missing import).
 * - Do not cache failures by default; callers should re-run verification immediately.
 */
object VerificationCache {
  case class CacheKey(nodeName: String, commandId: Long, commandSource: String, proofText: String)
  case class CacheEntry(result: IQIntegration.VerificationResult, timestamp: Long)
  enum FailureCause {
    case SemanticFailure
    case InfrastructureFailure
  }
  enum ResultClass {
    case StableSuccess
    case TransientUnavailable
    case SemanticFailure
    case InfrastructureFailure
  }

  private val maxSize = AssistantConstants.VERIFICATION_CACHE_SIZE
  private val infrastructureFailureHints =
    List(
      "timeout",
      "timed out",
      "unavailable",
      "connection",
      "network",
      "transport",
      "refused",
      "temporar",
      "throttl",
      "rate limit",
      "service unavailable",
      "interrupted",
      "cancelled",
      "isar_explore"
    )

  private val cache = new java.util.LinkedHashMap[CacheKey, CacheEntry](maxSize + 1, 0.75f, true) {
    override def removeEldestEntry(eldest: java.util.Map.Entry[CacheKey, CacheEntry]): Boolean =
      this.size() > maxSize
  }

  private def keyFor(command: Command, proofText: String): CacheKey =
    CacheKey(command.node_name.node, command.id, command.source, proofText)

  private[assistant] def classifyFailure(error: String): FailureCause = {
    val normalized = Option(error).getOrElse("").toLowerCase
    if (infrastructureFailureHints.exists(normalized.contains))
      FailureCause.InfrastructureFailure
    else FailureCause.SemanticFailure
  }

  private[assistant] def classifyResult(result: IQIntegration.VerificationResult): ResultClass =
    result match {
      case IQIntegration.ProofSuccess(_, _) => ResultClass.StableSuccess
      case IQIntegration.ProofTimeout | IQIntegration.IQUnavailable | IQIntegration.MissingImport(_) =>
        ResultClass.TransientUnavailable
      case IQIntegration.ProofFailure(error) =>
        classifyFailure(error) match {
          case FailureCause.InfrastructureFailure => ResultClass.InfrastructureFailure
          case FailureCause.SemanticFailure => ResultClass.SemanticFailure
        }
    }

  private[assistant] def shouldCacheResult(result: IQIntegration.VerificationResult): Boolean =
    classifyResult(result) == ResultClass.StableSuccess

  def get(command: Command, proofText: String): Option[IQIntegration.VerificationResult] = synchronized {
    val key = keyFor(command, proofText)
    Option(cache.get(key)).map(_.result)
  }

  private[assistant] def getByKey(
    nodeName: String,
    commandId: Long,
    commandSource: String,
    proofText: String
  ): Option[IQIntegration.VerificationResult] = synchronized {
    val key = CacheKey(nodeName, commandId, commandSource, proofText)
    Option(cache.get(key)).map(_.result)
  }

  def putIfCacheable(command: Command, proofText: String, result: IQIntegration.VerificationResult): Boolean =
    synchronized {
      if (shouldCacheResult(result)) {
        val key = keyFor(command, proofText)
        cache.put(key, CacheEntry(result, System.currentTimeMillis()))
        true
      } else false
    }

  def put(command: Command, proofText: String, result: IQIntegration.VerificationResult): Unit = synchronized {
    putIfCacheable(command, proofText, result)
  }

  private[assistant] def putByKey(
    nodeName: String,
    commandId: Long,
    commandSource: String,
    proofText: String,
    result: IQIntegration.VerificationResult
  ): Unit = synchronized {
    val key = CacheKey(nodeName, commandId, commandSource, proofText)
    cache.put(key, CacheEntry(result, System.currentTimeMillis()))
  }

  def clear(): Unit = synchronized { cache.clear() }

  def size: Int = synchronized { cache.size() }

  def stats: String = synchronized { s"Cache: ${cache.size()}/$maxSize entries" }
}
