/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

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
  private val ttlMs = AssistantConstants.VERIFICATION_CACHE_TTL_MS

  /** Test seam: overridable clock so TTL tests don't have to block. */
  private[assistant] var nowMs: () => Long = () => System.currentTimeMillis()

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

  private def keyFor(
      command: IQMcpClient.CommandInfo,
      proofText: String
  ): CacheKey =
    CacheKey(
      command.nodePath.getOrElse(""),
      command.id,
      command.source,
      proofText
    )

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

  /** Look up, then evict if the entry has passed its TTL. Returns `None`
    * both when the key is absent and when the stored entry is too old. */
  private def getFresh(key: CacheKey): Option[IQIntegration.VerificationResult] = {
    Option(cache.get(key)) match {
      case None => None
      case Some(entry) =>
        if (nowMs() - entry.timestamp > ttlMs) {
          cache.remove(key)
          None
        } else Some(entry.result)
    }
  }

  def get(
      command: IQMcpClient.CommandInfo,
      proofText: String
  ): Option[IQIntegration.VerificationResult] = synchronized {
    getFresh(keyFor(command, proofText))
  }

  private[assistant] def getByKey(
    nodeName: String,
    commandId: Long,
    commandSource: String,
    proofText: String
  ): Option[IQIntegration.VerificationResult] = synchronized {
    getFresh(CacheKey(nodeName, commandId, commandSource, proofText))
  }

  def putIfCacheable(
      command: IQMcpClient.CommandInfo,
      proofText: String,
      result: IQIntegration.VerificationResult
  ): Boolean =
    synchronized {
      if (shouldCacheResult(result)) {
        val key = keyFor(command, proofText)
        cache.put(key, CacheEntry(result, nowMs()))
        true
      } else false
    }

  def put(
      command: IQMcpClient.CommandInfo,
      proofText: String,
      result: IQIntegration.VerificationResult
  ): Unit = synchronized {
    val _ = putIfCacheable(command, proofText, result)
  }

  private[assistant] def putByKey(
    nodeName: String,
    commandId: Long,
    commandSource: String,
    proofText: String,
    result: IQIntegration.VerificationResult
  ): Unit = synchronized {
    val key = CacheKey(nodeName, commandId, commandSource, proofText)
    val _ = cache.put(key, CacheEntry(result, nowMs()))
  }

  /** Invalidate every entry whose node path matches the given name.
    * Called after a theory file has been edited so that stale cached
    * outcomes for that theory cannot satisfy later look-ups. */
  def invalidateNode(nodeName: String): Int = synchronized {
    if (nodeName == null || nodeName.isEmpty) 0
    else {
      val it = cache.entrySet().iterator()
      var removed = 0
      while (it.hasNext) {
        val e = it.next()
        if (e.getKey.nodeName == nodeName) {
          it.remove()
          removed += 1
        }
      }
      removed
    }
  }

  def clear(): Unit = synchronized { cache.clear() }

  def size: Int = synchronized { cache.size() }

  def stats: String = synchronized { s"Cache: ${cache.size()}/$maxSize entries" }
}
