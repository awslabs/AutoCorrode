/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/**
 * LRU cache for I/Q proof verification results.
 * Keyed by (node name, command ID, command source, proof text) to avoid
 * collisions between identical command text at different document positions.
 * Uses Java LinkedHashMap with access-order for O(1) LRU eviction.
 */
object VerificationCache {
  case class CacheKey(nodeName: String, commandId: Long, commandSource: String, proofText: String)
  case class CacheEntry(result: IQIntegration.VerificationResult, timestamp: Long)

  private val maxSize = AssistantConstants.VERIFICATION_CACHE_SIZE

  private val cache = new java.util.LinkedHashMap[CacheKey, CacheEntry](maxSize + 1, 0.75f, true) {
    override def removeEldestEntry(eldest: java.util.Map.Entry[CacheKey, CacheEntry]): Boolean =
      this.size() > maxSize
  }

  def get(command: Command, proofText: String): Option[IQIntegration.VerificationResult] = synchronized {
    val key = CacheKey(command.node_name.node, command.id, command.source, proofText)
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

  def put(command: Command, proofText: String, result: IQIntegration.VerificationResult): Unit = synchronized {
    val key = CacheKey(command.node_name.node, command.id, command.source, proofText)
    cache.put(key, CacheEntry(result, System.currentTimeMillis()))
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
