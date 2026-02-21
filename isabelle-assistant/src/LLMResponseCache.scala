/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * LRU cache for LLM responses to avoid redundant API calls.
 * Uses LinkedHashMap (access-ordered) for O(1) LRU eviction.
 * Does not cache responses that look like errors.
 */
object LLMResponseCache {

  private case class CacheEntry(response: String, timestamp: Long, hitCount: Int)

  private val maxSize = AssistantConstants.LLM_CACHE_SIZE
  private val maxAge = AssistantConstants.LLM_CACHE_EXPIRY_HOURS * 60 * 60 * 1000L

  private val cache = new java.util.LinkedHashMap[String, CacheEntry](maxSize + 1, 0.75f, true) {
    override def removeEldestEntry(eldest: java.util.Map.Entry[String, CacheEntry]): Boolean =
      size() > maxSize
  }

  def get(prompt: String): Option[String] = synchronized {
    Option(cache.get(prompt)).flatMap { entry =>
      if (System.currentTimeMillis() - entry.timestamp < maxAge) {
        cache.put(prompt, entry.copy(hitCount = entry.hitCount + 1))
        Some(entry.response)
      } else {
        cache.remove(prompt)
        None
      }
    }
  }

  def put(prompt: String, response: String): Unit = synchronized {
    if (!looksLikeError(response)) {
      val _ = cache.put(prompt, CacheEntry(response, System.currentTimeMillis(), 1))
    }
  }

  /** Heuristic: don't cache responses that are error messages. */
  private val errorPrefixes = List(
    "Error:", "Could not parse response",
    "Operation timed out", "Network connection failed",
    "AWS credentials are invalid", "The selected AI model is not available",
    "AWS service limit reached", "Received invalid response"
  )

  private def looksLikeError(response: String): Boolean =
    errorPrefixes.exists(response.startsWith)

  def clear(): Unit = synchronized { cache.clear() }

  def stats: String = synchronized { s"Cache: ${cache.size()} entries" }

  def cleanup(): Unit = synchronized {
    val now = System.currentTimeMillis()
    val it = cache.entrySet().iterator()
    while (it.hasNext) {
      if (now - it.next().getValue.timestamp > maxAge) it.remove()
    }
  }
}
