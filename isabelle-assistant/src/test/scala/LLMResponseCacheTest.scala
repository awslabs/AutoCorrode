/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Contract tests for LLMResponseCache behavior.
 */
class LLMResponseCacheTest extends AnyFunSuite with Matchers {

  test("cache should store and retrieve entries") {
    LLMResponseCache.clear()
    LLMResponseCache.put("key", "value")
    LLMResponseCache.get("key") shouldBe Some("value")
  }

  test("cache should return None for missing entries") {
    LLMResponseCache.clear()
    LLMResponseCache.get("missing") shouldBe None
  }

  test("cache should not store known error responses") {
    LLMResponseCache.clear()
    LLMResponseCache.put("k1", "Error: failed")
    LLMResponseCache.put("k2", "Operation timed out. Please retry.")
    LLMResponseCache.put("k3", "AWS credentials are invalid")
    LLMResponseCache.get("k1") shouldBe None
    LLMResponseCache.get("k2") shouldBe None
    LLMResponseCache.get("k3") shouldBe None
  }

  test("cache should enforce max size with LRU eviction") {
    LLMResponseCache.clear()
    val max = AssistantConstants.LLM_CACHE_SIZE
    for (i <- 0 to max + 10) {
      LLMResponseCache.put(s"prompt-$i", s"response-$i")
    }
    LLMResponseCache.get("prompt-0") shouldBe None
    LLMResponseCache.get(s"prompt-${max + 10}") shouldBe Some(s"response-${max + 10}")
  }

  test("cache stats should report entry count") {
    LLMResponseCache.clear()
    LLMResponseCache.put("a", "b")
    LLMResponseCache.stats should include("1 entries")
  }

  test("cache should report zero entries after clear") {
    LLMResponseCache.clear()
    val stats = LLMResponseCache.stats
    stats should include("0 entries")
  }

  test("concurrent puts and gets should not throw and stay bounded") {
    LLMResponseCache.clear()
    val nThreads = 4
    val opsPerThread = 500
    val max = AssistantConstants.LLM_CACHE_SIZE

    val threads = for (t <- 0 until nThreads) yield new Thread(() => {
      for (i <- 0 until opsPerThread) {
        val key = s"t$t-k${i % 256}"
        LLMResponseCache.put(key, s"v$t-$i")
        val _ = LLMResponseCache.get(key)
      }
    })

    // Capture uncaught exceptions from worker threads so they surface as
    // test failures rather than silent log output.
    val uncaught = new java.util.concurrent.ConcurrentLinkedQueue[Throwable]()
    val handler: Thread.UncaughtExceptionHandler =
      (_: Thread, ex: Throwable) => { val _ = uncaught.add(ex); () }
    threads.foreach(_.setUncaughtExceptionHandler(handler))
    threads.foreach(_.start())
    threads.foreach(_.join(10000))

    uncaught shouldBe empty
    // Final cache size is bounded by maxSize regardless of concurrent pressure.
    LLMResponseCache.stats should not be empty
    val countStr = LLMResponseCache.stats.replaceAll("[^0-9]", "")
    countStr.toInt should be <= max
  }

  test("get on LRU-evicted key should return None after capacity overflow") {
    LLMResponseCache.clear()
    val max = AssistantConstants.LLM_CACHE_SIZE
    for (i <- 0 until max) {
      LLMResponseCache.put(s"k$i", s"v$i")
    }
    // Touch the oldest to bump its recency — it should survive the next eviction.
    LLMResponseCache.get("k0") shouldBe Some("v0")
    LLMResponseCache.put("overflow", "extra")
    LLMResponseCache.get("k0") shouldBe Some("v0")
    // k1 (least-recently used after the touch on k0) should have been evicted.
    LLMResponseCache.get("k1") shouldBe None
  }
}
