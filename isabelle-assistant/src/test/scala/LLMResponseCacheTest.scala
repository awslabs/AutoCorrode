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
}
