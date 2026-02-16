/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class VerificationCacheTest extends AnyFunSuite with Matchers {

  test("cache clear should reset size to zero") {
    VerificationCache.clear()
    VerificationCache.size shouldBe 0
  }

  test("cache should round-trip by composite key") {
    VerificationCache.clear()
    val result = IQIntegration.VerificationResult.ProofSuccess(12L, "ok")
    VerificationCache.putByKey("Foo.thy", 42L, "lemma foo", "by simp", result)
    VerificationCache.getByKey("Foo.thy", 42L, "lemma foo", "by simp") shouldBe Some(result)
    VerificationCache.getByKey("Foo.thy", 42L, "lemma foo", "by auto") shouldBe None
  }

  test("cache keys should include node/id/source to avoid collisions") {
    VerificationCache.clear()
    val a = IQIntegration.VerificationResult.ProofSuccess(1L, "a")
    val b = IQIntegration.VerificationResult.ProofFailure("b")
    VerificationCache.putByKey("A.thy", 1L, "lemma x", "by simp", a)
    VerificationCache.putByKey("B.thy", 1L, "lemma x", "by simp", b)
    VerificationCache.getByKey("A.thy", 1L, "lemma x", "by simp") shouldBe Some(a)
    VerificationCache.getByKey("B.thy", 1L, "lemma x", "by simp") shouldBe Some(b)
  }

  test("cache should evict oldest entries beyond max size") {
    VerificationCache.clear()
    val max = AssistantConstants.VERIFICATION_CACHE_SIZE
    for (i <- 0 to max + 5) {
      VerificationCache.putByKey("T.thy", i.toLong, s"cmd-$i", "by simp", IQIntegration.VerificationResult.ProofSuccess(i))
    }
    VerificationCache.size should be <= max
    VerificationCache.getByKey("T.thy", 0L, "cmd-0", "by simp") shouldBe None
  }

  test("cache should provide stats") {
    VerificationCache.clear()
    val stats = VerificationCache.stats
    stats should include("0")
    stats should include("entries")
  }
}
