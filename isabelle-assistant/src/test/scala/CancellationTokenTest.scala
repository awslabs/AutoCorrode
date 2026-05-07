/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class CancellationTokenTest extends AnyFunSuite with Matchers {

  test("newly created token should not be cancelled") {
    val token = new CancellationToken
    token.isCancelled shouldBe false
  }

  test("cancel should flip isCancelled") {
    val token = new CancellationToken
    token.cancel()
    token.isCancelled shouldBe true
  }

  test("cancel should be idempotent") {
    val token = new CancellationToken
    token.cancel()
    token.cancel()
    token.isCancelled shouldBe true
  }

  test("reset should return the token to non-cancelled state") {
    val token = new CancellationToken
    token.cancel()
    token.reset()
    token.isCancelled shouldBe false
  }

  test("cancellation should be visible across threads") {
    val token = new CancellationToken
    val latch = new java.util.concurrent.CountDownLatch(1)

    val observer = new Thread(() => {
      while (!token.isCancelled) {
        Thread.sleep(1)
      }
      latch.countDown()
    })
    observer.start()

    token.cancel()
    val observed = latch.await(2, java.util.concurrent.TimeUnit.SECONDS)
    observed shouldBe true
    observer.join(1000)
  }

  test("independent tokens should not share cancellation state") {
    val a = new CancellationToken
    val b = new CancellationToken
    a.cancel()
    a.isCancelled shouldBe true
    b.isCancelled shouldBe false
  }
}
