/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import java.util.concurrent.{CountDownLatch, TimeUnit}
import java.util.concurrent.atomic.AtomicInteger

class IQOperationLifecycleTest extends AnyFunSuite with Matchers {

  test("complete should invoke callback and deactivate exactly once") {
    val completionLatch = new CountDownLatch(1)
    val deactivateLatch = new CountDownLatch(1)
    val deactivateCount = new AtomicInteger(0)
    val values = scala.collection.mutable.ListBuffer[String]()

    val lifecycle = new IQOperationLifecycle[String](
      onComplete = value => {
        values.synchronized { values += value }
        completionLatch.countDown()
      },
      deactivate = () => {
        deactivateCount.incrementAndGet()
        deactivateLatch.countDown()
      },
      forkThread = IQOperationLifecycle.forkJvmThread,
      dispatchToGui = IQOperationLifecycle.runInline
    )

    lifecycle.complete("first")
    lifecycle.complete("second")

    completionLatch.await(1, TimeUnit.SECONDS) shouldBe true
    deactivateLatch.await(1, TimeUnit.SECONDS) shouldBe true
    Thread.sleep(50)

    values.synchronized { values.toList } shouldBe List("first")
    deactivateCount.get shouldBe 1
  }

  test("non-timeout completion should win over timeout watcher") {
    val completionLatch = new CountDownLatch(1)
    val deactivateLatch = new CountDownLatch(1)
    val deactivateCount = new AtomicInteger(0)
    val values = scala.collection.mutable.ListBuffer[String]()

    val lifecycle = new IQOperationLifecycle[String](
      onComplete = value => {
        values.synchronized { values += value }
        completionLatch.countDown()
      },
      deactivate = () => {
        deactivateCount.incrementAndGet()
        deactivateLatch.countDown()
      },
      forkThread = IQOperationLifecycle.forkJvmThread,
      dispatchToGui = IQOperationLifecycle.runInline
    )

    lifecycle.forkTimeout(name = "iq-lifecycle-timeout-1", timeoutMs = 200)("timeout")
    lifecycle.complete("success")

    completionLatch.await(1, TimeUnit.SECONDS) shouldBe true
    deactivateLatch.await(1, TimeUnit.SECONDS) shouldBe true
    Thread.sleep(300)

    values.synchronized { values.toList } shouldBe List("success")
    deactivateCount.get shouldBe 1
  }

  test("timeout completion should deactivate exactly once and ignore late completions") {
    val completionLatch = new CountDownLatch(1)
    val deactivateLatch = new CountDownLatch(1)
    val deactivateCount = new AtomicInteger(0)
    val values = scala.collection.mutable.ListBuffer[String]()

    val lifecycle = new IQOperationLifecycle[String](
      onComplete = value => {
        values.synchronized { values += value }
        completionLatch.countDown()
      },
      deactivate = () => {
        deactivateCount.incrementAndGet()
        deactivateLatch.countDown()
      },
      forkThread = IQOperationLifecycle.forkJvmThread,
      dispatchToGui = IQOperationLifecycle.runInline
    )

    lifecycle.forkTimeout(name = "iq-lifecycle-timeout-2", timeoutMs = 50)("timeout")

    completionLatch.await(1, TimeUnit.SECONDS) shouldBe true
    deactivateLatch.await(1, TimeUnit.SECONDS) shouldBe true

    lifecycle.complete("late")
    Thread.sleep(50)

    values.synchronized { values.toList } shouldBe List("timeout")
    deactivateCount.get shouldBe 1
  }
}
