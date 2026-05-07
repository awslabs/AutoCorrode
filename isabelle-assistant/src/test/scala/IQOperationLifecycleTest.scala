/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import java.util.concurrent.{CountDownLatch, TimeUnit}
import java.util.concurrent.atomic.AtomicInteger

class IQOperationLifecycleTest extends AnyFunSuite with Matchers {

  test("complete should invoke callback and deactivate exactly once") {
    // First-fire latch counts down on the first onComplete; the "extra"
    // latch counts down only on any second-or-later onComplete, letting us
    // assert quiescence via `.await(...) == false` rather than Thread.sleep.
    val completionLatch = new CountDownLatch(1)
    val extraCompletionLatch = new CountDownLatch(1)
    val deactivateLatch = new CountDownLatch(1)
    val extraDeactivateLatch = new CountDownLatch(1)
    val deactivateCount = new AtomicInteger(0)
    val values = scala.collection.mutable.ListBuffer[String]()

    val lifecycle = new IQOperationLifecycle[String](
      onComplete = value => {
        values.synchronized { values += value }
        if (completionLatch.getCount > 0) completionLatch.countDown()
        else extraCompletionLatch.countDown()
      },
      deactivate = () => {
        deactivateCount.incrementAndGet()
        if (deactivateLatch.getCount > 0) deactivateLatch.countDown()
        else extraDeactivateLatch.countDown()
      },
      forkThread = IQOperationLifecycle.forkJvmThread,
      dispatchToGui = IQOperationLifecycle.runInline
    )

    lifecycle.complete("first")
    lifecycle.complete("second")

    completionLatch.await(1, TimeUnit.SECONDS) shouldBe true
    deactivateLatch.await(1, TimeUnit.SECONDS) shouldBe true
    // Extra-fire latches must NOT count down within a generous window.
    extraCompletionLatch.await(100, TimeUnit.MILLISECONDS) shouldBe false
    extraDeactivateLatch.await(100, TimeUnit.MILLISECONDS) shouldBe false

    values.synchronized { values.toList } shouldBe List("first")
    deactivateCount.get shouldBe 1
  }

  test("non-timeout completion should win over timeout watcher") {
    val completionLatch = new CountDownLatch(1)
    val extraCompletionLatch = new CountDownLatch(1)
    val deactivateLatch = new CountDownLatch(1)
    val extraDeactivateLatch = new CountDownLatch(1)
    val deactivateCount = new AtomicInteger(0)
    val values = scala.collection.mutable.ListBuffer[String]()

    val lifecycle = new IQOperationLifecycle[String](
      onComplete = value => {
        values.synchronized { values += value }
        if (completionLatch.getCount > 0) completionLatch.countDown()
        else extraCompletionLatch.countDown()
      },
      deactivate = () => {
        deactivateCount.incrementAndGet()
        if (deactivateLatch.getCount > 0) deactivateLatch.countDown()
        else extraDeactivateLatch.countDown()
      },
      forkThread = IQOperationLifecycle.forkJvmThread,
      dispatchToGui = IQOperationLifecycle.runInline
    )

    lifecycle.forkTimeout(name = "iq-lifecycle-timeout-1", timeoutMs = 200)("timeout")
    lifecycle.complete("success")

    completionLatch.await(1, TimeUnit.SECONDS) shouldBe true
    deactivateLatch.await(1, TimeUnit.SECONDS) shouldBe true
    // The 200ms timeout watcher must not fire after we've already
    // completed: wait past its deadline and confirm no extra callback.
    extraCompletionLatch.await(400, TimeUnit.MILLISECONDS) shouldBe false
    extraDeactivateLatch.await(10, TimeUnit.MILLISECONDS) shouldBe false

    values.synchronized { values.toList } shouldBe List("success")
    deactivateCount.get shouldBe 1
  }

  test("timeout completion should deactivate exactly once and ignore late completions") {
    val completionLatch = new CountDownLatch(1)
    val extraCompletionLatch = new CountDownLatch(1)
    val deactivateLatch = new CountDownLatch(1)
    val extraDeactivateLatch = new CountDownLatch(1)
    val deactivateCount = new AtomicInteger(0)
    val values = scala.collection.mutable.ListBuffer[String]()

    val lifecycle = new IQOperationLifecycle[String](
      onComplete = value => {
        values.synchronized { values += value }
        if (completionLatch.getCount > 0) completionLatch.countDown()
        else extraCompletionLatch.countDown()
      },
      deactivate = () => {
        deactivateCount.incrementAndGet()
        if (deactivateLatch.getCount > 0) deactivateLatch.countDown()
        else extraDeactivateLatch.countDown()
      },
      forkThread = IQOperationLifecycle.forkJvmThread,
      dispatchToGui = IQOperationLifecycle.runInline
    )

    lifecycle.forkTimeout(name = "iq-lifecycle-timeout-2", timeoutMs = 50)("timeout")

    completionLatch.await(1, TimeUnit.SECONDS) shouldBe true
    deactivateLatch.await(1, TimeUnit.SECONDS) shouldBe true

    lifecycle.complete("late")
    // A second callback must not fire from the late completion — the
    // lifecycle should have latched after the timeout. Wait a generous
    // window and confirm neither the extra-complete nor extra-deactivate
    // latch is released.
    extraCompletionLatch.await(100, TimeUnit.MILLISECONDS) shouldBe false
    extraDeactivateLatch.await(10, TimeUnit.MILLISECONDS) shouldBe false

    values.synchronized { values.toList } shouldBe List("timeout")
    deactivateCount.get shouldBe 1
  }
}
