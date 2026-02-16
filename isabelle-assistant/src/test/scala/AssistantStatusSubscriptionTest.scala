/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import scala.collection.mutable.ListBuffer

class AssistantStatusSubscriptionTest extends AnyFunSuite with Matchers {

  private final class FakeOutlet[A] {
    private[this] val consumers = ListBuffer.empty[Session.Consumer[A]]
    var addCount: Int = 0
    var removeCount: Int = 0

    def add(c: Session.Consumer[A]): Unit = {
      addCount += 1
      if (!consumers.exists(_ eq c)) consumers += c
    }

    def remove(c: Session.Consumer[A]): Unit = {
      removeCount += 1
      val idx = consumers.indexWhere(_ eq c)
      if (idx >= 0) consumers.remove(idx)
    }

    def emit(a: A): Unit = consumers.foreach(_.consume_robust(a))
    def size: Int = consumers.size
  }

  test("start should be idempotent") {
    val outlet = new FakeOutlet[Int]
    val subscription =
      AssistantStatusSubscription.createForTest[Int](
        "assistant-status-test",
        _ => (),
        outlet.add,
        outlet.remove
      )

    subscription.start()
    subscription.start()

    outlet.addCount shouldBe 1
    outlet.size shouldBe 1
    subscription.isStarted shouldBe true
  }

  test("stop should be idempotent") {
    val outlet = new FakeOutlet[Int]
    val subscription =
      AssistantStatusSubscription.createForTest[Int](
        "assistant-status-test",
        _ => (),
        outlet.add,
        outlet.remove
      )

    subscription.start()
    subscription.stop()
    subscription.stop()

    outlet.removeCount shouldBe 1
    outlet.size shouldBe 0
    subscription.isStarted shouldBe false
  }

  test("restart should not duplicate callbacks") {
    val outlet = new FakeOutlet[Int]
    var callbackCount = 0
    val subscription =
      AssistantStatusSubscription.createForTest[Int](
        "assistant-status-test",
        _ => callbackCount += 1,
        outlet.add,
        outlet.remove
      )

    subscription.start()
    outlet.emit(1)
    callbackCount shouldBe 1

    subscription.stop()
    outlet.emit(2)
    callbackCount shouldBe 1

    subscription.start()
    outlet.emit(3)
    callbackCount shouldBe 2

    outlet.addCount shouldBe 2
    outlet.removeCount shouldBe 1
    outlet.size shouldBe 1
  }
}
