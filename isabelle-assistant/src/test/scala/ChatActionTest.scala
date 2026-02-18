/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ChatActionTest extends AnyFunSuite with Matchers {

  test("clearHistory should reset message count") {
    ChatAction.clearHistory()
    ChatAction.getHistorySnapshot.length shouldBe 0
  }

  test("addMessage should append to history") {
    ChatAction.clearHistory()
    ChatAction.addMessage("user", "test message")
    ChatAction.getHistorySnapshot.length shouldBe 1
    ChatAction.getHistorySnapshot.head.content shouldBe "test message"
  }

  test("history should respect max size limit") {
    ChatAction.clearHistory()
    val overLimit = AssistantConstants.MAX_ACCUMULATED_MESSAGES + 10
    for (i <- 1 to overLimit) {
      ChatAction.addMessage("user", s"message $i")
    }
    ChatAction.getHistorySnapshot.length should be <= AssistantConstants.MAX_ACCUMULATED_MESSAGES
  }

  test("transient messages should be filterable") {
    ChatAction.clearHistory()
    ChatAction.addMessage(ChatAction.Message(ChatAction.User, "regular", java.time.LocalDateTime.now()))
    ChatAction.addMessage(ChatAction.Message(ChatAction.Assistant, "transient", java.time.LocalDateTime.now(), transient = true))
    
    val all = ChatAction.getHistorySnapshot
    all.length shouldBe 2
    
    val nonTransient = all.filterNot(_.transient)
    nonTransient.length shouldBe 1
    nonTransient.head.content shouldBe "regular"
  }

  test("formatTime should produce HH:mm format") {
    val ts = java.time.LocalDateTime.of(2025, 1, 15, 14, 30)
    ChatAction.formatTime(ts) shouldBe "14:30"
  }

  test("commandNames should include all dispatch entries") {
    val names = ChatAction.commandNames
    names should contain("help")
    names should contain("suggest")
    names should contain("explain")
    names should contain("prove")
    names should contain("set")
    names should contain("models")
    names.length should be >= 25  // We have 30+ commands
  }

  test("getHistory and getHistorySnapshot should return same result") {
    ChatAction.clearHistory()
    ChatAction.addMessage("user", "test")
    ChatAction.getHistory shouldBe ChatAction.getHistorySnapshot
  }

  test("history should be thread-safe with concurrent adds") {
    ChatAction.clearHistory()
    val threads = (1 to 10).map { i =>
      new Thread(() => {
        for (j <- 1 to 10) {
          ChatAction.addMessage("user", s"thread-$i-msg-$j")
        }
      })
    }
    threads.foreach(_.start())
    threads.foreach(_.join())
    
    // Should have all 100 messages (within limit)
    val history = ChatAction.getHistorySnapshot
    history.length shouldBe 100
  }
}
