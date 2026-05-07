/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ChatActionTest extends AnyFunSuite with Matchers {

  test("clearHistory should reset message count") {
    ChatAction.clearHistory()
    ChatAction.getHistory.length shouldBe 0
  }

  // After clearHistory(), AssistantDockable.clearChat re-invokes
  // displayConversation, which takes the history.isEmpty branch and
  // renders the welcome card. This test pins the invariant at the
  // data layer (history is actually empty after clear) so the UI path
  // can rely on it: seeing an empty `getHistory` means the renderer
  // will emit the welcome card, not a stale bubble.
  test("clearHistory leaves getHistory empty so the welcome card renders on next display") {
    ChatAction.addMessage(ChatAction.User, "first")
    ChatAction.addMessage(ChatAction.Assistant, "reply")
    ChatAction.getHistory.length shouldBe 2

    ChatAction.clearHistory()
    ChatAction.getHistory shouldBe Nil

    // ConversationRenderer.createWelcomeHtml is unconditionally emitted when
    // the displayConversation() path is reached with an empty history (see
    // AssistantDockable.scala:929). Spot-check the welcome contract here so
    // a breakage in that contract shows up as a test failure.
    val html = ConversationRenderer.createWelcomeHtml(() => "help-id")
    html should include("Isabelle Assistant")
  }

  test("addMessage should append to history") {
    ChatAction.clearHistory()
    ChatAction.addMessage(ChatAction.User, "test message")
    ChatAction.getHistory.length shouldBe 1
    ChatAction.getHistory.head.content shouldBe "test message"
  }

  test("history should respect max size limit") {
    ChatAction.clearHistory()
    val overLimit = AssistantConstants.MAX_ACCUMULATED_MESSAGES + 10
    for (i <- 1 to overLimit) {
      ChatAction.addMessage(ChatAction.User, s"message $i")
    }
    ChatAction.getHistory.length should be <= AssistantConstants.MAX_ACCUMULATED_MESSAGES
  }

  test("transient messages should be filterable") {
    ChatAction.clearHistory()
    ChatAction.addMessage(ChatAction.Message(ChatAction.User, "regular", java.time.LocalDateTime.now()))
    ChatAction.addMessage(ChatAction.Message(ChatAction.Assistant, "transient", java.time.LocalDateTime.now(), transient = true))
    
    val all = ChatAction.getHistory
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
    names should contain("set")
    names should contain("models")
    names.length should be >= 24
  }

  test("history should be thread-safe with concurrent adds") {
    ChatAction.clearHistory()
    val threads = (1 to 10).map { i =>
      new Thread(() => {
        for (j <- 1 to 10) {
          ChatAction.addMessage(ChatAction.User, s"thread-$i-msg-$j")
        }
      })
    }
    threads.foreach(_.start())
    threads.foreach(_.join())

    // Should have all 100 messages (within limit)
    val history = ChatAction.getHistory
    history.length shouldBe 100
  }

  test("clearHistory should also reset tool-permission session state") {
    // Seed a session allow for verify_proof (an AskAtFirstUse tool).
    // checkPermission should then return Allowed without prompting.
    ToolPermissions.clearSession()
    ToolPermissions.setSessionAllowedForTest("verify_proof")
    val beforeClear =
      ToolPermissions.checkPermission("verify_proof", Map.empty[String, ResponseParser.ToolValue])
    beforeClear shouldBe ToolPermissions.Allowed

    ChatAction.clearHistory()

    // With the session cleared, verify_proof should fall back to its
    // configured AskAtFirstUse level and need a prompt.
    val afterClear =
      ToolPermissions.checkPermission("verify_proof", Map.empty[String, ResponseParser.ToolValue])
    afterClear shouldBe a[ToolPermissions.NeedPrompt]
  }

  test("addMessage truncates oversize content with an explicit marker") {
    ChatAction.clearHistory()
    val limit = AssistantConstants.MAX_MESSAGE_SIZE_CHARS
    val oversize = "x" * (limit + 1000)
    ChatAction.addMessage(ChatAction.User, oversize)

    val history = ChatAction.getHistory
    history.length shouldBe 1
    val stored = history.head.content
    stored.length should be < oversize.length
    stored should include("— truncated 1000 characters —")
    stored should startWith("x")
    stored should endWith("x")
  }

  test("addMessage leaves messages at or below the cap untouched") {
    ChatAction.clearHistory()
    val content = "y" * 1024
    ChatAction.addMessage(ChatAction.Assistant, content)

    val history = ChatAction.getHistory
    history.length shouldBe 1
    history.head.content shouldBe content
  }

  test("addErrorResponse tags the message as Error and translates via ErrorHandler") {
    ChatAction.clearHistory()
    ChatAction.addErrorResponse("connection timed out", "verify")

    val history = ChatAction.getHistory
    history.length shouldBe 1
    history.head.kind shouldBe ChatAction.ResponseKind.Error
    // makeUserFriendly rewrites "timed out" to the actionable hint.
    history.head.content should include("Try again")
  }

  test("addSuccessResponse tags the message as Success and does not translate") {
    ChatAction.clearHistory()
    ChatAction.addSuccessResponse("Proof verified successfully (10ms).")

    val history = ChatAction.getHistory
    history.length shouldBe 1
    history.head.kind shouldBe ChatAction.ResponseKind.Success
    history.head.content shouldBe "Proof verified successfully (10ms)."
  }

  test("addInfoResponse tags the message as Info") {
    ChatAction.clearHistory()
    ChatAction.addInfoResponse("Isabelle Assistant 0.1")

    val history = ChatAction.getHistory
    history.length shouldBe 1
    history.head.kind shouldBe ChatAction.ResponseKind.Info
  }

  test("addSummarizationNotice tags the message as Summary and drops bracket-prefix") {
    ChatAction.clearHistory()
    ChatAction.addSummarizationNotice()

    val history = ChatAction.getHistory
    history.length shouldBe 1
    history.head.kind shouldBe ChatAction.ResponseKind.Summary
    history.head.transient shouldBe true
    history.head.content should not startWith "["
  }

  test("addResponse leaves the message at the default Normal kind") {
    ChatAction.clearHistory()
    ChatAction.addResponse("just a plain response")

    val history = ChatAction.getHistory
    history.length shouldBe 1
    history.head.kind shouldBe ChatAction.ResponseKind.Normal
  }

  test("commandNames should include :version") {
    ChatAction.commandNames should contain("version")
  }

  test("addMessage sanitises rawHtml widget content defense-in-depth") {
    // Any widget producer that forgets to escape user-derived text would
    // otherwise let a <script> or on*-handler through. The sanitiser is the
    // last line of defence between Widget-role HTML and the HTMLEditorKit.
    ChatAction.clearHistory()
    val evil =
      """<div>hello<script>alert('xss')</script><a onclick="bad()" href="javascript:x">c</a></div>"""
    ChatAction.addMessage(
      ChatAction.Message(
        ChatAction.Widget,
        evil,
        java.time.LocalDateTime.now(),
        rawHtml = true
      )
    )
    val stored = ChatAction.getHistory.head.content
    stored should not include "<script"
    stored should not include "onclick="
    stored should not include "javascript:"
    // The benign surrounding markup is preserved.
    stored should include("hello")
  }

  test("addMessage leaves non-rawHtml content untouched") {
    // The sanitiser must never run on plain markdown content — it would
    // silently corrupt text that contained literal "<script>" (e.g. a user
    // asking about XSS examples). Only rawHtml widgets go through it.
    ChatAction.clearHistory()
    val literal = "Example: <script>alert('x')</script> is dangerous"
    ChatAction.addMessage(ChatAction.User, literal)
    ChatAction.getHistory.head.content shouldBe literal
  }
}
