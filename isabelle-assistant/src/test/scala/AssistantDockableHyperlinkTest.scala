/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Tests for the chat-panel hyperlink dispatcher. The listener's body is
  * extracted into `AssistantDockable.dispatchHyperlink` so it can be
  * exercised without a live JEditorPane. The allow-list must reject any
  * scheme other than `action:insert:` and `action:copy:`; the previous
  * implementation silently ignored unknown schemes with no diagnostic,
  * which would have made a later change to accept `http(s):` into an
  * injection surface. */
class AssistantDockableHyperlinkTest extends AnyFunSuite with Matchers {

  test("dispatchHyperlink routes action:insert: to the registry") {
    var fired = false
    val id = AssistantInsertRegistry.register(() => { fired = true })
    val accepted = AssistantDockable.dispatchHyperlink(s"action:insert:$id")
    accepted shouldBe true
    fired shouldBe true
  }

  test("dispatchHyperlink tolerates an unknown insert id (no NPE)") {
    val accepted =
      AssistantDockable.dispatchHyperlink("action:insert:does-not-exist")
    // Returns true because the scheme matched; body is a no-op when the
    // registry has no entry for the id.
    accepted shouldBe true
  }

  test("dispatchHyperlink accepts action:copy: for well-formed payloads") {
    // Succeeds in test environments where AWT is available; falls through
    // to the LinkageError branch on headless CI, also returning true. We
    // only assert that it is not rejected as an unsupported scheme.
    val accepted =
      AssistantDockable.dispatchHyperlink("action:copy:hello%20world")
    accepted shouldBe true
  }

  test("dispatchHyperlink refuses file: scheme") {
    AssistantDockable.dispatchHyperlink("file:///etc/passwd") shouldBe false
  }

  test("dispatchHyperlink refuses http(s): scheme") {
    AssistantDockable.dispatchHyperlink("http://example.com") shouldBe false
    AssistantDockable.dispatchHyperlink("https://example.com") shouldBe false
  }

  test("dispatchHyperlink refuses javascript: scheme") {
    AssistantDockable.dispatchHyperlink("javascript:alert(1)") shouldBe false
  }

  test("dispatchHyperlink refuses mailto: scheme") {
    AssistantDockable.dispatchHyperlink("mailto:a@b") shouldBe false
  }

  test("dispatchHyperlink refuses an arbitrary action:<unknown> subscheme") {
    AssistantDockable.dispatchHyperlink("action:evil:foo") shouldBe false
  }

  test("dispatchHyperlink returns false for null or empty descriptor") {
    AssistantDockable.dispatchHyperlink(null) shouldBe false
    AssistantDockable.dispatchHyperlink("") shouldBe false
  }
}
