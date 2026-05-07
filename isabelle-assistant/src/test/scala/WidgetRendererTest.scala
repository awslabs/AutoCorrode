/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Tests for `WidgetRenderer` accessibility and layout invariants.
  * Primarily guards that decorative glyphs (`✓`, `✗`, `○`, `●`) are always
  * rendered through `HtmlUtil.accessibleGlyph`, so screen readers announce
  * the textual equivalent ("Done", "Pending", etc.) instead of Unicode
  * character names.
  */
class WidgetRendererTest extends AnyFunSuite with Matchers {

  test("taskList renders each status glyph with a screen-reader label") {
    TaskList.clear()
    val _ = TaskList.addTask("first task", "do the thing", "it is done")
    val _ = TaskList.addTask("second task", "also do", "also done")
    val _ = TaskList.markDone(1)

    val html = WidgetRenderer.taskList(highlightNext = true)

    // Every glyph span must carry aria-hidden, and the textual label must
    // sit next to it — otherwise we've regressed the accessibility
    // improvement for the task list.
    html should include("aria-hidden='true'")
    html should include("Done")
    // The remaining task is the "next" task and should be flagged as such.
    html should include("Next")

    TaskList.clear()
  }

  test("taskDetail wraps the status glyph with an accessible label") {
    TaskList.clear()
    val _ = TaskList.addTask("alpha", "alpha desc", "alpha crit")
    val task = TaskList.getTasks.head

    val html = WidgetRenderer.taskDetail(task)

    html should include("aria-hidden='true'")
    html should include("Pending")

    TaskList.clear()
  }

  test("taskStatus emits an accessible label for the 'done' glyph") {
    TaskList.clear()
    val _ = TaskList.addTask("beta", "beta desc", "beta crit")
    val _ = TaskList.markDone(1)

    val html = WidgetRenderer.taskStatus(1, "done", "ignored")

    html should include("aria-hidden='true'")
    html should include("Done")

    TaskList.clear()
  }

  test("askUser embeds a click hint for keyboard users") {
    val html = WidgetRenderer.askUser(
      question = "Pick one.",
      context = "",
      options = List("Alpha", "Beta"),
      onChoice = _ => ()
    )

    html should include("Click an option")
  }
}
