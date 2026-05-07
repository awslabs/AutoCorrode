/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for the planning widgets in WidgetRenderer.
 *
 * These are pure HTML-string assertions — they don't need a live jEdit
 * view. The main guarantee we want to pin down is that the "selected
 * approach" marker lands on the row whose ID matches `selectedApproach`,
 * regardless of the row's position in the list.
 */
class PlanningWidgetTest extends AnyFunSuite with Matchers {

  private val dummyRegister: (() => Unit) => String = _ => "expand-id"

  test("planningInProgress should show the brainstorm phase label") {
    val html = WidgetRenderer.planningInProgress("prove X", "brainstorm")
    html should include("Phase 1")
    html should include("Brainstorming")
  }

  test("planningInProgress should show the elaborate phase label") {
    val html = WidgetRenderer.planningInProgress("prove X", "elaborate", List("A", "B", "C"))
    html should include("Phase 2")
    html should include("Elaborating")
    html should include("Approach 1: A")
    html should include("Approach 2: B")
    html should include("Approach 3: C")
  }

  test("planningInProgress should show the select phase label") {
    val html = WidgetRenderer.planningInProgress("prove X", "select", List("A", "B", "C"))
    html should include("Phase 3")
    html should include("Selecting")
  }

  test("planningInProgress should HTML-escape the problem text") {
    val html = WidgetRenderer.planningInProgress("<script>alert(1)</script>", "brainstorm")
    html should not include "<script>alert(1)</script>"
    html should include("&lt;script&gt;")
  }

  test("planningResult should mark the selected approach by ID, not position") {
    // The approaches have non-sequential IDs — this is the M6 regression
    // test. A positional comparison would land the tick marker on row 2
    // (ID 5) when we ask for approach 10; only an ID-based comparison
    // gets it right.
    //
    // We distinguish selected from non-selected rows by looking for the
    // ✓ marker next to each title. Non-selected rows render three &nbsp;
    // pads instead.
    val approaches = List((1, "Alpha"), (5, "Beta"), (10, "Gamma"))
    val html = WidgetRenderer.planningResult(
      problem = "demo",
      approaches = approaches,
      selectedApproach = 10,
      reasoning = "best one",
      plan = "step 1\nstep 2",
      registerAction = dummyRegister
    )

    // Find each approach row (by its trailing ". Title") and look backward
    // to the nearest preceding "<div" to decide whether that row was marked
    // with ✓ (selected) or &nbsp; (unselected).
    def isSelectedRow(title: String): Boolean = {
      val titleIdx = html.indexOf(s". $title")
      if (titleIdx < 0) return false
      val divStart = html.lastIndexOf("<div", titleIdx)
      if (divStart < 0) return false
      val rowSnippet = html.substring(divStart, titleIdx)
      rowSnippet.contains("✓")
    }

    isSelectedRow("Gamma") shouldBe true
    isSelectedRow("Alpha") shouldBe false
    isSelectedRow("Beta") shouldBe false
  }

  test("planningResult should not mark any approach row as selected when selectedApproach matches none") {
    val approaches = List((1, "Alpha"), (2, "Beta"))
    val html = WidgetRenderer.planningResult(
      problem = "demo",
      approaches = approaches,
      selectedApproach = 99, // not present
      reasoning = "fallback",
      plan = "plan",
      registerAction = dummyRegister
    )

    def isSelectedRow(title: String): Boolean = {
      val titleIdx = html.indexOf(s". $title")
      if (titleIdx < 0) return false
      val divStart = html.lastIndexOf("<div", titleIdx)
      if (divStart < 0) return false
      html.substring(divStart, titleIdx).contains("✓")
    }

    isSelectedRow("Alpha") shouldBe false
    isSelectedRow("Beta") shouldBe false
  }

  test("planningResult should render a short plan inline without an expand link") {
    val shortPlan = (1 to 5).map(i => s"step $i").mkString("\n")
    val html = WidgetRenderer.planningResult(
      problem = "demo",
      approaches = List((1, "Alpha")),
      selectedApproach = 1,
      reasoning = "only option",
      plan = shortPlan,
      registerAction = dummyRegister
    )
    html should not include "Show full plan"
  }

  test("planningResult should render a long plan with an expand link") {
    val longPlan = (1 to 50).map(i => s"step $i").mkString("\n")
    val html = WidgetRenderer.planningResult(
      problem = "demo",
      approaches = List((1, "Alpha")),
      selectedApproach = 1,
      reasoning = "only option",
      plan = longPlan,
      registerAction = dummyRegister
    )
    html should include("Show full plan")
    html should include("(50 lines)")
  }

  test("planningResult should HTML-escape the reasoning text") {
    val html = WidgetRenderer.planningResult(
      problem = "demo",
      approaches = List((1, "Alpha")),
      selectedApproach = 1,
      reasoning = "<img src=x onerror=alert(1)>",
      plan = "step",
      registerAction = dummyRegister
    )
    html should not include "<img src=x"
    html should include("&lt;img")
  }
}
