/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Smoke-level coverage for the `CounterexampleFinderAction` Config values
  * that `NitpickAction` and `QuickcheckAction` route through. The `run`
  * path itself dispatches into I/Q and can't be exercised without a live
  * backend, but the config objects are the contract — if someone flips
  * nitpick's `toolName` to `"quickcheck"` (or vice versa), every
  * `displayResult` branch mis-labels the output.
  */
class CounterexampleFinderActionTest extends AnyFunSuite with Matchers {

  test("Nitpick config has consistent toolName and displayName") {
    val cfg = CounterexampleFinderAction.Nitpick
    cfg.toolName shouldBe "nitpick"
    cfg.displayName shouldBe "Nitpick"
    cfg.queryArgs shouldBe List("nitpick")
  }

  test("Quickcheck config has consistent toolName and displayName") {
    val cfg = CounterexampleFinderAction.Quickcheck
    cfg.toolName shouldBe "quickcheck"
    cfg.displayName shouldBe "Quickcheck"
    cfg.queryArgs shouldBe List("quickcheck")
  }

  test("config timeout getters return positive millisecond values") {
    // The getters defer to AssistantOptions, but must not return zero or
    // negative values: a zero-ms timeout fires a spurious "query failed"
    // the moment the MCP call starts, independent of its real status.
    CounterexampleFinderAction.Nitpick.getTimeout()      should be > 0L
    CounterexampleFinderAction.Quickcheck.getTimeout()   should be > 0L
  }

  test("Nitpick and Quickcheck are distinct configs") {
    // Sanity guard against a copy-paste regression where both aliases
    // point at the same `Config` instance.
    CounterexampleFinderAction.Nitpick shouldNot equal (CounterexampleFinderAction.Quickcheck)
  }
}
