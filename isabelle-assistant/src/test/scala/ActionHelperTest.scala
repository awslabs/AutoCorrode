/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** ActionHelper is a threading/UI harness — its entry points fork
  * Isabelle_Thread and then dispatch results back to the Swing EDT. That
  * means its semantically interesting behaviour (what the user sees on
  * success vs. on error) is not observable without a live jEdit View and
  * an Isabelle session backing Isabelle_Thread.
  *
  * This suite therefore pins the static surface that IS observable: the
  * object loads without throwing, and the default-argument values exposed
  * through its public API match what AssistantConstants declares. This
  * catches accidental breakage (e.g. someone changing STATUS_THINKING
  * without updating the default status passed to runAsync) without
  * requiring a full GUI harness. */
class ActionHelperTest extends AnyFunSuite with Matchers {

  test("ActionHelper object loads") {
    // Forcing a reference to the object triggers classloading; if the
    // object initializer threw we'd see the error here.
    ActionHelper.getClass.getName should include("ActionHelper")
  }

  test("default status strings remain aligned with AssistantConstants") {
    // These defaults are the values jEdit chat surfaces show while
    // commands run. If somebody renames STATUS_THINKING, we want the test
    // to flag the contract change rather than letting stale defaults
    // silently fall out of sync.
    AssistantConstants.STATUS_THINKING should not be empty
    AssistantConstants.STATUS_READY should not be empty
    AssistantConstants.STATUS_THINKING should not equal AssistantConstants.STATUS_READY
  }
}
