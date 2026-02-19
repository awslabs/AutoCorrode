/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.View

/** Runs Quickcheck via I/Q and offers LLM explanation of counterexamples. */
object QuickcheckAction {
  def run(view: View): Unit =
    CounterexampleFinderAction.run(view, CounterexampleFinderAction.Quickcheck)
}
