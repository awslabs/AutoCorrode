/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.View

/** Runs Nitpick model finder via I/Q and offers LLM explanation of
  * counterexamples.
  */
object NitpickAction {
  def run(view: View): Unit =
    CounterexampleFinderAction.run(view, CounterexampleFinderAction.Nitpick)
}
