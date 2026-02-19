/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Explains counterexamples found by Nitpick or Quickcheck using LLM analysis.
  */
object ExplainCounterexampleAction {

  /** Chat command handler: prompt user to run nitpick/quickcheck first. */
  def chatCommand(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val goal = GoalExtractor.getGoalState(buffer, offset).getOrElse("")
    if (goal.isEmpty) {
      val nitpickId = AssistantDockable.registerAction(() =>
        CounterexampleFinderAction.run(view, CounterexampleFinderAction.Nitpick)
      )
      val qcId = AssistantDockable.registerAction(() =>
        CounterexampleFinderAction.run(
          view,
          CounterexampleFinderAction.Quickcheck
        )
      )
      ChatAction.addResponse(
        s"No goal at cursor position. Run a counterexample finder first:\n\n{{ACTION:$nitpickId:Run Nitpick}} {{ACTION:$qcId:Run Quickcheck}}"
      )
    } else {
      ChatAction.addResponse(
        "Run `:quickcheck` or `:nitpick` first, then click the 'Explain counterexample' link in the result."
      )
    }
  }
  def explain(view: View, goal: String, counterexample: String): Unit = {
    ActionHelper.runAndRespond(
      "explain-counterexample",
      "Explaining counterexample..."
    ) {
      val defContext = ContextFetcher.getContext(view)
      val subs = Map("goal" -> goal, "counterexample" -> counterexample) ++
        defContext.map("definitions" -> _)
      val prompt = PromptLoader.load("explain_counterexample.md", subs)
      BedrockClient.invokeInContext(prompt)
    }
  }
}
