/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Explains counterexamples found by Nitpick or Quickcheck using LLM analysis.
  */
object ExplainCounterexampleAction {

  /** Chat command handler: prompt user to run nitpick/quickcheck first.
    * Goal-state lookup goes through I/Q MCP, so it must not run on the EDT.
    */
  def chatCommand(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    AssistantDockable.setStatus("Checking goal state…")
    val _ = Isabelle_Thread.fork(name = "assistant-explain-cex") {
      val goal = GoalExtractor.getGoalState(buffer, offset).getOrElse("")
      GUI_Thread.later {
        if (goal.isEmpty) {
          val nitpickId = AssistantDockable.registerAction(() =>
            CounterexampleFinderAction.run(view, CounterexampleFinderAction.Nitpick)
          )
          val qcId = AssistantDockable.registerAction(() =>
            CounterexampleFinderAction.run(view, CounterexampleFinderAction.Quickcheck)
          )
          ChatAction.addResponse(
            s"${AssistantConstants.UIText.NO_GOAL_AT_CURSOR} Run a counterexample finder first:\n\n{{ACTION:$nitpickId:Nitpick}} {{ACTION:$qcId:Quickcheck}}"
          )
        } else {
          ChatAction.addResponse(
            "Run `:quickcheck` or `:nitpick` first, then click the 'Explain counterexample' link in the result."
          )
        }
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      }
    }
  }
  def explain(view: View, goal: String, counterexample: String): Unit = {
    ActionHelper.runAndRespond(
      "explain-counterexample",
      "Explaining counterexample…"
    ) {
      val defContext = ContextFetcher.getContext(view)
      val subs = Map("goal" -> goal, "counterexample" -> counterexample) ++
        defContext.map("definitions" -> _)
      val prompt = PromptLoader.load("explain_counterexample.md", subs)
      BedrockClient.invokeInContext(prompt)
    }
  }
}
