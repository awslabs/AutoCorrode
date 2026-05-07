/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.View

import ToolArgs._

/** Handler for the `plan_approach` tool.
  *
  * Dispatches into [[BedrockClient.invokePlanningAgent]], which runs the
  * three-phase adaptive tree-of-thought pipeline (brainstorm → parallel
  * elaboration → select). The handler itself is thin — it sanitises tool
  * arguments, rejects obviously malformed input, and routes exceptions
  * thrown by the orchestrator into a user-friendly error string.
  *
  * Split out of AssistantTools so the LLM-facing argument contract lives
  * next to its test, rather than in the 1800-line tool registry. */
private[assistant] object PlanApproachToolHandler {

  /** Max length for the free-text `scope` hint: "proof", "refactor",
    * "multi-file", etc. Anything above this is almost certainly the LLM
    * restating the whole problem and gets truncated. */
  private val MAX_SCOPE_LENGTH = 200

  /** Max length for optional `context`. Planning is expensive, so we don't
    * want an unbounded prompt fragment, but the main agent may legitimately
    * want to pass in a goal statement, a stack trace, or a file excerpt. */
  private val MAX_CONTEXT_LENGTH = 4000

  def execPlanApproach(args: ResponseParser.ToolArgs, view: View): String = {
    val problem = safeStringArg(args, "problem", MAX_STRING_ARG_LENGTH)
    val scope   = safeStringArg(args, "scope", MAX_SCOPE_LENGTH)
    val context = safeStringArg(args, "context", MAX_CONTEXT_LENGTH)

    if (problem.isEmpty) "Error: problem description required"
    else
      try BedrockClient.invokePlanningAgent(problem, scope, context, view)
      catch {
        case ex: Exception =>
          s"Error: planning failed: ${ErrorHandler.makeUserFriendly(ex.getMessage, "planning")}"
      }
  }
}
