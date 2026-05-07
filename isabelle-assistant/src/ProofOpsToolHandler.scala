/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import ToolArgs._

/** Tool handlers that drive I/Q proof-state explorations: verify_proof,
  * run_sledgehammer, run_nitpick, run_quickcheck, find_counterexample,
  * execute_step, trace_simplifier.
  *
  * Each wraps an `IQMcpClient.callExplore` with the appropriate query type and
  * timeout, branching on success/timeout/error to render the user-facing
  * string. Extraction from AssistantTools is structural only — no behavior
  * changes — and keeps verification semantics in one file so the MCP-only
  * layering gate can focus on a tighter scope.
  */
private[assistant] object ProofOpsToolHandler {

  /** Pull a user-readable failure line out of an unsuccessful explore result.
    * Tries error → message → raw results in that order; falls back to the
    * caller-supplied description when all three are blank. */
  private[assistant] def exploreFailureMessage(
      result: IQMcpClient.ExploreResult,
      fallback: String
  ): String =
    List(result.error.getOrElse(""), result.message, result.results)
      .map(_.trim)
      .find(_.nonEmpty)
      .getOrElse(fallback)

  def execVerifyProof(args: ResponseParser.ToolArgs): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      val timeout = AssistantOptions.getVerificationTimeout
      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.Proof,
          arguments = proof,
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"Error: $mcpErr",
          explore => {
            if (explore.success) "Proof verified"
            else if (explore.timedOut) "Error: verification timed out"
            else
              s"Error: ${exploreFailureMessage(explore, "proof verification failed")}"
          }
        )
    }
  }

  def execRunSledgehammer(): String = {
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      val timeout = AssistantOptions.getSledgehammerTimeout
      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.Sledgehammer,
          arguments = "",
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"Error: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty) text else "No proofs found."
            } else if (explore.timedOut) "Sledgehammer timed out."
            else s"Error: ${exploreFailureMessage(explore, "sledgehammer failed")}"
          }
        )
    }
  }

  def execRunNitpick(): String = {
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      val timeout = AssistantOptions.getNitpickTimeout
      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.Proof,
          arguments = "nitpick",
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"Error: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty) text else "Nitpick returned no output."
            } else if (explore.timedOut) "Nitpick timed out."
            else s"Error: ${exploreFailureMessage(explore, "nitpick failed")}"
          }
        )
    }
  }

  def execRunQuickcheck(): String = {
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      val timeout = AssistantOptions.getQuickcheckTimeout
      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.Proof,
          arguments = "quickcheck",
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"Error: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty) text else "Quickcheck returned no output."
            } else if (explore.timedOut) "Quickcheck timed out."
            else s"Error: ${exploreFailureMessage(explore, "quickcheck failed")}"
          }
        )
    }
  }

  def execFindCounterexample(args: ResponseParser.ToolArgs): String = {
    val method = safeStringArg(args, "method", 50).toLowerCase
    val effectiveMethod = if (method.isEmpty) "quickcheck" else method

    effectiveMethod match {
      case "nitpick"    => execRunNitpick()
      case "quickcheck" => execRunQuickcheck()
      case "both" =>
        val nitpickResult = execRunNitpick()
        if (nitpickResult.contains("Counterexample")) nitpickResult
        else execRunQuickcheck()
      case _ =>
        s"Error: invalid method '$method', must be 'nitpick', 'quickcheck', or 'both'"
    }
  }

  def execExecuteStep(args: ResponseParser.ToolArgs): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      val timeout = AssistantOptions.getVerificationTimeout
      val mcpStart = System.currentTimeMillis()
      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.Proof,
          arguments = proof,
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"Error: step execution failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.isEmpty)
                "Error: step execution completed without a result."
              else {
                val stepResult = IQIntegration.parseStepResult(
                  text,
                  System.currentTimeMillis() - mcpStart
                )
                val status =
                  if (stepResult.complete) "[COMPLETE]"
                  else
                    stepResult.numSubgoals match {
                      case Some(n) => s"[$n subgoals]"
                      case None    => "[subgoal count unknown]"
                    }
                s"$status\n${stepResult.stateText}"
              }
            } else if (explore.timedOut) "Error: step execution timed out."
            else
              s"Error: ${exploreFailureMessage(explore, "step execution failed")}"
          }
        )
    }
  }

  def execTraceSimplifier(args: ResponseParser.ToolArgs): String = {
    val method = safeStringArg(args, "method", 50)
    val effectiveMethod =
      if (method.isEmpty || method == "simp") "simp" else method
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      val timeout = AssistantOptions.getTraceTimeout
      val depth = AssistantOptions.getTraceDepth
      val queryTimeoutMs =
        timeout * 1000L + AssistantConstants.TIMEOUT_BUFFER_MS
      val queryArg = s"simp_trace $effectiveMethod $timeout $depth"
      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.Proof,
          arguments = queryArg,
          timeoutMs = queryTimeoutMs
        )
        .fold(
          mcpErr => s"Error: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty) text
              else "Error: simplifier trace completed without a result."
            } else if (explore.timedOut) "Simplifier trace timed out."
            else
              s"Error: ${exploreFailureMessage(explore, "simplifier trace failed")}"
          }
        )
    }
  }
}
