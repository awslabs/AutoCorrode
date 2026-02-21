/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/** Checks I/Q availability via MCP reachability probes, with periodic re-checking.
  *
  * I/Q (Isabelle/Q) provides proof verification, sledgehammer, find_theorems,
  * and other Isabelle query capabilities. When unavailable, Assistant runs in
  * LLM-only mode with reduced functionality.
  *
  * The availability status is cached but can be refreshed via `recheck()`.
  */
object IQAvailable {
  @volatile private var _cached: Option[Boolean] = None
  private val AvailabilityProbeTimeoutMs = 1000L

  private def check(): Boolean = {
    IQMcpClient
      .callTool("list_files", Map.empty, AvailabilityProbeTimeoutMs)
      .isRight
  }

  def isAvailable: Boolean = _cached match {
    case Some(v) => v
    case None =>
      val result = check()
      _cached = Some(result)
      result
  }

  /** Force a re-check of I/Q availability. Call after installing I/Q at runtime. */
  def recheck(): Boolean = {
    val result = check()
    val changed = _cached.exists(_ != result)
    _cached = Some(result)
    if (changed) {
      logStatus()
      AssistantDockable.refreshIQStatus()
    }
    result
  }

  def logStatus(): Unit = {
    if (isAvailable)
      Output.writeln("[Assistant] I/Q plugin detected - proof verification features enabled")
    else
      Output.writeln("[Assistant] I/Q MCP endpoint unavailable - running in LLM-only mode.")
  }
}
