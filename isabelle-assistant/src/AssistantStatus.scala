/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Sanitized status text used for UI event propagation. */
final case class AssistantStatus private (text: String)

object AssistantStatus {
  def fromText(raw: String): AssistantStatus = {
    val normalized = Option(raw).map(_.trim).getOrElse("")
    if (normalized.nonEmpty) AssistantStatus(normalized)
    else AssistantStatus(AssistantConstants.STATUS_READY)
  }
}
