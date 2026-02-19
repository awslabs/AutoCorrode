/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.buffer.JEditBuffer
import scala.util.boundary, boundary.break

/** Extracts proof blocks (lemma..qed) from PIDE command structure and detects
  * apply-style proofs.
  */
object ProofExtractor {
  private val proofStarters = IsabelleKeywords.proofStarters
  private val proofEnders =
    IsabelleKeywords.proofClosers ++ IsabelleKeywords.proofMethods

  def getProofBlockAtOffset(
      buffer: JEditBuffer,
      offset: Int
  ): Option[String] = {
    try {
      Document_Model.get_model(buffer).flatMap { model =>
        val snapshot = Document_Model.snapshot(model)
        val node = snapshot.get_node(model.node_name)
        if (node.commands.isEmpty) None
        else {
          val commands = node.command_iterator().toList
          val cmdIndex = commands.indexWhere { case (cmd, cmdOffset) =>
            offset >= cmdOffset && offset < cmdOffset + cmd.source.length
          }
          if (cmdIndex < 0) None
          else {
            var startIdx = -1
            var endIdx = -1

            boundary {
              for (i <- cmdIndex to 0 by -1) {
                // Use PIDE span name — the parsed command keyword
                val kw = commands(i)._1.span.name
                if (proofStarters.contains(kw)) { startIdx = i; break() }
              }
            }

            boundary {
              for (i <- cmdIndex until commands.length) {
                val kw = commands(i)._1.span.name
                if (proofEnders.contains(kw)) { endIdx = i; break() }
              }
            }

            if (startIdx >= 0 && endIdx >= 0)
              Some(
                commands
                  .slice(startIdx, endIdx + 1)
                  .map(_._1.source)
                  .mkString("\n")
              )
            else None
          }
        }
      }
    } catch {
      case _: Exception => None
    }
  }

  def isApplyStyleProof(proofText: String): Boolean =
    proofText.linesIterator.exists(line =>
      CommandMatcher.startsWithKeyword(line, "apply")
    )
}
