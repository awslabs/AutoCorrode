/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

object FineGrainedTimingScope {
  final case class ScopeCommand(name: String, offset: Int, length: Int)

  final case class NamedProof(
      startIndex: Int,
      endIndex: Int,
      startOffset: Int,
      endOffset: Int
  )

  /* Every command that opens a goal state, matching the `thy_goal*` keyword
     kinds the Python side keys on. `instance`, `interpretation`, `sublocale`
     and `termination` carry no name that `ProofNamePattern` can recover, so
     `proofName` falls back for them; they were previously attributed to no
     proof at all. */
  private val NamedProofStarters: Set[String] =
    Set(
      "lemma",
      "theorem",
      "corollary",
      "proposition",
      "schematic_goal",
      "instance",
      "interpretation",
      "global_interpretation",
      "sublocale",
      "subclass",
      "termination"
    )

  /* Blocks that a proof can nest, distinguished because they close
     differently: a structured `proof` block ends at `qed`, while a `subgoal`
     block ends at a terminator such as `by` or `done`. */
  private sealed trait ProofBlock
  private case object StructuredBlock extends ProofBlock
  private case object SubgoalBlock extends ProofBlock

  private val ProofTerminators: Set[String] =
    Set("by", "..", ".", "sorry", "\\<proof>", "done", "oops")

  private val ProofNamePattern =
    """(?s)^\s*(?:lemma|theorem|corollary|proposition|schematic_goal)\s+([A-Za-z0-9_'.]+)""".r

  def proofName(source: String, fallback: String): String =
    ProofNamePattern.findFirstMatchIn(source).map(_.group(1))
      .getOrElse(fallback)

  def partitionNamedProofs(commands: IndexedSeq[ScopeCommand]): IndexedSeq[NamedProof] = {
    val result = Vector.newBuilder[NamedProof]
    var i = 0
    while (i < commands.length) {
      if (!NamedProofStarters.contains(commands(i).name)) {
        i += 1
      } else {
        var blocks = List.empty[ProofBlock]
        var j = i + 1
        var endIndex = -1
        while (j < commands.length && endIndex < 0) {
          val name = commands(j).name
          if (name == "proof") blocks = StructuredBlock :: blocks
          else if (name == "subgoal") blocks = SubgoalBlock :: blocks
          else if (name == "qed") {
            blocks match {
              case Nil => endIndex = j
              case List(StructuredBlock) => endIndex = j
              case StructuredBlock :: SubgoalBlock :: rest => blocks = rest
              case StructuredBlock :: rest => blocks = rest
              case _ =>
            }
          } else if (name == "oops") {
            endIndex = j
          } else if (ProofTerminators.contains(name)) {
            blocks match {
              /* Closes the enclosing `subgoal`, not the proof. */
              case SubgoalBlock :: rest => blocks = rest
              /* Closes a step inside a structured proof; `qed` ends that. */
              case StructuredBlock :: _ =>
              case Nil => endIndex = j
            }
          }
          j += 1
        }
        if (endIndex >= 0) {
          val end = commands(endIndex)
          result += NamedProof(
            startIndex = i,
            endIndex = endIndex,
            startOffset = commands(i).offset,
            endOffset = end.offset + end.length
          )
          i = endIndex + 1
        } else {
          i += 1
        }
      }
    }
    result.result()
  }

  def namedProofAt(
      proofs: IndexedSeq[NamedProof],
      commandIndex: Int
  ): Option[NamedProof] =
    proofs.find(proof => commandIndex >= proof.startIndex && commandIndex <= proof.endIndex)
}
