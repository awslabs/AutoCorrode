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

  private val NamedProofStarters: Set[String] =
    Set("lemma", "theorem", "corollary", "proposition", "schematic_goal")

  def partitionNamedProofs(commands: IndexedSeq[ScopeCommand]): IndexedSeq[NamedProof] = {
    val result = Vector.newBuilder[NamedProof]
    var i = 0
    while (i < commands.length) {
      if (!NamedProofStarters.contains(commands(i).name)) {
        i += 1
      } else {
        var depth = 0
        var j = i + 1
        var endIndex = -1
        while (j < commands.length && endIndex < 0) {
          commands(j).name match {
            case "proof" =>
              depth += 1
            case "qed" =>
              if (depth <= 1) endIndex = j
              else depth -= 1
            case "by" | "done" | "sorry" | "oops" if depth == 0 =>
              endIndex = j
            case _ =>
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
