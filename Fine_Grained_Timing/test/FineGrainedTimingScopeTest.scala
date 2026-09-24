/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

object FineGrainedTimingScopeTest {
  private def requireThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  private def commands(names: String*): IndexedSeq[FineGrainedTimingScope.ScopeCommand] = {
    var offset = 0
    names.map { name =>
      val command = FineGrainedTimingScope.ScopeCommand(name, offset, name.length)
      offset += name.length + 1
      command
    }.toIndexedSeq
  }

  private def testNamedProofPartitioning(): Unit = {
    val proofs = FineGrainedTimingScope.partitionNamedProofs(commands(
      "text",
      "lemma", "by",
      "lemma", "proof", "have", "by", "show", "by", "qed",
      "text"
    ))
    requireThat(proofs.length == 2, s"expected two named proofs, got ${proofs.length}")
    requireThat(proofs.head.startIndex == 1 && proofs.head.endIndex == 2,
      s"one-line proof partition is incorrect: ${proofs.head}")
    requireThat(proofs(1).startIndex == 3 && proofs(1).endIndex == 9,
      s"structured proof partition is incorrect: ${proofs(1)}")
    requireThat(FineGrainedTimingScope.namedProofAt(proofs, 6).contains(proofs(1)),
      "inner proof command should belong to the named outer proof")
    requireThat(FineGrainedTimingScope.namedProofAt(proofs, 0).isEmpty,
      "top-level text should not belong to a named proof")
  }

  private def testIncompleteNamedProofIsExcluded(): Unit = {
    val proofs =
      FineGrainedTimingScope.partitionNamedProofs(commands("lemma", "proof", "show"))
    requireThat(proofs.isEmpty, "an incomplete named proof should not be partitioned")
  }

  def main(_args: Array[String]): Unit = {
    testNamedProofPartitioning()
    testIncompleteNamedProofIsExcluded()
    println("FineGrainedTimingScopeTest: all tests passed")
  }
}
