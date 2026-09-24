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

  private def testQualifiedProofName(): Unit = {
    requireThat(
      FineGrainedTimingScope.proofName(
        "lemma foo.first [simp]: \"True\"",
        "lemma"
      ) == "foo.first",
      "qualified proof names should not be truncated"
    )
  }

  private def testSubgoalBlockDoesNotEndTheProof(): Unit = {
    val proofs = FineGrainedTimingScope.partitionNamedProofs(commands(
      "lemma", "apply", "subgoal", "by", "apply", "done",
      "text"
    ))
    requireThat(proofs.length == 1, s"expected one named proof, got ${proofs.length}")
    requireThat(proofs.head.startIndex == 0 && proofs.head.endIndex == 5,
      s"a subgoal block must not terminate the proof: ${proofs.head}")
    requireThat(FineGrainedTimingScope.namedProofAt(proofs, 4).contains(proofs.head),
      "a command after the subgoal block still belongs to the proof")
  }

  private def testNestedSubgoalInStructuredProof(): Unit = {
    val proofs = FineGrainedTimingScope.partitionNamedProofs(commands(
      "lemma", "proof", "subgoal", "by", "show", "by", "qed"
    ))
    requireThat(proofs.length == 1, s"expected one named proof, got ${proofs.length}")
    requireThat(proofs.head.endIndex == 6,
      s"structured proof with a subgoal must end at qed: ${proofs.head}")
  }

  private def testStructuredProofClosesItsSubgoalBlock(): Unit = {
    val proofs = FineGrainedTimingScope.partitionNamedProofs(commands(
      "lemma",
      "apply",
      "subgoal", "premises", "proof", "show", "by", "qed",
      "apply", "done",
      "lemma", "by"
    ))
    requireThat(proofs.length == 2,
      s"expected two named proofs, got ${proofs.length}")
    requireThat(proofs.head.startIndex == 0 && proofs.head.endIndex == 9,
      s"qed must close its structured proof and subgoal: ${proofs.head}")
    requireThat(proofs(1).startIndex == 10 && proofs(1).endIndex == 11,
      s"the following proof must remain separate: ${proofs(1)}")
  }

  private def testShortProofTerminators(): Unit = {
    for (terminator <- Seq("qed", "..", ".", "\\<proof>", "oops")) {
      val proofs = FineGrainedTimingScope.partitionNamedProofs(commands(
        "instance", terminator,
        "lemma", "by"
      ))
      requireThat(proofs.length == 2,
        s"$terminator should close an instance proof, got ${proofs.length}")
      requireThat(proofs.head.endIndex == 1,
        s"$terminator consumed the following proof: ${proofs.head}")
    }
  }

  private def testGoalStartersBeyondLemma(): Unit = {
    for (starter <- Seq(
      "instance",
      "interpretation",
      "global_interpretation",
      "sublocale",
      "subclass",
      "termination"
    )) {
      val proofs =
        FineGrainedTimingScope.partitionNamedProofs(commands(starter, "by"))
      requireThat(proofs.length == 1,
        s"$starter should open a named proof, got ${proofs.length}")
    }
  }

  def main(_args: Array[String]): Unit = {
    testNamedProofPartitioning()
    testIncompleteNamedProofIsExcluded()
    testQualifiedProofName()
    testSubgoalBlockDoesNotEndTheProof()
    testNestedSubgoalInStructuredProof()
    testStructuredProofClosesItsSubgoalBlock()
    testShortProofTerminators()
    testGoalStartersBeyondLemma()
    println("FineGrainedTimingScopeTest: all tests passed")
  }
}
