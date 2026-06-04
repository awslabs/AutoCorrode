/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import IQScopeResolution.ScopeCommand

object IQScopeResolutionTest {
  private def requireThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  /**
   * Helper: build a command stream from a list of (keyword, source) pairs,
   * laying them out contiguously in offset space starting at 0. Returns
   * the stream plus the total content length, which the resolver uses for
   * bounds clamping and for the File scope.
   */
  private def stream(pairs: (String, String)*): (IndexedSeq[ScopeCommand], Int) = {
    var offset = 0
    val cmds = pairs.toIndexedSeq.map { case (kw, src) =>
      val c = ScopeCommand(kw, offset, src.length)
      offset += src.length
      c
    }
    (cmds, offset)
  }

  /**
   * Convenience: given the (kw, src) pairs and an anchor source string,
   * resolve the scope at exactly that command's range.
   */
  private def resolveAt(
      pairs: List[(String, String)],
      anchorSrc: String,
      scope: CheckContextScope
  ): (Int, Int, CheckContextScope) = {
    val (cmds, total) = stream(pairs *)
    val anchor = cmds.find(c => pairs(cmds.indexWhere(_ eq c))._2 == anchorSrc)
      .orElse {
        // Fallback: match by source via the layout
        var off = 0
        var found: Option[ScopeCommand] = None
        pairs.foreach { case (kw, src) =>
          if (found.isEmpty && src == anchorSrc) found = Some(ScopeCommand(kw, off, src.length))
          off += src.length
        }
        found
      }
      .getOrElse(sys.error(s"no command with src=$anchorSrc"))
    IQScopeResolution.resolveScope(cmds, total, anchor.offset, anchor.offset + anchor.length, scope)
  }

  /**
   * Resolve at the command at the given pairs-index. Use this when the
   * anchor source string is not unique in the stream (resolveAt picks
   * first match, which is order-dependent and brittle).
   */
  private def resolveAtIndex(
      pairs: List[(String, String)],
      anchorIdx: Int,
      scope: CheckContextScope
  ): (Int, Int, CheckContextScope) = {
    val (cmds, total) = stream(pairs *)
    val anchor = cmds(anchorIdx)
    IQScopeResolution.resolveScope(cmds, total, anchor.offset, anchor.offset + anchor.length, scope)
  }

  // ---------- Scenario 1: edit inside a proof…qed body ----------

  private def testInsideProofQed(): Unit = {
    // lemma A: ... proof - have h: ... by simp thus ?thesis . qed
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "proof" -> "proof -",
      "have"  -> "have h: \"P\"",
      "by"    -> "by simp",
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed"
    )
    val (s, e, r) = resolveAt(pairs, "have h: \"P\"", CheckContextScope.Block)
    requireThat(r == CheckContextScope.Block,
      s"edit at have inside proof…qed should resolve as Block, got $r")
    // The scope range should cover proof…qed fully.
    val (cmds, _) = stream(pairs *)
    val proofStart = cmds.find(_.name == "proof").get.offset
    val qedEnd = { val q = cmds.findLast(_.name == "qed").get; q.offset + q.length }
    requireThat(s <= proofStart && e >= qedEnd,
      s"Block scope should cover proof($proofStart)..qed($qedEnd), got [$s, $e)")
  }

  // ---------- Scenario 2: edit inside a `lemma … by …` (no proof block) ----------

  private def testInsideLemmaBy(): Unit = {
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "by"    -> "by simp"
    )
    // Edit at the `by` itself with Block.
    val (s, e, r) = resolveAt(pairs, "by simp", CheckContextScope.Block)
    requireThat(r == CheckContextScope.Proof,
      s"edit inside lemma…by should resolve to Proof (lemma block), got $r")
    val (cmds, _) = stream(pairs *)
    val lemmaStart = cmds.find(_.name == "lemma").get.offset
    val byEnd = { val b = cmds.find(_.name == "by").get; b.offset + b.length }
    requireThat(s == lemmaStart && e == byEnd,
      s"Proof scope should cover lemma..by, got [$s, $e)")
  }

  // ---------- Scenario 3: edit at lemma statement after a sibling proof…qed ----------

  private def testAfterSiblingProofQed(): Unit = {
    // lemma A: ... proof - by simp thus . qed   lemma B: ... by simp
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "proof" -> "proof -",
      "have"  -> "have h: \"P\"",
      "by"    -> "by simp",
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed",
      "lemma" -> "lemma B: \"Q\"",   // edit anchor
      "by"    -> "by simp"
    )
    val (s, e, r) = resolveAt(pairs, "lemma B: \"Q\"", CheckContextScope.Block)
    // Previously this latched onto the prior `proof` and degenerated to
    // command. Depth-aware walk-back must instead recognise the
    // closed-out sibling and resolve to lemma B's own block.
    requireThat(r == CheckContextScope.Proof,
      s"edit at lemma statement after sibling proof…qed should resolve to Proof, got $r")
    val (cmds, _) = stream(pairs *)
    val lemmaBStart = cmds.findLast(_.name == "lemma").get.offset
    requireThat(s == lemmaBStart,
      s"scope start should be lemma B (offset $lemmaBStart), got $s")
  }

  // ---------- Scenario 4: edit between two lemmas (top-level, no enclosing block) ----------

  private def testTopLevelBetweenLemmas(): Unit = {
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "by"    -> "by simp",
      ""      -> "(* between *)",   // pseudo top-level command
      "lemma" -> "lemma B: \"Q\"",
      "by"    -> "by simp"
    )
    val (s, e, r) = resolveAt(pairs, "(* between *)", CheckContextScope.Block)
    requireThat(r == CheckContextScope.Command,
      s"edit between lemmas at top level should degrade to Command, got $r")
    val (cmds, _) = stream(pairs *)
    val between = cmds.find(_.name == "").get
    requireThat(s == between.offset && e == between.offset + between.length,
      s"degraded scope range should equal the edit range")
  }

  // ---------- Scenario 5: depth-2 nested proof…qed ----------

  private def testDeepNested(): Unit = {
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "proof" -> "proof -",            // outer
      "have"  -> "have outer: \"P\"",
      "proof" -> "proof -",            // inner
      "have"  -> "have inner: \"P\"",  // edit anchor
      "by"    -> "by simp",
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed",                // closes inner
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed"                 // closes outer
    )
    val (s, e, r) = resolveAt(pairs, "have inner: \"P\"", CheckContextScope.Block)
    requireThat(r == CheckContextScope.Block,
      s"edit at depth 2 with Block should resolve to Block (innermost), got $r")
    val (cmds, _) = stream(pairs *)
    // The innermost proof is at index 3, the matching qed at index 8.
    val innerProofStart = cmds.zipWithIndex.collect { case (c, 3) => c.offset }.head
    val innerQedEnd = {
      val q = cmds.zipWithIndex.collect { case (c, 8) => c }.head
      q.offset + q.length
    }
    requireThat(s == innerProofStart && e == innerQedEnd,
      s"Block at depth 2 should cover the inner proof…qed, got [$s, $e)")
  }

  // ---------- Scenario 6: scope=command and scope=file pass-through ----------

  private def testPassThrough(): Unit = {
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "by"    -> "by simp"
    )
    val (cmds, total) = stream(pairs *)
    val anchor = cmds.head
    val (cs, ce, cr) =
      IQScopeResolution.resolveScope(cmds, total, anchor.offset, anchor.offset + anchor.length, CheckContextScope.Command)
    requireThat(cr == CheckContextScope.Command, "Command should pass through")
    requireThat(cs == anchor.offset && ce == anchor.offset + anchor.length,
      "Command should not widen the range")

    val (fs, fe, fr) =
      IQScopeResolution.resolveScope(cmds, total, anchor.offset, anchor.offset + anchor.length, CheckContextScope.File)
    requireThat(fr == CheckContextScope.File, "File should pass through")
    requireThat(fs == 0 && fe == total,
      "File should widen to the whole content")
  }

  // ---------- Scenario 7: empty command stream degrades cleanly ----------

  private def testEmptyStream(): Unit = {
    val (s, e, r) =
      IQScopeResolution.resolveScope(IndexedSeq.empty, 0, 0, 0, CheckContextScope.Block)
    requireThat(r == CheckContextScope.Command,
      "Empty command stream with Block must degrade to Command")
    requireThat(s == 0 && e == 0, "degraded range must equal edit range")
  }

  // ---------- Scenario 8: scope=Proof on edit inside a NON-nested proof ----------
  //
  // Contract: 'proof' resolves to the OUTERMOST enclosing proof…qed. In a
  // single-layer proof the innermost layer IS the outermost, so 'block' and
  // 'proof' coincide here and both cover the one proof…qed. The nested case
  // where they diverge (proof ⊋ block) is pinned by Scenarios 14-16.

  private def testProofScopeFromInsideBody(): Unit = {
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "proof" -> "proof -",
      "have"  -> "have h: \"P\"",   // edit anchor
      "by"    -> "by simp",
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed"
    )
    val (s, e, r) = resolveAt(pairs, "have h: \"P\"", CheckContextScope.Proof)
    requireThat(r == CheckContextScope.Proof,
      s"Proof scope from inside body should resolve to Proof, got $r")
    val (cmds, _) = stream(pairs *)
    val proofStart = cmds.find(_.name == "proof").get.offset
    val qedEnd = { val q = cmds.find(_.name == "qed").get; q.offset + q.length }
    requireThat(s == proofStart && e == qedEnd,
      s"Proof inside a non-nested proof body covers that proof..qed, got [$s, $e)")
  }

  // ---------- Scenario 9: edits across multiple sibling lemmas walk-back gracefully ----------

  private def testManySiblingBys(): Unit = {
    // Several `lemma … by …` sequences, then an edit at the next lemma stmt.
    val pairs = List(
      "lemma" -> "lemma A: \"P\"", "by" -> "by simp",
      "lemma" -> "lemma B: \"Q\"", "by" -> "by simp",
      "lemma" -> "lemma C: \"R\"", "by" -> "by simp",
      "lemma" -> "lemma D: \"S\""    // edit anchor
    )
    val (_, _, r) = resolveAt(pairs, "lemma D: \"S\"", CheckContextScope.Block)
    requireThat(r == CheckContextScope.Proof,
      s"edit at lemma D after many sibling bys should resolve to Proof, got $r")
  }

  // ---------- Scenario 10: anchor INSIDE a nested proof body, AFTER an inner `by` ----------
  //
  // Regression: previously findInnerProof treated a top-level 'by' as a
  // closer. Walking back from `thus ?thesis` through the inner `by simp`
  // would push the depth counter to 1, then the inner `proof` would
  // decrement back to 0 and fail to return — silently latching onto the
  // OUTER proof instead. scope_resolved still reported Block, so the
  // caller had no way to detect the silent widening.
  //
  // Fix: 'by' (like 'sorry'/'oops'/'done') is a goal closer, not a
  // 'proof' closer. Only 'qed' pairs with 'proof'.

  private def testInnerByDoesNotShadowEnclosingProof(): Unit = {
    val pairs = List(
      "lemma" -> "lemma N05: \"P\"",
      "proof" -> "proof -",            // OUTER proof   (idx 1)
      "have"  -> "have outer: \"P\"",
      "proof" -> "proof -",            // INNER proof   (idx 3)
      "have"  -> "have inner: \"P\"",
      "by"    -> "by simp",
      "thus"  -> "thus ?thesis",       // <-- edit anchor (idx 6, after inner `by`)
      "."     -> ".",
      "qed"   -> "qed",                // closes inner  (idx 8)
      "thus"  -> "thus ?thesis",       // (duplicate source — anchor by index, not source)
      "."     -> ".",
      "qed"   -> "qed"                 // closes outer
    )
    val anchorIdx = 6
    val innerProofIdx = 3
    val innerQedIdx = 8
    val (s, e, r) = resolveAtIndex(pairs, anchorIdx, CheckContextScope.Block)
    requireThat(r == CheckContextScope.Block,
      s"edit after inner `by` in nested proof should resolve as Block (innermost), got $r")
    val (cmds, _) = stream(pairs *)
    val innerProofStart = cmds(innerProofIdx).offset
    val innerQedEnd = cmds(innerQedIdx).offset + cmds(innerQedIdx).length
    requireThat(s == innerProofStart && e == innerQedEnd,
      s"resolver should latch onto the INNER proof…qed [$innerProofStart, $innerQedEnd), got [$s, $e)")
  }

  // ---------- Scenario 11: anchor inside a proof body, AFTER a sub-goal `sorry` ----------
  //
  // Regression: previously findInnerProof and the forward walk both
  // treated 'sorry' as a 'proof'-paired closer (because it was in the
  // StructuralEnders set, and the walks branched on that set). Walking
  // back from `thus ?thesis` through a sub-goal `sorry` would push depth
  // to 1; the enclosing 'proof' would decrement to 0 and not return —
  // silently latching one level out. The forward walk had a mirror flaw:
  // it would terminate at the inner 'sorry' rather than the matching
  // 'qed', producing a too-narrow block that failed the coverage guard
  // and degraded scope to Command.
  //
  // Fix: 'sorry' (like 'oops'/'done'/'by') is a goal closer, not a
  // 'proof' closer. Only 'qed' pairs with 'proof'.

  private def testInnerSorryDoesNotShadowEnclosingProof(): Unit = {
    val pairs = List(
      "lemma" -> "lemma S",
      "proof" -> "proof -",            // (idx 1)
      "have"  -> "have h: \"P\"",
      "sorry" -> "sorry",               // sub-goal admitted
      "thus"  -> "thus ?thesis",       // <-- edit anchor (idx 4)
      "."     -> ".",
      "qed"   -> "qed"                  // (idx 6)
    )
    val anchorIdx = 4
    val proofIdx = 1
    val qedIdx = 6
    val (s, e, r) = resolveAtIndex(pairs, anchorIdx, CheckContextScope.Block)
    requireThat(r == CheckContextScope.Block,
      s"edit after sub-goal sorry should resolve as Block, got $r")
    val (cmds, _) = stream(pairs *)
    val proofStart = cmds(proofIdx).offset
    val qedEnd = cmds(qedIdx).offset + cmds(qedIdx).length
    requireThat(s == proofStart && e == qedEnd,
      s"Block scope should cover proof…qed, got [$s, $e) expected [$proofStart, $qedEnd)")
  }

  // ---------- Scenario 12: anchor inside a proof body containing a sub-goal `done` ----------
  //
  // 'done' typically closes an apply-script's outer goal but can also
  // appear inside an Isar proof body to close a sub-goal whose proof
  // was given as an apply-script. Same conceptual issue as sorry.

  private def testInnerDoneDoesNotShadowEnclosingProof(): Unit = {
    val pairs = List(
      "lemma" -> "lemma D",
      "proof" -> "proof -",            // (idx 1)
      "have"  -> "have h: \"P\"",
      "apply" -> "apply x",
      "done"  -> "done",                // sub-goal closed by apply-script
      "thus"  -> "thus ?thesis",       // <-- edit anchor (idx 5)
      "."     -> ".",
      "qed"   -> "qed"                  // (idx 7)
    )
    val anchorIdx = 5
    val proofIdx = 1
    val qedIdx = 7
    val (s, e, r) = resolveAtIndex(pairs, anchorIdx, CheckContextScope.Block)
    requireThat(r == CheckContextScope.Block,
      s"edit after sub-goal done should resolve as Block, got $r")
    val (cmds, _) = stream(pairs *)
    val proofStart = cmds(proofIdx).offset
    val qedEnd = cmds(qedIdx).offset + cmds(qedIdx).length
    requireThat(s == proofStart && e == qedEnd,
      s"Block scope should cover proof…qed, got [$s, $e) expected [$proofStart, $qedEnd)")
  }

  // ---------- Scenario 13: lemma-style starter still terminates at 'sorry' ----------
  //
  // The conceptual fix says only 'qed' pairs with 'proof'. But for a
  // lemma-style starter (no enclosing 'proof' block), 'sorry' at depth 0
  // legitimately closes the lemma's outer goal and so terminates the
  // forward walk. This pins that the special-casing is on the STARTER
  // kind, not just on the keyword.

  private def testLemmaSorryAtDepthZeroTerminates(): Unit = {
    val pairs = List(
      "lemma" -> "lemma A",
      "sorry" -> "sorry"
    )
    val anchorIdx = 0
    val (s, e, r) = resolveAtIndex(pairs, anchorIdx, CheckContextScope.Block)
    requireThat(r == CheckContextScope.Proof,
      s"lemma A: sorry with Block should degrade to Proof (lemma block), got $r")
    val (cmds, _) = stream(pairs *)
    val expectedStart = cmds(0).offset
    val expectedEnd = cmds(1).offset + cmds(1).length
    requireThat(s == expectedStart && e == expectedEnd,
      s"Proof scope should cover lemma..sorry, got [$s, $e) expected [$expectedStart, $expectedEnd)")
  }

  // ===================================================================
  // Block-vs-Proof scope contract (Scenarios 14-16).
  //
  // The contract:
  //   - 'block' = the CURRENT (innermost) proof layer.
  //   - 'proof' = the ENTIRE proof of the enclosing lemma, i.e. the
  //               OUTERMOST enclosing proof…qed (the whole lemma proof).
  //
  // Inside a nested proof, 'proof' is strictly wider than 'block'; inside a
  // non-nested proof the two coincide. These pin that contract against
  // regression (it was previously collapsed: 'proof' resolved to the
  // innermost proof, the same as 'block').
  // ===================================================================

  // ---------- Scenario 14: nested proof, edit in inner body ----------
  //
  // 'block' must cover the INNER proof…qed; 'proof' must cover the OUTER
  // (entire) proof…qed. The two ranges must therefore DIFFER: proof ⊋ block.

  private def testProofWidensToOutermostNested(): Unit = {
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "proof" -> "proof -",            // OUTER  (idx 1)
      "have"  -> "have outer: \"P\"",
      "proof" -> "proof -",            // INNER  (idx 3)
      "have"  -> "have inner: \"P\"",  // <-- edit anchor (idx 4)
      "by"    -> "by simp",
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed",                // closes INNER (idx 8)
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed"                 // closes OUTER (idx 11)
    )
    val (cmds, _) = stream(pairs *)
    val outerProofStart = cmds(1).offset
    val outerQedEnd = cmds(11).offset + cmds(11).length
    val innerProofStart = cmds(3).offset
    val innerQedEnd = cmds(8).offset + cmds(8).length

    // 'block' = inner layer (this already holds today).
    val (bs, be, br) = resolveAtIndex(pairs, 4, CheckContextScope.Block)
    requireThat(br == CheckContextScope.Block, s"block should resolve to Block, got $br")
    requireThat(bs == innerProofStart && be == innerQedEnd,
      s"block should cover INNER proof…qed [$innerProofStart,$innerQedEnd), got [$bs,$be)")

    // 'proof' = entire (outer) proof.
    val (ps, pe, pr) = resolveAtIndex(pairs, 4, CheckContextScope.Proof)
    requireThat(pr == CheckContextScope.Proof,
      s"Scenario 14: proof scope should report Proof, got $pr")
    requireThat(ps == outerProofStart && pe == outerQedEnd,
      s"Scenario 14: 'proof' should widen to the ENTIRE (outer) proof…qed " +
      s"[$outerProofStart,$outerQedEnd) but got [$ps,$pe) " +
      s"(must not collapse onto the inner proof…qed [$innerProofStart,$innerQedEnd))")
    requireThat(ps < innerProofStart || pe > innerQedEnd,
      s"Scenario 14: 'proof' range must be strictly WIDER than 'block' range; " +
      s"got proof=[$ps,$pe) block=[$bs,$be)")
  }

  // ---------- Scenario 15: depth-3 nesting ----------
  //
  // 'block' = innermost layer; 'proof' = outermost layer, regardless of
  // how deep the edit sits.

  private def testProofWidensToOutermostDepth3(): Unit = {
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "proof" -> "proof -",             // L1 outer   (idx 1)
      "have"  -> "have h1: \"P\"",
      "proof" -> "proof -",             // L2         (idx 3)
      "have"  -> "have h2: \"P\"",
      "proof" -> "proof -",             // L3 inner   (idx 5)
      "have"  -> "have h3: \"P\"",      // <-- edit anchor (idx 6)
      "by"    -> "by simp",
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed",                 // closes L3   (idx 10)
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed",                 // closes L2   (idx 13)
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed"                  // closes L1   (idx 16)
    )
    val (cmds, _) = stream(pairs *)
    val outerStart = cmds(1).offset
    val outerEnd = cmds(16).offset + cmds(16).length
    val innerStart = cmds(5).offset
    val innerEnd = cmds(10).offset + cmds(10).length

    val (bs, be, _) = resolveAtIndex(pairs, 6, CheckContextScope.Block)
    requireThat(bs == innerStart && be == innerEnd,
      s"block at depth 3 should cover innermost proof…qed [$innerStart,$innerEnd), got [$bs,$be)")

    val (ps, pe, _) = resolveAtIndex(pairs, 6, CheckContextScope.Proof)
    requireThat(ps == outerStart && pe == outerEnd,
      s"Scenario 15: 'proof' at depth 3 should widen to the OUTERMOST proof…qed " +
      s"[$outerStart,$outerEnd), got [$ps,$pe)")
  }

  // ---------- Scenario 16: single-layer proof — block and proof coincide ----------
  //
  // With no nesting, the current and innermost layers ARE the outermost
  // layer, so block and proof legitimately produce the same range. This
  // pins that the intended fix does NOT over-widen in the common case.

  private def testProofEqualsBlockSingleLayer(): Unit = {
    val pairs = List(
      "lemma" -> "lemma A: \"P\"",
      "proof" -> "proof -",
      "have"  -> "have h: \"P\"",   // edit anchor (idx 2)
      "by"    -> "by simp",
      "thus"  -> "thus ?thesis",
      "."     -> ".",
      "qed"   -> "qed"
    )
    val (bs, be, _) = resolveAtIndex(pairs, 2, CheckContextScope.Block)
    val (ps, pe, pr) = resolveAtIndex(pairs, 2, CheckContextScope.Proof)
    requireThat(pr == CheckContextScope.Proof,
      s"Scenario 16: single-layer proof scope should report Proof, got $pr")
    requireThat(bs == ps && be == pe,
      s"Scenario 16: with no nesting, 'block' and 'proof' must coincide; " +
      s"got block=[$bs,$be) proof=[$ps,$pe)")
  }

  def main(args: Array[String]): Unit = {
    testInsideProofQed()
    testInsideLemmaBy()
    testAfterSiblingProofQed()
    testTopLevelBetweenLemmas()
    testDeepNested()
    testPassThrough()
    testEmptyStream()
    testProofScopeFromInsideBody()
    testManySiblingBys()
    testInnerByDoesNotShadowEnclosingProof()
    testInnerSorryDoesNotShadowEnclosingProof()
    testInnerDoneDoesNotShadowEnclosingProof()
    testLemmaSorryAtDepthZeroTerminates()

    // Block-vs-Proof scope contract.
    testProofWidensToOutermostNested()
    testProofWidensToOutermostDepth3()
    testProofEqualsBlockSingleLayer()

    println("IQScopeResolutionTest: all tests passed")
  }
}
