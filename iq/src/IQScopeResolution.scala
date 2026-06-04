/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/**
 * Pure logic for resolving write_file's check_context_scope to an offset
 * range over a (post-edit) command stream. Kept free of PIDE / jEdit
 * dependencies so it can be unit-tested via the regular `make test`
 * runner without spinning up an Isabelle session.
 *
 * The wrapper in IQServer (resolveCheckContextWindow) translates a real
 * Document.Snapshot into the small ScopeCommand stubs this module
 * accepts and delegates the actual walk to resolveScope below.
 */
object IQScopeResolution {

  /** Minimal projection of a PIDE Command needed by the scope walk. */
  final case class ScopeCommand(name: String, offset: Int, length: Int)

  // Block-starting keywords. Mirror of IQServer's ProofBlockStarters,
  // duplicated here on purpose so this module stays free of any
  // dependency on the IQServer class.
  val Starters: Set[String] =
    Set("lemma", "theorem", "corollary", "proposition", "schematic_goal", "proof")

  // Goal-completing keywords. Useful as a set, but NOT all interchangeable
  // for proof-depth bookkeeping: only 'qed' pairs with 'proof'. The others
  // close the most recent goal (the lemma's outer goal in 'lemma … by/
  // sorry/oops/done', or a sub-goal inside an Isar body).
  val StructuralEnders: Set[String] =
    Set("qed", "done", "sorry", "oops")

  /**
   * Resolve a check-context scope to an offset range against the given
   * command stream and edit position. Returns
   *   (scopeStart, scopeEnd, resolvedScope)
   * where the offsets are in the post-edit content and resolvedScope
   * reflects any degradation:
   *
   * - Block: the innermost enclosing 'proof…qed' (the current proof layer).
   * - Proof: the OUTERMOST enclosing 'proof…qed' (the entire proof of the
   *   enclosing lemma). For an edit inside a non-nested proof, Block and
   *   Proof coincide; inside a nested proof, Proof is strictly wider.
   * - Block or Proof requested with no enclosing 'proof' at all (e.g. a
   *   bare 'lemma … by …', or a lemma statement before its proof block):
   *   resolves to the surrounding lemma/theorem block and reports Proof.
   * - Block or Proof requested but no enclosing block at all, or the
   *   block we pin to the edit-start doesn't cover editEnd: degrades
   *   to Command.
   * - Command and File pass through unchanged.
   */
  def resolveScope(
      commands: IndexedSeq[ScopeCommand],
      contentLength: Int,
      editStart: Int,
      editEnd: Int,
      scope: CheckContextScope
  ): (Int, Int, CheckContextScope) = {
    if (scope == CheckContextScope.Command) return (editStart, editEnd, scope)
    if (scope == CheckContextScope.File)    return (0, contentLength, scope)

    if (commands.isEmpty) return (editStart, editEnd, CheckContextScope.Command)

    // Anchor on the command containing the start of the edit; the forward
    // walk below extends the resolved block past editEnd whenever needed
    // (it stops only at a balanced structural ender), so the start anchor
    // alone is sufficient for the common cases. Edits that straddle a
    // structural boundary (one whose end falls outside the block we pin
    // to its start) hit the coverage guard further down and degrade to
    // scope=command.
    def indexAt(offset: Int): Int = {
      val clamped = math.max(0, math.min(offset, contentLength - 1))
      commands.indexWhere(c => clamped >= c.offset && clamped < c.offset + c.length)
    }
    val startIdx = indexAt(editStart)
    if (startIdx < 0) return (editStart, editEnd, CheckContextScope.Command)

    // Walk back from `from` to find an enclosing 'proof' that is open at
    // the edit position. Depth-aware: a 'qed' we cross while walking back
    // must already have been opened by a 'proof' further back, so
    // increment `depth` on 'qed' and decrement on 'proof'; a 'proof' is a
    // true ancestor only when depth == 0 when we reach it. This avoids
    // latching onto a previous sibling's already-closed 'proof…qed'.
    //
    // Pairing rule: 'proof' pairs ONLY with 'qed'. 'by', 'done', 'sorry'
    // and 'oops' are GOAL closers, not 'proof' closers — they terminate
    // the lemma's outer goal in a 'lemma … by/sorry/oops' shape, or close
    // a sub-goal (have/show) inside an Isar proof body. Counting them as
    // 'proof' closers here would wrongly cancel out the very enclosing
    // 'proof' we are looking for, e.g. for an edit anchored after an
    // inner 'by simp' or 'sorry' inside a proof body — see
    // testInnerByDoesNotShadowEnclosingProof and
    // testInnerSorryDoesNotShadowEnclosingProof.
    //
    // Sibling `lemma … by …` chains are handled by failure: this walk
    // returns -1 (no enclosing 'proof' found) and the caller falls back
    // to findOuterStarter, which gives the surrounding lemma block
    // reported as scope_resolved=Proof.
    def findInnerProof(from: Int): Int = {
      var i = from
      var depth = 0
      while (i >= 0) {
        val kw = commands(i).name
        if (kw == "qed") {
          depth += 1
        } else if (kw == "proof") {
          if (depth == 0) return i
          depth -= 1
        }
        i -= 1
      }
      -1
    }
    // Walk back to the OUTERMOST enclosing 'proof' that is open at the edit
    // position -- the start of the entire proof of the enclosing lemma.
    // Same depth-aware bookkeeping as findInnerProof ('qed' increments,
    // 'proof' at depth 0 is an ancestor, a balanced 'proof' decrements),
    // but instead of returning the first ancestor 'proof' we keep walking
    // and remember the last one seen at depth 0. Because ancestor 'proof's
    // nest, the last depth-0 'proof' encountered walking back is the
    // outermost. Closed sibling 'proof…qed' pairs balance out via the depth
    // counter and are correctly skipped. Returns -1 when the edit is not
    // inside any 'proof' (e.g. a bare `lemma … by …` or a lemma statement
    // before its proof block), in which case the caller falls back to the
    // surrounding lemma/theorem block.
    def findOutermostProof(from: Int): Int = {
      var i = from
      var depth = 0
      var result = -1
      while (i >= 0) {
        val kw = commands(i).name
        if (kw == "qed") {
          depth += 1
        } else if (kw == "proof") {
          if (depth == 0) result = i
          else depth -= 1
        }
        i -= 1
      }
      result
    }
    // Walk back to the closest enclosing ProofBlockStarter -- including
    // 'proof' itself. Used as the fallback for both 'block' and 'proof'
    // when the edit is not inside any 'proof' body: it yields the
    // surrounding lemma/theorem block.
    def findOuterStarter(from: Int): Int = {
      var i = from
      while (i >= 0) {
        if (Starters.contains(commands(i).name)) return i
        i -= 1
      }
      -1
    }

    // Starter selection by scope:
    //   - Block: the innermost enclosing 'proof' (the current proof layer).
    //   - Proof: the outermost enclosing 'proof' (the entire lemma proof).
    // Both fall back to the surrounding lemma/theorem starter when the edit
    // is not inside any 'proof' body.
    val starterIdx = {
      val proofIdx = scope match {
        case CheckContextScope.Block => findInnerProof(startIdx)
        case CheckContextScope.Proof => findOutermostProof(startIdx)
        case _ => -1
      }
      if (proofIdx >= 0) proofIdx else findOuterStarter(startIdx)
    }
    if (starterIdx < 0) return (editStart, editEnd, CheckContextScope.Command)

    // Walk forward to the matching block end. Two cases by starter kind:
    //
    // Starter == "proof": match its 'qed' by tracking nested 'proof's.
    // 'by/done/sorry/oops' inside the body close sub-goals (have/show),
    // not the proof block itself, so they're skipped at any depth.
    //
    // Starter == lemma/theorem/etc.: terminate at the lemma's outer
    // closer at depth 0. That can be 'by'/'done'/'sorry'/'oops' (no
    // proof block), or the matching 'qed' of an inner 'proof' block.
    // Inside a 'proof' body (depth >= 1), 'by/done/sorry/oops' close
    // sub-goals and are skipped; only the balancing 'qed' (which brings
    // depth back to 0) terminates the lemma.
    val starterIsProof = commands(starterIdx).name == "proof"
    var depth = 0
    var j = starterIdx
    var foundEnd = false
    while (j < commands.length && !foundEnd) {
      val kw = commands(j).name
      if (kw == "proof") {
        depth += 1
      } else if (kw == "qed") {
        if (depth <= 1) foundEnd = true
        else depth -= 1
      } else if (!starterIsProof && depth == 0
          && (kw == "by" || kw == "done" || kw == "sorry" || kw == "oops")) {
        foundEnd = true
      }
      j += 1
    }
    val endCmdIdx = if (foundEnd) j - 1 else commands.length - 1

    val blockStart = commands(starterIdx).offset
    val blockEnd = commands(endCmdIdx).offset + commands(endCmdIdx).length

    // If the resolved block doesn't actually cover the edit (degenerate
    // case), fall back to `command` semantics.
    if (blockStart > editStart || blockEnd < editEnd) {
      return (editStart, editEnd, CheckContextScope.Command)
    }

    // For 'block' with no enclosing 'proof', the walk above degraded to
    // the outer lemma/theorem block: report that as 'proof' so the
    // caller knows.
    val resolved =
      if (scope == CheckContextScope.Block && commands(starterIdx).name != "proof")
        CheckContextScope.Proof
      else scope
    (math.min(editStart, blockStart), math.max(editEnd, blockEnd), resolved)
  }
}
