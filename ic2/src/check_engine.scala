/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      ic2/src/check_engine.scala

The IC2 check engine, in three cleanly separated steps:

  A) updateModel — make the in-prover document model match the filesystem for a
     target theory and its whole import closure: resolve dependencies, add new
     nodes, and MINIMALLY edit changed nodes (common prefix + common suffix, so a
     small change near EOF invalidates only the commands after it, not the whole
     file). This step marks NOTHING required — it only adapts the model to the
     files.

  B) evaluate — drive the prover to check "up to a point": mark ONLY the target
     theory `required` and wait until the target's import closure has consolidated
     (or an external `shouldStop` fires). The prover propagates `required` from the
     target to all its ancestors automatically (Pure/PIDE/document.ML `make_required`
     = `all_preds required_node`), so we never mark ancestors ourselves.

  C) stop — the inverse of B: un-require the targets AND reclaim any still-running
     in-flight execution (a fork left running by a cancelled / first-error / timed-
     out check). A PAUSE, not a teardown — node text stays in the model for the next
     incremental check.

This replaces the former ic2_use_theories.scala, which was a copy of
`Headless.Session.use_theories` that fused "update the model" with "evaluate" and
marked every loaded theory required. The separation here is deliberate: A and B are
independently callable, and B relies on prover-side `required` propagation rather
than flagging the closure.

Dependency resolution reuses Isabelle's own resolver, `Resources.dependencies`,
which reads theory headers from disk and returns the transitive graph. It excludes
theories already in the session heap image (Pure/Build/resources.scala:
`if (loaded_theory(name)) …`), so the resolved closure is only the local, not-yet-
built `.thy` files — always a small set, no load-size batching needed.

Everything here reads the document only via `session.get_state()` / snapshots and
mutates it only via `session.update` — no upstream `Headless.Resources.State`
bookkeeping (no old-text cache, no UUID-scoped `required` refcount). Checks are
serialized server-wide (`Check.slot`), so refcounting would be dead weight; the
current model text is read back from the snapshot (`SessionTools.nodeText`) whenever
a diff is needed. */

package isabelle.ic2

import isabelle._


object Check_Engine {

  /* ---- Result: settled per-node status, mirrors the old use_theories Result ---- */

  /** The outcome of an `evaluate` run: the document state/version it settled on,
    * plus the per-node `Node_Status` for the target's import closure. `ok` iff no
    * node failed; `snapshot(name)` gives a stable snapshot for reading messages. */
  final class Result private[Check_Engine] (
    val state: Document.State,
    val version: Document.Version,
    val nodes: List[(Document.Node.Name, Document_Status.Node_Status)]
  ) {
    def snapshot(name: Document.Node.Name): Document.Snapshot = {
      val snapshot = state.snapshot(name)
      assert(version.id == snapshot.version.id)
      snapshot
    }

    def ok: Boolean = nodes.iterator.forall({ case (_, st) => st.ok })
  }


  /* ---- Model: the closure synced by updateModel, consumed by evaluate ---- */

  /** The document model as adapted to the filesystem for a set of targets.
    *   - `closure`: the target theories plus all transitively imported local
    *     (non-heap) theories, in topological order. This is the node set `evaluate`
    *     waits on and `Result.nodes` reports — ancestors carry no `required` flag of
    *     their own, so consolidation must be checked across the whole closure.
    *   - `targets`: the theories the caller asked to check (a subset of `closure`);
    *     these are the ONLY nodes `evaluate` marks `required`.
    *   - `files`: auxiliary loaded files (e.g. `ML_file` sources) the closure needs. */
  final case class Model(
    closure: List[Document.Node.Name],
    targets: List[Document.Node.Name],
    files: List[Document.Node.Name]
  )


  /* ---- A) update the document model to match the filesystem ---- */

  /** Resolve `targets`' import closure and sync the model to the files on disk in a
    * single `session.update`. Marks nothing required (perspective is `required =
    * false` everywhere). Returns the resolved `Model`, or `Left(msg)` on a
    * dependency/header error.
    *
    * Per node: new nodes are inserted whole; existing nodes get a minimal
    * prefix/suffix edit vs. their current model text; unchanged nodes produce no
    * edit. Auxiliary loaded files are synced as blobs. */
  def updateModel(
    session: Headless.Session,
    resources: Headless.Resources,
    targets: List[Document.Node.Name],
    unicode_symbols: Boolean = false
  ): Either[String, Model] =
    try {
      val dependencies = {
        val import_names = targets.map(_ -> Position.none)
        resources.dependencies(import_names).check_errors
      }
      // Only local, not-yet-built theories: dependencies already drops heap
      // theories, but filter defensively so the closure never names a loaded one.
      val closure = dependencies.theories.filterNot(resources.loaded_theory)
      val files = dependencies.loaded_files

      val headers: Map[Document.Node.Name, Document.Node.Header] =
        dependencies.entries.map(e => e.name -> e.header).toMap

      val theory_edits: List[Document.Edit_Text] =
        closure.flatMap { name =>
          val header = headers.getOrElse(name, Document.Node.no_header)
          val fs_text = Symbol.output(unicode_symbols, File.read(name.path))
          val model_text = SessionTools.nodeText(session, name)
          val text_edits =
            if (model_text.isEmpty) Text.Edit.inserts(0, fs_text)
            else minimalReplace(model_text, fs_text)
          if (text_edits.isEmpty) Nil
          else List(
            name -> Document.Node.Deps(header),
            name -> Document.Node.Edits(text_edits),
            name -> notRequired)
        }

      // Auxiliary loaded files (e.g. ML_file sources): minimally edit each blob
      // node against its current model text, same as theories. `doc_blobs` carries
      // only the blobs that changed (so PIDE re-reads exactly those).
      val changed_blobs =
        files.flatMap { name =>
          val bytes = Bytes.read(name.path)
          val fs_text = bytes.text
          val model_text = SessionTools.nodeText(session, name)
          val text_edits =
            if (model_text.isEmpty) Text.Edit.inserts(0, fs_text)
            else minimalReplace(model_text, fs_text)
          if (text_edits.isEmpty) None
          else {
            val item = Document.Blobs.Item(bytes, fs_text, Symbol.Text_Chunk(fs_text), changed = true)
            Some((name, item, text_edits))
          }
        }
      val doc_blobs = Document.Blobs(changed_blobs.map { case (n, item, _) => n -> item }.toMap)
      val file_edits: List[Document.Edit_Text] =
        changed_blobs.flatMap { case (name, item, text_edits) =>
          List(name -> Document.Node.Blob(item), name -> Document.Node.Edits(text_edits))
        }

      if (theory_edits.nonEmpty || file_edits.nonEmpty)
        session.update(doc_blobs, theory_edits ::: file_edits)

      Right(Model(closure = closure, targets = targets, files = files))
    } catch {
      case ERROR(msg) => Left(msg)
      case exn: Throwable if !Exn.is_interrupt(exn) => Left(Exn.message(exn))
    }


  /* ---- B) evaluate: drive the prover and wait for completion ---- */

  /** A bounded, partial-check target: evaluate node `node` only up to and including
    * the command spanning `range` (the command that ends at line N). Used by
    * `check FILE --line N`. */
  final case class Bound(node: Document.Node.Name, range: Text.Range, command: Command)

  /** Drive the prover over `model`, and wait until it is done — or `shouldStop()`
    * returns true (caller-driven early exit: first-error stop or cancel).
    *
    * Two modes, selected by `bound`:
    *
    *  - FULL (`bound = None`): mark ONLY `model.targets` required and wait until every
    *    node in `model.closure` has consolidated. The prover propagates `required`
    *    from the targets to all ancestors (Pure/PIDE/document.ML `make_required`),
    *    so the whole closure is evaluated.
    *
    *  - BOUNDED (`bound = Some(b)`): set a bounded VISIBLE perspective on `b.node`
    *    covering `[0, b.range.stop)` — `required = false`. The prover schedules the
    *    prefix up to and including the visible-last command (`b.command`) and STOPS
    *    there (document.ML: `prev = visible_last node then NONE`), so nothing past
    *    the target line is ever scheduled — no overshoot. `make_required`
    *    additionally requires the visible node's ancestors, so the imports are fully
    *    evaluated and the prefix type-checks. Completion is the target command
    *    reaching `is_terminated` — the bounded prefix never "consolidates" (that
    *    needs theory end), so it is the natural signal (same one the previous
    *    watchdog used).
    *
    * `onStatus` is invoked (best-effort) on each document change with the current
    * per-node status for the whole closure, so the caller can drive progress and
    * first-error detection. It also fires once at the end with the settled status.
    * `poll_delay` bounds how long the wait blocks between re-checks even if no
    * `commands_changed` event arrives. */
  def evaluate(
    session: Headless.Session,
    model: Model,
    onStatus: List[(Document.Node.Name, Document_Status.Node_Status)] => Unit = _ => (),
    shouldStop: () => Boolean = () => false,
    bound: Option[Bound] = None,
    poll_delay: Time = Time.seconds(0.2)
  ): Result = {
    val closure = model.closure

    // Drive the prover: FULL requires the targets; BOUNDED makes the target node's
    // prefix visible (required=false) so eval stops at the visible-last command,
    // while make_required still fully evaluates that node's ancestors.
    val driveEdits: List[Document.Edit_Text] =
      bound match {
        case None => model.targets.map(_ -> required)
        case Some(b) =>
          List(b.node -> Document.Node.Perspective(
            false, Text.Perspective(List(Text.Range(0, b.range.stop))),
            Document.Node.Overlays.empty))
      }
    session.update(Document.Blobs.empty, driveEdits)

    val done = new java.util.concurrent.CountDownLatch(1)
    @volatile var result: Option[Result] = None
    val poll_lock = new Object

    def perNodeStatus(
      state: Document.State, version: Document.Version
    ): List[(Document.Node.Name, Document_Status.Node_Status)] = {
      val now = Date.now()
      closure.map(name => name -> Document_Status.Node_Status.make(now, state, version, name))
    }

    // A FULL-mode closure node counts as "done" on the same disjunction the
    // reference use_theories used: either its formal theory CONSOLIDATED marker has
    // arrived (Node_Status.consolidated), or it is quasi-consolidated (all commands
    // terminated — the marker can lag behind under editor_consolidate_delay), or its
    // last command reached the consolidated state. Using only the theory marker
    // would risk hanging while a fully-evaluated node waits for the marker.
    def nodeDone(
      state: Document.State, version: Document.Version,
      name: Document.Node.Name, st: Document_Status.Node_Status
    ): Boolean =
      st.consolidated || st.quasi_consolidated || state.node_consolidated(version, name)

    // BOUNDED mode: done when the target command has terminated. A bounded prefix
    // never consolidates (that needs theory end), so this — not nodeDone — is the
    // completion signal for a partial check.
    def boundReached(state: Document.State, version: Document.Version): Boolean =
      bound.exists(b => state.command_status(version, b.command).is_terminated)

    // Recompute status, publish it, and settle the result when the prover is done
    // (or the caller asked to stop). Idempotent once settled, and serialized: poll()
    // is driven both by the commands_changed consumer and the await loop below, so
    // the lock keeps their status computations from racing.
    def poll(): Unit = poll_lock.synchronized {
      if (result.isDefined) return
      val state = session.get_state()
      state.stable_tip_version match {
        case None =>
        case Some(version) =>
          val status = perNodeStatus(state, version)
          try onStatus(status) catch { case _: Throwable => }
          val complete =
            bound match {
              case None => status.forall { case (name, st) => nodeDone(state, version, name, st) }
              case Some(_) => boundReached(state, version)
            }
          if (shouldStop() || complete) {
            result = Some(new Result(state, version, status))
            done.countDown()
          }
      }
    }

    val consumer =
      isabelle.Session.Consumer[isabelle.Session.Commands_Changed](getClass.getName) {
        changed => if (changed.nodes.exists(closure.contains) || changed.assignment) poll()
      }

    session.commands_changed += consumer
    try {
      poll()   // in case it is already complete / already stopped
      while (result.isEmpty) {
        val _ = done.await(poll_delay.ms, java.util.concurrent.TimeUnit.MILLISECONDS)
        poll()
      }
    } finally {
      session.commands_changed -= consumer
    }
    result.get
  }


  /* ---- C) stop the check: un-require the targets and reclaim in-flight work ---- */

  /** Stop a check started by `evaluate` — the inverse of step B. Two things, as one
    * unit:
    *
    *  1. RECLAIM in-flight execution. Dropping `required` alone does NOT interrupt a
    *     tactic already running on a worker thread — the perspective flip is
    *     text-neutral, so PIDE keeps the fork alive. For each target with a running
    *     or forked command, a text-CHANGING tail remint (SessionTools.resetNodeTails)
    *     re-splits [frontier, EOF) so PIDE's version-assignment diff cancels the
    *     superseded execs AND their fork groups — the primitive that truly interrupts
    *     the ML tactic. That remint also flips those nodes to not-required.
    *  2. UN-REQUIRE the rest. Targets with nothing in flight only need their
    *     `required` flag cleared — a text-neutral perspective flip. This is a PAUSE,
    *     not a teardown: node text stays in the model, so the next check's
    *     `updateModel` reuses the unchanged prefix.
    *
    * Runs on every exit path of a check (normal completion, first-error, cancel,
    * timeout, exception). Best-effort; safe to call unconditionally — a fully
    * consolidated node has no running command, so it takes the cheap un-require path
    * (`cancelFrontier` returns None). Operates on `model.targets` only: ancestors
    * were never explicitly required, so they go dormant once no target pulls them in. */
  def stop(session: Headless.Session, model: Model): Unit =
    try {
      // Targets with something still executing: reclaim via a text-changing tail
      // edit (which also un-requires them). No-op on a settled node.
      val cuts = model.targets.flatMap(n => SessionTools.cancelFrontier(session, n).map(n -> _))
      val reclaimed = cuts.map(_._1).toSet
      // The remaining targets (nothing in flight) just need `required` cleared.
      val releaseEdits = model.targets.filterNot(reclaimed).map(_ -> notRequired)
      if (releaseEdits.nonEmpty) session.update(Document.Blobs.empty, releaseEdits)
      if (cuts.nonEmpty) SessionTools.resetNodeTails(session, cuts)
    } catch { case _: Throwable => /* best-effort */ }


  /* ---- helpers ---- */

  private val required: Document.Node.Perspective_Text.T =
    Document.Node.Perspective(true, Text.Perspective.empty, Document.Node.Overlays.empty)

  private val notRequired: Document.Node.Perspective_Text.T =
    Document.Node.Perspective(false, Text.Perspective.empty, Document.Node.Overlays.empty)

  /** A minimal edit turning `old_text` into `new_text`: replace only the range
    * between the common prefix and the common suffix. This preserves unchanged
    * command identities so PIDE re-splits (and re-executes) only the commands in
    * the changed range — unlike a whole-file `Text.Edit.replace(0, old, new)`,
    * which removes every prefix command before reparse can keep it. */
  private def minimalReplace(old_text: String, new_text: String): List[Text.Edit] = {
    if (old_text == new_text) Nil
    else {
      val old_len = old_text.length
      val new_len = new_text.length

      var start = 0
      while (start < old_len && start < new_len &&
             old_text.charAt(start) == new_text.charAt(start)) start += 1

      var old_stop = old_len
      var new_stop = new_len
      while (old_stop > start && new_stop > start &&
             old_text.charAt(old_stop - 1) == new_text.charAt(new_stop - 1)) {
        old_stop -= 1
        new_stop -= 1
      }

      Text.Edit.removes(start, old_text.substring(start, old_stop)) :::
        Text.Edit.inserts(start, new_text.substring(start, new_stop))
    }
  }
}
