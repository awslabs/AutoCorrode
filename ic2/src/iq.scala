/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      ic2/src/iq.scala

AutoCorrode I/R support for the daemon.

At session start (unless `--no-iq`) the daemon brings up the full I/R stack
against its Headless.Session AND an MCP server in front of it, so an agent
or operator can drive interactive Isar proof development against the same session
that serves checks — no separate jEdit + I/Q instance needed.

Two layers:

  1. I/R bring-up — delegated to the session-generic `IRLauncher`
     (iq/src/IRClient.scala, shared into this component). IRLauncher works for
     any `isabelle.Session` — the live PIDE session in Isabelle/jEdit's I/Q
     plugin, or our headless Headless.Session — and performs the whole handshake:
     probe IR_Repl.status, ad-hoc-load the I/R ML into the prover if needed, send
     IR_Repl.start, spawn `ir/repl.py --daemon --expect-ml` against the in-prover
     ML_Repl, scrape repl.py's client-facing port/token, and connect an IRClient.

  2. MCP server — a generic `McpServer` (shared from iq/src/McpServer.scala) on a
     loopback ephemeral port with a fresh token, offering the I/R `repl_*` tools
     via the shared `IRTools` provider, exactly as Isabelle/jEdit's I/Q plugin
     does. ic2 supplies its own `IRConnection` (Ic2IRConnection): it wraps the
     IRLauncher-connected client + the daemon's session, and resolves source
     locations headlessly (complete against loaded session nodes, read text from
     disk) rather than against jEdit buffers.

`ic2 server status` advertises both the client-facing repl.py endpoint (raw I/R wire
protocol) and the MCP endpoint (port + token). The in-prover ML_Repl is never
advertised — clients go through the bridge. Bring-up is all-or-nothing and
best-effort: any failure disables I/R+MCP but never the checking server; the
repl.py child and the MCP server are owned by the daemon and torn down on
shutdown.

Locations: $AUTOCORRODE_BASE if set, else the AutoCorrode tree this component
lives inside ($ISABELLE_IC2_HOME/.. — ic2 sits at <AutoCorrode>/ic2, so the I/R
sources are at <AutoCorrode>/ir). repl.py and the I/R ML (ir.ML / tcp_handler.ML
/ ml_repl.ML) all live in that `ir/` directory.
*/

package isabelle.ic2

import isabelle._

import java.util.concurrent.atomic.AtomicReference
import scala.jdk.CollectionConverters._


/** Functionality shared by both check entry points — the wire `ic2 check` op
 *  (Daemon.Connection_Handler) and the `check` MCP tool (IQ.checkTool). Keeping
 *  these in one place means the two paths resolve files the same way, share the
 *  single in-flight slot that serializes checks and drives `ic2 server status`
 *  idle/busy, and log start/finish/abort boundaries in one format. The
 *  transport-specific parts (JSON event streaming vs MCP notifications, the
 *  Progress used) stay with each caller.
 *
 *  There is AT MOST ONE check in flight at a time, server-wide: the check engine
 *  is not safe to run concurrently on the one `Headless.Session` (the calls
 *  share a single document state + version history), so `submit` refuses a new
 *  check while one is running. The caller cancels the running check and
 *  resubmits the merged set of theories. Because checks never overlap, there is
 *  no registry, no job ids, and no per-check bookkeeping — just `slot`. */
object Check {

  /* Headless.Session is batch-oriented: a bare stop-flag flip leaves the ML kernel
   * running the tactic, and its liveness signals over-count forked proofs. ic2
   * needs live progress and a real stop, so it reaches below the public API in two
   * places (details in each docstring):
   *   (a) Timing_Tracker — reports which commands are genuinely executing.
   *   (b) Check_Engine.stop (step C) — reclaims a still-running forked proof via a
   *       text-changing tail remint (SessionTools.resetNodeTails).
   */

  /** Delegates to `SessionTools.resolveFileTargets`, the shared
    * file→(Node.Name, theory-string) resolver used by the check pipeline. */
  def resolveTargets(
    resources: Headless.Resources, files: List[String]
  ): Either[String, List[(Document.Node.Name, String)]] =
    SessionTools.resolveFileTargets(resources, files)


  /* Timing_Tracker — mechanism (a): which commands are executing RIGHT NOW.
   * Counts the raw `command_timing` stream (Pure/General/timing.ML, on the
   * public `session.command_timings` outlet) per exec id (running:+1, elapsed:-1,
   * drop at 0). That stream fires only at the toplevel transition and the forked
   * terminal `by`, never for print forks, so it is correct for forked proofs —
   * unlike Command_Status.is_running (counts every fork) or Command_Timings
   * (offset-keyed, so a forked `by` collides with its transition). Keyword/line/
   * preview come from the authoritative Command at render time. Session-global:
   * one tracker serves every check, filtered by node in `running`. */
  final class Timing_Tracker {
    private final case class Entry(count: Int, start: Date)
    private val live =
      scala.collection.concurrent.TrieMap.empty[Document_ID.Generic, Entry]

    /** Fold one raw command_timing message into the counter. */
    def note(ct: isabelle.Session.Command_Timing): Unit = {
      val id = ct.state_id
      val running = ct.props.contains(Markup.command_running)
      if (running)
        live.updateWith(id) {
          case Some(e) => Some(e.copy(count = e.count + 1))
          case None => Some(Entry(1, Date.now()))
        }
      else
        live.updateWith(id) {
          case Some(e) if e.count > 1 => Some(e.copy(count = e.count - 1))
          case _ => None   // count -> 0: command settled, drop it
        }
      ()
    }

    /** Currently-executing commands in `name`, each with elapsed since first
      * seen. Resolves every live exec id to its Command via the snapshot;
      * prunes ids that no longer resolve (superseded document versions). */
    def running(session: Session, name: Document.Node.Name): List[RunningCommand] = {
      if (live.isEmpty) Nil
      else {
        val snapshot = session.snapshot(node_name = name)
        val node = snapshot.get_node(name)
        val lineDoc =
          if (node == null) None
          else try Some(Line.Document(node.source)) catch { case _: Throwable => None }
        // Line of a command from its start offset in the node source (the
        // command_timing message carries only an id_only position, no line —
        // so we derive it from the resolved Command's own span).
        def lineOf(cmd: Command): Int =
          (for {
            nd <- Option(node)
            doc <- lineDoc
            start <- nd.command_start(cmd)
            p <- scala.util.Try(doc.position(start).line + 1).toOption
          } yield p).getOrElse(0)
        val now = Date.now()
        val out = scala.collection.mutable.ListBuffer.empty[RunningCommand]
        for ((id, entry) <- live) {
          snapshot.find_command(id) match {
            case Some((_, cmd)) if cmd.node_name == name =>
              out += RunningCommand(cmd.span.name, lineOf(cmd),
                math.max(0.0, (now - entry.start).seconds), previewOf(cmd.source))
            case Some(_) => // a live command, but in another node — skip
            case None => live.remove(id)   // dead exec id — prune the leak
          }
        }
        out.toList.sortBy(-_.elapsedSecs)
      }
    }
  }

  /** The session-global timing tracker, bound once at daemon session
    * bring-up (daemon.scala subscribes it to `session.command_timings`).
    * None until bound; `runningCommandsFor` falls back to Nil when unbound
    * (e.g. a host that never wired it up). */
  @volatile private var timingTracker: Option[Timing_Tracker] = None
  def bindTimingTracker(t: Timing_Tracker): Unit = { timingTracker = Some(t) }


  /* ------------------------------------------------------------------- *
   * Job: a single check (running the A/B check engine), held by `slot`.
   *
   * `submit` is non-blocking: it resolves targets, starts a worker running the
   * check engine (Check_Engine.updateModel then evaluate), parks the Job in
   * `slot`, and returns. It REFUSES if a job is already running (Left) — checks
   * never overlap. A Job outlives the connection/request that started it.
   *
   * Blocking is a CALLER-SIDE policy on top of submit: subscribe to the job's
   * events, await its terminal state, and (for the wire path) cancel the job if
   * the caller's own connection drops. The Job itself never knows or cares
   * whether anyone is watching.
   *
   * The Job carries a Job_Progress doing the session-generic work: track
   * per-theory Node_Status, FIRST-ERROR STOP (set the failed theory + stop(),
   * which Check_Engine.evaluate polls via shouldStop), and fan typed Events out
   * to subscribers. Each transport renders Events its own way (wire JSON events;
   * MCP notifications), so no transport detail lives here.
   * ------------------------------------------------------------------- */

  /** One command that has been running for a while, surfaced under its theory's
    * progress bar. `elapsedSecs` is the wall-clock elapsed since the daemon
    * first observed the command as busy; the client filters by its own
    * threshold before rendering. `preview` is a single-line trimmed excerpt of
    * the command source (empty when unavailable — e.g. a pro-forma theory node
    * whose "command" is the whole theory), so a user can tell two `by (…)`
    * proofs apart without hunting for the line. */
  final case class RunningCommand(
    keyword: String, line: Int, elapsedSecs: Double, preview: String = "")

  /** A node's live status as a plain map (the shape used in progress/status).
    * If any commands in the node are currently running, they are attached as a
    * `long_running` array (each: keyword/line/elapsed_s), so the client can
    * render them indented under this theory's progress bar. Empty commands ⇒
    * no field emitted. */
  def nodeStatusJson(
    name: Document.Node.Name,
    st: Document_Status.Node_Status,
    runningCommands: List[RunningCommand] = Nil,
    updateSeq: Long = 0L
  ): JSON.Object.T = {
    val base = JSON.Object(
      "theory" -> name.theory,
      // finished-based percentage (see SessionTools.progressPercentage):
      // credits commands once DONE, not when they start running.
      "percentage" -> SessionTools.progressPercentage(st),
      "unprocessed" -> st.unprocessed,
      "running" -> st.running,
      "finished" -> st.finished,
      "warned" -> st.warned,
      "failed" -> st.failed,
      // Monotonic "last updated" stamp (0 if unknown); the client sorts the
      // shown theories by this so the display tracks recent activity.
      "update_seq" -> updateSeq,
      "consolidated" -> st.consolidated)
    if (runningCommands.isEmpty) base
    else base ++ JSON.Object("long_running" -> runningCommands.map { rc =>
      val core = JSON.Object("keyword" -> rc.keyword, "line" -> rc.line,
        "elapsed_s" -> rc.elapsedSecs)
      if (rc.preview.isEmpty) core
      else core ++ JSON.Object("preview" -> rc.preview)
    })
  }

  /** Single-line trimmed excerpt of a command's source, capped so it fits
    * comfortably under a progress bar. Newlines and runs of whitespace collapse
    * to a single space; longer previews get an ellipsis. */
  private def previewOf(source: String, maxChars: Int = 80): String = {
    val flat = source.trim.replaceAll("\\s+", " ")
    if (flat.length <= maxChars) flat else flat.take(maxChars - 1).trim + "…"
  }

  /** Currently long-running commands in `name`, via the session's bound
    * `Timing_Tracker` (see it for why that stream is the right signal).
    * Returns Nil when no tracker is bound. Display thresholds are applied by
    * clients, so this reports every live command. */
  def runningCommandsFor(
    session: Session, name: Document.Node.Name
  ): List[RunningCommand] =
    try timingTracker.map(_.running(session, name)).getOrElse(Nil)
    catch { case _: Throwable => Nil }

  /** Typed events a Job fans out to subscribers, in lifecycle order:
    * Started once, Progress repeatedly (throttled), at most one Error (first
    * failure), and exactly one Finished. */
  sealed trait Event
  object Event {
    final case class Started(theories: List[String]) extends Event
    /** Per-theory node status plus, for each theory, the list of currently
      * running commands (with elapsed time), for indented rendering under bars. */
    final case class Progress(
      nodes: List[(Document.Node.Name, Document_Status.Node_Status)],
      runningCommands: Map[Document.Node.Name, List[RunningCommand]] = Map.empty,
      updateSeqs: Map[Document.Node.Name, Long] = Map.empty
    ) extends Event
    final case class Error(theory: String, file: Option[String], line: Option[Int], message: String) extends Event
    final case class Finished(ok: Boolean, reason: String) extends Event
  }

  /** Terminal classification of a check. */
  sealed trait Outcome { def ok: Boolean; def reason: String }
  object Outcome {
    case object Ok extends Outcome { val ok = true; val reason = "" }
    final case class Failed(reason: String) extends Outcome { val ok = false }
    case object Running extends Outcome { val ok = false; val reason = "running" }
  }

  /** Progress driver for a Job: fed by Check_Engine.evaluate's `onStatus`
    * callback (step B). Records per-theory status, performs first-error stop, and
    * fans Events to the job's subscribers. A background ticker re-emits Progress
    * events with fresh elapsed times so long-running-command payloads keep updating
    * even when the document itself is quiet (a spinning command triggers no
    * commands_changed events). Session-generic; carries no transport.
    *
    * `stopped` is the single "please stop" flag Check_Engine.evaluate polls via
    * `shouldStop`: it is set by first-error detection (`record_status`) and by
    * `Job.cancel` (via `stop()`). It replaces the old `Progress.stopped` that
    * use_theories used to poll. (Partial mode no longer stops via this flag — it
    * bounds the perspective and completes when the target command terminates.) */
  private final class Job_Progress(job: Job, session: Headless.Session) {
    @volatile private var _stopped: Boolean = false
    def stopped: Boolean = _stopped
    /** Request stop (first-error or cancel). Also halts the ticker. */
    def stop(): Unit = { ticker_stop = true; _stopped = true }

    private val per_theory =
      Synchronized(Map.empty[Document.Node.Name, Document_Status.Node_Status])
    // Per-node "last updated" stamp: a monotonic sequence bumped each time a
    // node's status actually changes, so the client can show the theories the
    // check most recently touched (where work is happening) rather than the
    // most-progressed ones. Not wall-clock — a sequence keeps it deterministic
    // and cheap, and only relative order matters to the display.
    private val update_seq =
      Synchronized(Map.empty[Document.Node.Name, Long])
    private val seq_counter = new java.util.concurrent.atomic.AtomicLong(0L)
    def updateSeqOf(name: Document.Node.Name): Long = update_seq.value.getOrElse(name, 0L)
    private val error_latch = Synchronized(false)
    private val last_emit = Synchronized[Option[Long]](None)
    private val emit_interval_ms: Long = 200
    private val tick_interval_ms: Long = 500
    @volatile private var ticker: Option[Thread] = None
    @volatile private var ticker_stop: Boolean = false

    def error_emitted: Boolean = error_latch.value
    private def claim_error(): Boolean = error_latch.change_result(e => (true, !e))
    def snapshot_status: Map[Document.Node.Name, Document_Status.Node_Status] = per_theory.value

    /** Idempotent; exits when `ticker_stop` or the first-error latch fires. */
    def start_ticker(): Unit = synchronized {
      if (ticker.isDefined) return
      val t = new Thread(new Runnable {
        def run(): Unit = {
          while (!ticker_stop && !error_emitted) {
            try {
              val cur = per_theory.value
              if (cur.nonEmpty) {
                val running = snapshotRunning(cur)
                if (running.nonEmpty)
                  job.fan(Event.Progress(cur.toList.sortBy(_._1.theory), running, update_seq.value))
              }
            } catch { case _: Throwable => }
            try Thread.sleep(tick_interval_ms) catch { case _: InterruptedException => return }
          }
        }
      }, "ic2-check-ticker")
      t.setDaemon(true)
      ticker = Some(t)
      t.start()
    }

    /** Stop the ticker WITHOUT setting the stop flag — used from the worker's
      * `finally` after Check_Engine.evaluate returns normally. */
    def stop_ticker(): Unit = ticker_stop = true

    private def snapshotRunning(
      status: Map[Document.Node.Name, Document_Status.Node_Status]
    ): Map[Document.Node.Name, List[RunningCommand]] =
      status.iterator
        .filter { case (_, st) => !st.consolidated }
        .flatMap { case (name, _) =>
          val rcs = runningCommandsFor(session, name)
          if (rcs.isEmpty) None else Some(name -> rcs)
        }.toMap

    /** Fold one status snapshot (per closure node) into the recorded state, fan a
      * throttled Progress event, and trigger first-error stop. This is the
      * `onStatus` callback Check_Engine.evaluate invokes on each document change;
      * it replaces the old `Progress.nodes_status` override. */
    def record_status(status: List[(Document.Node.Name, Document_Status.Node_Status)]): Unit = {
      if (stopped || error_emitted) return
      val updated = per_theory.change_result { cache =>
        var c = cache
        for ((name, st) <- status) {
          // Bump the node's update stamp only when its status actually changed,
          // so an unchanged node re-reported on a quiet tick keeps its place
          // rather than churning to the top of the last-updated list.
          if (!st.is_empty && !cache.get(name).contains(st)) {
            c = c + (name -> st)
            update_seq.change(_ + (name -> seq_counter.incrementAndGet()))
          }
        }
        (c, c)
      }
      updated.find { case (_, st) => st.failed > 0 } match {
        case Some((name, _)) =>
          if (claim_error()) {
            val state = session.get_state()
            val snap = if (state.stable_tip_version.isDefined) Some(state.snapshot(name)) else None
            emit_error_from(name, snap)
            stop()   // first-error stop: evaluate polls `stopped` via shouldStop
          }
        case None =>
          val now = System.currentTimeMillis()
          val emit = last_emit.change_result {
            case Some(t) if now - t < emit_interval_ms => (false, Some(t))
            case _ => (true, Some(now))
          }
          if (emit)
            job.fan(Event.Progress(updated.toList.sortBy(_._1.theory), snapshotRunning(updated), update_seq.value))
      }
    }

    /** Emit a final Progress snapshot (end-state percentages). No live commands
      * remain here (the run has settled), so `runningCommands` is empty. */
    def flush_final(): Unit = {
      val cur = per_theory.value
      if (cur.nonEmpty) job.fan(Event.Progress(cur.toList.sortBy(_._1.theory), Map.empty, update_seq.value))
    }

    /** Post-result fallback: result is failure but the live callback never saw
      * it (consolidation on the final tick). Emit the first error, once. */
    def emit_post_result_error(result: Check_Engine.Result): Unit =
      result.nodes.find { case (_, st) => st.failed > 0 } match {
        case Some((name, _)) => if (claim_error()) emit_error_from(name, Some(result.snapshot(name)))
        case None =>
      }

    private def emit_error_from(name: Document.Node.Name, snapshot: Option[Document.Snapshot]): Unit = {
      snapshot.flatMap(_.messages.find { case (tree, _) => Protocol.is_error(tree) }) match {
        case Some((tree, pos)) =>
          job.fan(Event.Error(name.theory,
            Position.File.unapply(pos).orElse(Some(name.path.expand.implode)),
            Position.Line.unapply(pos),
            XML.content(Pretty.formatted(List(tree)))))
        case None =>
          job.fan(Event.Error(name.theory, None, None, "(failed but no error message available)"))
      }
    }
  }

  /** What granularity a Job targets. Full-theory checks evaluate the whole target
    * (the common case). A partial check limits evaluation to a prefix of ONE
    * theory ending at a resolved command — it runs the same A/B engine and stops
    * `evaluate` once the command at `line` has been processed.
    *
    * Both modes reuse the same event fan-out, cancel-running-execs +
    * cancel-pulse, subscribe API, and status JSON — they differ ONLY in the
    * worker body. The UI (wire events, MCP progress notifications, ANSI/plain
    * bars) is identical: from the client's point of view a partial check is a
    * fast full check on a single-theory job. */
  sealed trait Mode
  object Mode {
    case object Full extends Mode
    /** Partial-check target: the node under test and the 1-based caret line.
      * partial_body runs the A/B engine on the job's target node and stops it
      * once the command at `line` has been processed. */
    final case class Partial(target: Document.Node.Name, line: Int) extends Mode
  }

  /** A check job: a worker thread running the A/B check engine (Full mode, or Partial
    * mode which stops it at the target line), held in `slot`.
    * Subscribers receive Events live; the recorded status/outcome stays
    * available after completion for late status queries (until replaced). */
  final class Job private[Check] (
    val theories: List[String],
    val nodeNames: List[Document.Node.Name],
    session: Headless.Session,
    val mode: Mode = Mode.Full,
    resources: Option[Headless.Resources] = None
  ) {
    @volatile private var state: Outcome = Outcome.Running
    @volatile private var startMs: Long = 0L
    @volatile private var endMs: Long = 0L
    // When the check is cancelled, why — so the terminal interrupt is reported
    // as that reason (e.g. "timeout", "cancelled", "disconnect") rather than a
    // generic "interrupted". Set before cancel(); read on the interrupt path.
    @volatile private var cancelReason: Option[String] = None
    // The settled per-theory status from the engine result — the reliable
    // terminal state (the last live status callback lags consolidation),
    // used for the final progress snapshot. Empty until the worker returns.
    @volatile private var finalStatus: List[(Document.Node.Name, Document_Status.Node_Status)] = Nil
    private val latch = new java.util.concurrent.CountDownLatch(1)
    private val subscribers = new java.util.concurrent.CopyOnWriteArrayList[Event => Unit]()
    private val progress = new Job_Progress(this, session)
    @volatile private var worker: Thread = null

    /** Deliver an event to every current subscriber (best-effort per sink). */
    private[Check] def fan(e: Event): Unit =
      subscribers.forEach(s => try s(e) catch { case _: Throwable => })

    /** Subscribe to live events. Returns an unsubscribe thunk. Late subscribers
      * (job already finished) still get nothing replayed here — callers use
      * `statusJson` to read the recorded state, then subscribe for the tail. */
    def subscribe(sink: Event => Unit): () => Unit = {
      subscribers.add(sink); () => { val _ = subscribers.remove(sink) }
    }

    def outcome: Outcome = state
    def isRunning: Boolean = state == Outcome.Running
    /** Cancel the check. `progress.stop()` flips the stop flag, so
      * Check_Engine.evaluate stops waiting (`shouldStop` returns true) and returns.
      * The actual teardown — un-require the targets AND reclaim any still-running
      * fork via a text-changing tail remint — is step C (Check_Engine.stop), run in
      * runEngine's `finally`; the flip here does not itself interrupt a running ML
      * tactic. */
    def cancel(reason: String = "cancelled"): Unit = {
      if (cancelReason.isEmpty) cancelReason = Some(reason)
      progress.stop()
    }

    def await(): Outcome = { latch.await(); state }
    /** Bounded await; returns true if it reached a terminal state in time. */
    def await(ms: Long): Boolean = latch.await(ms, java.util.concurrent.TimeUnit.MILLISECONDS)

    private[Check] def start(): Unit = {
      startMs = System.currentTimeMillis()
      fan(Event.Started(theories))
      progress.start_ticker()
      val body: Runnable = mode match {
        case Mode.Full => full_body()
        case p: Mode.Partial => partial_body(p)
      }
      val t = new Thread(body, "ic2-check")
      t.setDaemon(true)
      worker = t
      t.start()
    }

    private def theResources: Headless.Resources =
      resources.getOrElse(error("check job missing Headless.Resources"))

    /** Run step A (updateModel) then step B (evaluate), classify the outcome, and
      * run step C (stop) on every exit path. `shouldStop` is the first-error/cancel
      * flag the progress driver and `cancel()` share (`progress.stopped`).
      *
      * `resolveBound` selects the drive mode. FULL mode returns None (require the
      * targets, wait for consolidation). PARTIAL mode returns Some(Bound): after
      * updateModel has parsed the node, it resolves `line N` to the target command
      * so evaluate can drive a BOUNDED visible perspective to it. It may throw
      * (ERROR) if the line can't be resolved (theory too short / parse error), which
      * classifies as a failed check.
      *
      * Check_Engine.stop is the whole teardown: it un-requires / un-shows the
      * targets AND reclaims any still-running fork (a text-changing tail remint), so
      * a cancelled / first-error / timed-out check leaves nothing executing and the
      * next check of this theory resumes cleanly instead of hanging on a tail. */
    private def runEngine(
      resolveBound: Check_Engine.Model => Option[Check_Engine.Bound] = _ => None
    ): Exn.Result[Check_Engine.Result] =
      Check_Engine.updateModel(session, theResources, nodeNames) match {
        case Left(msg) => Exn.Exn(ERROR(msg))
        case Right(model) =>
          try Exn.Res(
            Check_Engine.evaluate(session, model,
              onStatus = progress.record_status,
              shouldStop = () => progress.stopped,
              bound = resolveBound(model)))
          catch { case e: Throwable => Exn.Exn(e) }
          finally Check_Engine.stop(session, model)
      }

    /** The Full-mode worker: run the A/B engine and classify the outcome from its
      * result + the observed cancel/first-error flags. */
    private def full_body(): Runnable = new Runnable {
      def run(): Unit = {
        val result =
          try runEngine()   // runs step C (Check_Engine.stop) in its own finally
          finally {
            progress.stop_ticker()   // does NOT set the stop flag
            progress.flush_final()
          }
        // Record the settled per-theory status from the result for finalNodes
        // (reliable even when the last live callback lagged consolidation).
        result match {
          case Exn.Res(r) => finalStatus = r.nodes.sortBy(_._1.theory)
          case _ =>
        }
        val out =
          result match {
            case Exn.Res(r) =>
              // A caller-driven cancel (timeout/disconnect/explicit) that left no
              // failed node surfaces as that reason. A failed node — whether via
              // a live first-error stop or found in the settled result — is
              // "errors". (evaluate always returns a Result now, even on a
              // first-error stop, so we classify from the authoritative result.)
              if (!r.ok) { progress.emit_post_result_error(r); Outcome.Failed("errors") }
              else if (progress.error_emitted) Outcome.Failed("errors")
              else if (cancelReason.isDefined) Outcome.Failed(cancelReason.get)
              else Outcome.Ok
            // An interrupt the CALLER caused (timeout/disconnect/explicit
            // cancel) surfaces as that reason. But a real error must never be
            // masked as a bare interrupt: if the run actually saw a failed
            // node, classify it as the error — errors win over a no-reason
            // interrupt. Only a truly reasonless interrupt is "interrupted".
            case Exn.Exn(exn) if Exn.is_interrupt(exn) =>
              if (cancelReason.isDefined) Outcome.Failed(cancelReason.get)
              else if (progress.error_emitted) Outcome.Failed("errors")
              else Outcome.Failed("interrupted")
            case Exn.Exn(ERROR(msg)) => Outcome.Failed(msg)
            case Exn.Exn(e) => Outcome.Failed("exception: " + e.getMessage)
          }
        settle(out)
      }
    }

    /** The Partial-mode worker for `check FILE --line N`.
      *
      * Runs the same A/B/C engine as a full check, but step B drives a BOUNDED
      * visible perspective instead of requiring the target: `updateModel([target])`
      * parses and syncs the target's whole dependency closure, `resolveTargetBound`
      * resolves `line N` to the target command, and `evaluate(bound = ...)` makes
      * the target node visible up to that command. The prover then:
      *
      *  - evaluates the target's ancestors fully (make_required requires the
      *    predecessors of any visible node), so the prefix type-checks; and
      *  - schedules the target node ONLY up to the visible-last command and stops
      *    there — so commands past the line are NEVER scheduled. No overshoot, no
      *    watchdog, no line-reached cancel.
      *
      * Completion is the target command reaching `is_terminated` (a bounded prefix
      * never consolidates). Step C (Check_Engine.stop) still un-shows the target and
      * reclaims anything left running (e.g. an ancestor fork, or the target command
      * itself if the check was cancelled mid-flight). */
    private def partial_body(p: Mode.Partial): Runnable = new Runnable {
      def run(): Unit = {
        val out =
          try classify_partial(runEngine(resolveBound = m => Some(resolveTargetBound(p, m))))
          catch {
            case exn: Throwable if Exn.is_interrupt(exn) =>
              if (cancelReason.isDefined) Outcome.Failed(cancelReason.get)
              else Outcome.Failed("interrupted")
            case ERROR(msg) => Outcome.Failed(msg)
            case e: Throwable => Outcome.Failed("exception: " + e.getMessage)
          }
          finally {
            progress.stop_ticker()
            progress.flush_final()
          }
        settle(out)
      }
    }

    /** Resolve `line N` to the bounded target command for a partial check. Called
      * after updateModel, whose text edit triggers the (async) change-parser, so we
      * poll (bounded, 30s) until the target node's commands appear, then resolve
      * `line N` to a command (jEdit walk-back, same as `query state-at --line N`).
      * The returned Bound makes evaluate drive a visible perspective to `[0, end)`.
      * Throws ERROR if the line can't be resolved (theory too short / parse error)
      * or the check is cancelled while waiting — both classify as a failed check. */
    private def resolveTargetBound(p: Mode.Partial, model: Check_Engine.Model): Check_Engine.Bound = {
      val deadline = System.currentTimeMillis() + 30000
      var result: Option[Check_Engine.Bound] = None
      while (result.isEmpty && System.currentTimeMillis() < deadline && !progress.stopped && isRunning) {
        SessionTools.commandsUpToLine(session, p.target, p.line) match {
          case Right((_, cmd, endOffset)) =>
            result = Some(Check_Engine.Bound(p.target, Text.Range(0, endOffset), cmd))
          case Left(_) => try Thread.sleep(100) catch { case _: InterruptedException => }
        }
      }
      result.getOrElse(
        if (progress.stopped || !isRunning) error("partial check cancelled before line " + p.line + " resolved")
        else error("could not resolve line " + p.line + " in " + p.target.theory))
    }

    /** Outcome classification for partial mode. evaluate drives a bounded visible
      * perspective to the target command and returns normally once it terminates,
      * so reaching the target is the ordinary `Exn.Res` success — there is no
      * line-reached cancel. A failure in the evaluated prefix is "errors"; a
      * caller cancel (timeout/disconnect) surfaces as its reason. Mirrors Full mode. */
    private def classify_partial(result: Exn.Result[Check_Engine.Result]): Outcome =
      result match {
        case Exn.Res(r) =>
          if (!r.ok) { progress.emit_post_result_error(r); Outcome.Failed("errors") }
          else if (progress.error_emitted) Outcome.Failed("errors")
          else if (cancelReason.isDefined) Outcome.Failed(cancelReason.get)
          else Outcome.Ok
        case Exn.Exn(exn) if Exn.is_interrupt(exn) =>
          if (cancelReason.isDefined) Outcome.Failed(cancelReason.get)
          else if (progress.error_emitted) Outcome.Failed("errors")
          else Outcome.Failed("interrupted")
        case Exn.Exn(ERROR(msg)) => Outcome.Failed(msg)
        case Exn.Exn(e) => Outcome.Failed("exception: " + e.getMessage)
      }

    /** Common finalize: record end time, set state, fan Finished, count down.
      * Both Full and Partial workers end here. */
    private def settle(out: Outcome): Unit = {
      endMs = System.currentTimeMillis()
      state = out
      fan(Event.Finished(out.ok, out.reason))
      latch.countDown()
    }

    def elapsedMs: Long =
      (if (endMs > 0) endMs else System.currentTimeMillis()) - startMs

    /** The settled per-theory status, sorted — for a final progress snapshot.
      * Prefers the engine result (the reliable consolidated state); falls back to
      * the live-recorded status if the worker hasn't returned. */
    def finalNodes: List[(Document.Node.Name, Document_Status.Node_Status)] =
      if (finalStatus.nonEmpty) finalStatus
      else progress.snapshot_status.toList.sortBy(_._1.theory)

    /** Status as a JSON object — for status replies and the submit ack. */
    def statusJson: JSON.Object.T = {
      val st = state
      JSON.Object(
        "state" -> (st match {
          case Outcome.Running => "running"
          case Outcome.Ok => "ok"
          case Outcome.Failed(_) => "failed"
        }),
        "ok" -> st.ok,
        "theories" -> theories,
        "elapsed_ms" -> elapsedMs,
        "nodes" -> progress.snapshot_status.toList.sortBy(_._1.theory)
          .map { case (n, s) => nodeStatusJson(n, s, Nil, progress.updateSeqOf(n)) }) ++
      (st match { case Outcome.Failed(r) if r.nonEmpty => JSON.Object("reason" -> r); case _ => JSON.Object() })
    }
  }

  /** The single in-flight check slot. At most one check runs at a time
    * (the check engine is not concurrency-safe on one session), so there is no
    * registry — just the current/last job. One daemon process per server, so a
    * single slot is correct. */
  private val slot = new AtomicReference[Option[Job]](None)

  /** The current job, if any (running OR the last one to have finished). Callers
    * read its status; `busy` keys on whether it is still running. */
  def current: Option[Job] = slot.get

  /** True iff a check is in flight — drives `ic2 server status` busy/idle. */
  def busy: Boolean = slot.get.exists(_.isRunning)

  /** Submit a check: resolve, start a Job, park it in `slot`, return it.
    * Non-blocking. REFUSES (Left) if a check is already running — the caller
    * must cancel it and resubmit the merged set. Left also on a resolution
    * error or an empty file list. Synchronized so two concurrent submits (e.g.
    * two MCP clients) can't both pass the busy check and race on the slot. */
  def submit(
    session: Headless.Session, resources: Headless.Resources, files: List[String]
  ): Either[String, Job] = slot.synchronized {
    if (busy) Left("a check is already in flight; cancel it before submitting another")
    else if (files.isEmpty) Left("empty files list")
    else resolveTargets(resources, files).map { resolved =>
      val job = new Job(resolved.map(_._1.theory), resolved.map(_._1), session,
        resources = Some(resources))
      slot.set(Some(job))
      job.start()
      job
    }
  }

  /** Submit a partial check: `check FILE --line N`. Resolves the single file,
    * plants a Partial job in the slot, and starts it. Same in-flight gate as
    * `submit` — checks never overlap regardless of mode. The full theory is
    * NOT evaluated: only the prefix of commands up to and including the
    * command that ends on or before line N. Left on any resolution failure
    * (bad file / bad line / node not loadable).
    *
    * `line` MUST be >= 1. `files` MUST contain exactly one .thy path
    * (partial checks are single-file by construction; asking for multiple
    * files + a single line is meaningless). */
  def submitPartial(
    session: Headless.Session, resources: Headless.Resources,
    files: List[String], line: Int
  ): Either[String, Job] = slot.synchronized {
    if (busy) Left("a check is already in flight; cancel it before submitting another")
    else if (files.length != 1)
      Left("partial check (--line) requires exactly one FILE, got " + files.length)
    else if (line <= 0) Left("line must be >= 1, got " + line)
    else resolveTargets(resources, files).map { resolved =>
      val (name, _) = resolved.head
      val mode = Mode.Partial(name, line = line)
      val job = new Job(List(name.theory), List(name), session,
        mode = mode, resources = Some(resources))
      slot.set(Some(job))
      job.start()
      job
    }
  }

  /** Start-of-check log line (always shown), tagged with the source path. */
  def logStart(progress: Progress, source: String, theories: List[String]): Unit =
    progress.echo("[" + source + "] check started: " + theories.length +
      " theory/theories: " + theories.mkString(", "))

  /** End-of-check log line (always shown): one of ok / FAILED(reason) /
    * ABORTED(reason), with elapsed time. */
  def logFinish(
    progress: Progress, source: String, elapsedMs: Long, ok: Boolean, reason: String
  ): Unit = {
    val verdict =
      if (ok) "ok"
      else if (reason == "interrupted") "ABORTED (interrupted)"
      else "FAILED (" + reason + ")"
    progress.echo("[" + source + "] check finished in " + elapsedMs + "ms — " + verdict)
  }
}


object IQ {

  /** The I/R endpoints surfaced by `ic2 server status`:
   *    - the client-facing repl.py bridge (raw I/R wire protocol), and
   *    - the MCP server in front of it (the repl_* tools).
   *  The in-prover ML_Repl is deliberately not advertised — clients go through
   *  the bridge / MCP. */
  case class IR_Endpoint(
    repl_port: Int, repl_token: Option[String],
    mcp_port: Option[Int] = None, mcp_token: Option[String] = None,
    repl_cli: Option[String] = None, repl_py: Option[String] = None
  ) {
    def json: JSON.Object.T = {
      def opt[A](k: String, v: Option[A]): JSON.Object.T =
        v match { case Some(x) => JSON.Object(k -> x); case None => JSON.Object() }
      JSON.Object("repl_port" -> repl_port) ++
        opt("repl_token", repl_token) ++
        opt("mcp_port", mcp_port) ++ opt("mcp_token", mcp_token) ++
        opt("repl_cli", repl_cli)
    }
  }

  /** The `repl.py cli` invocation PREFIX for this server's bridge, up to and
    * including `cli`: `[IR_AUTH_TOKEN=… ]python3 <irDir>/repl.py cli --port N`.
    * Callers append a verb + args. Token as an env prefix (not inline) so it
    * isn't mistaken for a positional and matches "tokens only via status". */
  def repl_cli_prefix(irDir: String, port: Int, token: Option[String]): String = {
    val replPy = (Path.explode(irDir) + Path.explode("repl.py")).expand.implode
    val env = token.filter(_.nonEmpty).map(t => "IR_AUTH_TOKEN=" + t + " ").getOrElse("")
    env + "python3 " + replPy + " cli --port " + port
  }

  /** A ready-to-paste `repl.py cli` example (the generic `Ir.theories ()` probe),
    * surfaced by `ic2 server status`. */
  def repl_cli_command(irDir: String, port: Int, token: Option[String]): String =
    repl_cli_prefix(irDir, port, token) + " raw -- 'Ir.theories ()'"

  /** The concrete `repl.py cli` command lines an agent uses to DRIVE a
    * just-created REPL named `repl`: step / show its state / inspect / list.
    * Built from this server's bridge endpoint so they are copy-paste runnable. */
  def repl_drive_schema(irDir: String, port: Int, token: Option[String], repl: String): String = {
    val p = repl_cli_prefix(irDir, port, token)
    List(
      "Drive this REPL with `repl.py cli` (one-shot client; `cli help` lists all verbs):",
      "  step:       " + p + " step "  + repl + " 'apply simp'",
      "  show state: " + p + " state " + repl + " -1",
      "  full text:  " + p + " text "  + repl,
      "  any ML:     " + p + " raw  -- 'Ir.show \"" + repl + "\"'").mkString("\n")
  }

  /** Create an I/R REPL named `repl` from a source location: resolve `file` +
    * 1-based `line` to the command spanning that line in the session's
    * document, then `Ir.init_from_document`. This needs BOTH the session (to map
    * line -> command id) and the connected I/R client, which only the daemon has
    * — the bare `repl.py cli` can't do it. Returns the REPL's reply, or Left on a
    * resolution error. `session` is the daemon's Headless.Session; `client` the
    * launched IRClient. */
  def replFromSource(
    session: Session, client: IRClient, file: String, line: Int, repl: String
  ): Either[String, String] =
    SessionTools.resolveNode(session, file).flatMap { name =>
      val content = SessionTools.nodeText(session, name)
      if (content.isEmpty)
        Left("theory not loaded (or empty): " + name.node + " — check it first with `ic2 check`")
      else {
        // 1-based line -> char offset of that line's start, clamped to the node.
        val lineDoc = Line.Document(content)
        val ln = math.max(0, line - 1)
        val offset = lineDoc.offset(Line.Position(ln)).getOrElse(
          if (ln <= 0) 0 else content.length - 1)
        SessionTools.commandAt(session, name, math.min(offset, math.max(0, content.length - 1)))
          .flatMap { command =>
            // The I/R reply is a success message OR an error. IRClient.send
            // raises on an `ERR`-framed reply (e.g. "REPL already exists"),
            // which we normalise to an "ERR: …" string. Route any error to
            // Left so the daemon answers with server_error (exit 3) instead of
            // dressing the failure up as a created REPL.
            val reply =
              try client.initFromDocument(repl, command.node_name.node, command.id.toInt)
              catch { case e: Throwable => "ERR: " + e.getMessage }
            if (reply.startsWith("ERR")) Left(reply.stripPrefix("ERR:").stripPrefix("ERR").trim)
            else Right(reply)
          }
      }
    }

  /** Outcome of bring-up: the endpoint for status, plus the resources the daemon
   *  must tear down on shutdown — the repl.py child and the MCP server (if up). */
  case class Started(endpoint: IR_Endpoint, repl_py: Process, mcp: Option[McpServer],
                     client: IRClient)


  /** Candidate AutoCorrode base directories, in priority order: $AUTOCORRODE_BASE
   *  if set, then the AutoCorrode tree this component lives inside (ic2 sits at
   *  <AutoCorrode>/ic2, so the base is $ISABELLE_IC2_HOME/..). */
  private def autocorrode_bases: List[Path] = {
    val base = Isabelle_System.getenv("AUTOCORRODE_BASE")
    val from_env = if (base.nonEmpty) List(Path.explode(base)) else Nil
    val in_tree = Path.explode("$ISABELLE_IC2_HOME") + Path.explode("..")
    from_env :+ in_tree
  }

  /** Locate the `ir/` directory (holds repl.py and the I/R ML sources). This is
   *  the `irDir` IRLauncher needs to load the ML and spawn repl.py. */
  def ir_dir: Option[Path] =
    autocorrode_bases.map(_ + Path.explode("ir")).find(_.is_dir)


  /** Bring up the I/R stack against the daemon's session via IRLauncher, and —
   *  only when `loadMcp` is set — stand up an MCP server offering the repl_*
   *  tools in front of it. Returns None when the I/R sources aren't found or
   *  bring-up fails. Never throws — I/R+MCP are best-effort and must not wedge
   *  daemon startup.
   *
   *  IRLauncher.launch does the I/R handshake: probe, ad-hoc-load the I/R ML if
   *  needed, IR_Repl.start, spawn repl.py, scrape its port/token, and connect a
   *  client. We keep that client: it backs `ic2 repl-create` and (when enabled)
   *  the MCP repl_* tools, via Ic2IRConnection. The MCP server is OFF by default
   *  (opt in with `ic2 server start --mcp`); the repl.py bridge + `repl.py cli` +
   *  `ic2 repl-create` work regardless. */
  def start(
    session: Headless.Session, resources: Headless.Resources, progress: Progress,
    loadMcp: Boolean
  ): Option[Started] = {
    ir_dir match {
      case None =>
        progress.echo_warning(
          "I/R: ir/ directory not found (set AUTOCORRODE_BASE, or keep ic2 inside " +
          "the AutoCorrode tree); skipping I/R setup")
        None
      case Some(dir) =>
        try {
          val irDir = dir.expand.implode
          progress.echo("Bringing up I/R against the session (sources in " + irDir + ") ...")
          val launcher = new IRLauncher(session, msg => progress.echo("I/R: " + msg))
          launcher.launch(irDir) match {
            case Right(launched) =>
              // Don't log the token — progress may be a persistent daemon log.
              // The token is surfaced on demand via `ic2 server status`. The cli command
              // is logged WITHOUT the token prefix for the same reason.
              progress.echo("I/R ready: repl.py on port " + launched.replPort)
              progress.echo("I/R one-shot client: python3 " +
                (Path.explode(launched.irDir) + Path.explode("repl.py")).expand.implode +
                " cli help   (token via `ic2 server status`)")
              // Stand up the MCP server over the connected client — only when
              // requested (`--mcp`). Best-effort: if it fails, I/R is still
              // reachable on the repl.py port directly. Off by default.
              val mcp =
                if (loadMcp) start_mcp(session, resources, launched, progress)
                else None
              val cli = repl_cli_command(launched.irDir, launched.replPort, launched.replToken)
              val replPy = (Path.explode(launched.irDir) + Path.explode("repl.py")).expand.implode
              val base = IR_Endpoint(launched.replPort, launched.replToken,
                repl_cli = Some(cli), repl_py = Some(replPy))
              val endpoint = mcp match {
                case Some((server, token)) =>
                  base.copy(mcp_port = server.port, mcp_token = Some(token))
                case None => base
              }
              Some(Started(endpoint, launched.process, mcp.map(_._1), launched.client))
            case Left(reason) =>
              progress.echo_warning("I/R bring-up failed: " + reason + " (continuing)")
              None
          }
        } catch {
          case exn: Throwable =>
            progress.echo_warning("I/R setup failed: " + exn.getMessage + " (continuing)")
            None
        }
    }
  }

  /** Lowest MCP port ic2 binds, with how many to scan upward (the McpServer
   *  binds the first free one — see McpServerConfig.portSpan). Same base 8765
   *  and 100-wide scan as I/Q, so ic2 is a drop-in for the same MCP client
   *  config / iq_bridge.py (whose default port is also 8765). I/Q and ic2 aren't
   *  meant to run at once; if they do, the scan steps ic2 to 8766, 8767, ... . */
  private val Mcp_Base_Port: Int = 8765
  private val Mcp_Port_Span: Int = 100

  /** Build an McpServer offering the I/R repl_* tools (IRTools over an
   *  Ic2IRConnection wrapping the connected client + session) and a `status`
   *  probe tool, and start it (on the first free port from Mcp_Base_Port).
   *  Returns the server + its token, or None on any failure (best-effort).
   *
   *  The auth token is taken from $IQ_AUTH_TOKEN if set (the same variable I/Q
   *  uses, so one pinned token covers the whole AutoCorrode MCP surface and can
   *  live in an MCP client config), else a fresh UUID is generated and reported
   *  by `ic2 server status`. */
  private def start_mcp(
    session: Headless.Session, resources: Headless.Resources,
    launched: IRLauncher.Launched, progress: Progress
  ): Option[(McpServer, String)] = {
    try {
      val token = Isabelle_System.getenv("IQ_AUTH_TOKEN").trim match {
        case t if t.nonEmpty => t
        case _ => UUID.random_string()
      }
      val config = McpServerConfig(
        port = Mcp_Base_Port,
        portSpan = Mcp_Port_Span,
        authToken = token,
        maxClientThreads = 10,
        serverName = "ic2-ir-mcp-server",
        logName = "ic2 MCP",
        threadPrefix = "ic2-mcp",
        authToolDescription =
          "Authenticate with the ic2 I/R MCP server. Must be called before any " +
          "other tool. Use the IQ_AUTH_TOKEN value, or the token reported by " +
          "`isabelle ic2 server status`.")
      val json = new McpJsonCodec {
        def parse(line: String): JSON.T = JSON.parse(line)
        def format(value: Any): String = JSON.Format(value)
      }
      // McpServer already prefixes its own diagnostics with logName ("ic2 MCP"),
      // so don't prepend it again here. info/security are high-level and always
      // shown; debug is the per-request trace, gated behind -v (verbose=true).
      val logger = new McpLogger {
        def info(message: String): Unit = progress.echo(message)
        def security(message: String): Unit = progress.echo("ic2 MCP [SECURITY]: " + message)
        override def debug(message: String): Unit = progress.echo(message, verbose = true)
      }
      val server = new McpServer(config = config, json = json, logger = logger)
      val conn = new Ic2IRConnection(launched, session)
      // A `status` tool: a no-arg liveness/diagnostic probe for the MCP server
      // itself — confirms the server answers, the I/R bridge is reachable, and
      // reports the connected I/R directory. Useful for testing the full chain.
      val statusTool = McpTool(
        name = "status",
        description = "ic2 MCP server status: liveness, I/R bridge reachability, " +
          "and the connected I/R directory. Takes no arguments.",
        inputSchema = Map("type" -> "object", "properties" -> Map.empty[String, Any],
          "additionalProperties" -> false),
        handler = _ => Right(McpToolResult.fromMap(Map(
          "text" ->
            ("ic2 MCP server OK; I/R bridge " +
             (if (conn.client.exists(_.isConnected)) "reachable on port " + launched.replPort
              else "NOT reachable") +
             "; ir_dir=" + launched.irDir)))))
      val registration =
        server.register(statusTool)
          .flatMap(_ => server.register(checkTool(session, resources, progress)))
          .flatMap(_ => server.register(checkAsyncTool(session, resources, progress)))
          .flatMap(_ => server.register(checkStatusTool))
          .flatMap(_ => server.register(checkCancelTool))
          .flatMap(_ => new SessionClient(session, server).register())
          .flatMap(_ => new IRTools(server, conn).register())
      registration match {
        case Right(()) =>
          server.start()
          // Don't log the token — progress may be a persistent daemon log. The
          // token is surfaced on demand via `ic2 server status`.
          progress.echo("ic2 MCP server ready on port " + server.port.getOrElse(0))
          Some((server, token))
        case Left(err) =>
          progress.echo_warning("ic2 MCP: failed to register tools: " + err + " (continuing)")
          None
      }
    } catch {
      case exn: Throwable =>
        progress.echo_warning("ic2 MCP server failed to start: " + exn.getMessage + " (continuing)")
        None
    }
  }

  /** Map a Job's progress count to an MCP notifications/progress dict. */
  private def progressDict(done: Int, total: Int): JSON.Object.T =
    JSON.Object(
      "progress" -> done, "total" -> total,
      "message" -> (done.toString + "/" + total + " theories processed" +
        (if (done < total) ", " + (total - done) + " pending" else "")))

  /** Subscribe an MCP progress sink to a job: translate the job's Progress /
    * Finished events into notifications/progress (N of M theories consolidated).
    * Returns the unsubscribe thunk. No-op sink (client didn't opt in) still
    * subscribes but emits nothing. */
  private def subscribeMcpProgress(job: Check.Job, sink: McpProgress.Sink): () => Unit = {
    val total = job.theories.length
    def processed(nodes: List[(Document.Node.Name, Document_Status.Node_Status)]): Int =
      math.min(nodes.count { case (n, st) => job.nodeNames.contains(n) && st.consolidated }, total)
    job.subscribe {
      case Check.Event.Progress(nodes, _, _) => sink(progressDict(processed(nodes), total))
      case Check.Event.Finished(ok, _) => sink(progressDict(if (ok) total else 0, total))
      case _ =>
    }
  }

  /** The blocking `check` MCP tool: submit a Job and wait for it, the MCP
    * analogue of a foreground `isabelle ic2 check`. Submitting is the one
    * primitive (Check.submit, non-blocking); this tool layers the blocking
    * policy on top — subscribe a notifications/progress sink, then await. On
    * `timeout_secs` expiry it cancels the job (reason "timeout"). The job runs
    * with first-error stop. Result: { ok, theories, [reason] }. Session-mutating,
    * so ic2-specific (not in the session-generic SessionClient). */
  private def checkTool(
    session: Headless.Session, resources: Headless.Resources, log: Progress
  ): McpTool =
    McpTool(
      name = "check",
      description = "Type-check .thy files against the resident session (the MCP " +
        "analogue of `isabelle ic2 check`). Files must be absolute paths to " +
        "existing .thy files. Returns ok plus the resolved theory names; on " +
        "failure, a reason. Stops at the first failed theory. Blocks until the " +
        "check completes; reports N/M theories processed via notifications/" +
        "progress when the client supplied a progressToken. Aborts with " +
        "reason \"timeout\" if it exceeds `timeout_secs` (default 600). For a " +
        "non-blocking submit, use `check_async`. With `line`, check only the " +
        "prefix of the (single) file up to and including the command that ends " +
        "on or before that source line — same UI, same cancel semantics, but " +
        "later commands are left unprocessed. Useful for iterative development.",
      inputSchema = Map(
        "type" -> "object",
        "properties" -> Map(
          "files" -> Map("type" -> "array", "items" -> Map("type" -> "string"),
            "description" -> "Absolute paths of .thy files to check"),
          "line" -> Map("type" -> "integer",
            "description" -> ("If set, check only the prefix of the (single) " +
              "file up to line N (1-based). files must contain exactly one path.")),
          "timeout_secs" -> Map("type" -> "integer",
            "description" -> ("Abort the check after this many seconds " +
              "(default 600; 0 = unlimited)."))),
        "required" -> List("files"),
        "additionalProperties" -> false),
      handlerP = (params, progress) => {
        val (files, timeoutSecs, line) =
          (checkFiles(params), checkTimeoutSecs(params), checkLine(params))
        if (timeoutSecs < 0) Left("check: 'timeout_secs' must be >= 0 (0 = unlimited)")
        else submit_by_mode_mcp(session, resources, files, line) match {
          case Left(msg) => Left("check: " + msg)
          case Right(job) =>
            Check.logStart(log, "mcp", job.theories)
            val unsubscribe = subscribeMcpProgress(job, progress)
            try {
              val timeoutMs = timeoutSecs.toLong * 1000L
              if (timeoutMs > 0 && !job.await(timeoutMs) && job.isRunning)
                job.cancel("timeout")
              val out = job.await()
              Check.logFinish(log, "mcp", job.elapsedMs, out.ok, out.reason)
              val base = Map[String, Any]("ok" -> out.ok, "theories" -> job.theories)
              Right(McpToolResult.fromMap(
                if (out.ok) base else base + ("reason" -> out.reason)))
            } finally unsubscribe()
        }
      })

  /** Non-blocking `check_async`: submit the check and return its status
    * immediately. The check keeps running after this call returns; poll
    * `check_status` for progress/outcome and `check_cancel` to abort. Refuses
    * (isError) if a check is already in flight — cancel it and resubmit. */
  private def checkAsyncTool(
    session: Headless.Session, resources: Headless.Resources, log: Progress
  ): McpTool =
    McpTool(
      name = "check_async",
      description = "Submit a .thy check WITHOUT blocking: returns immediately " +
        "with the check's status while it runs in the background. Poll " +
        "`check_status` for progress and the final outcome; `check_cancel` " +
        "aborts it. Only one check runs at a time: this fails if one is already " +
        "in flight (cancel it and resubmit the merged set of files). Files must " +
        "be absolute .thy paths. Use plain `check` for a blocking call. With " +
        "`line`, check only the prefix of the (single) file up to that line.",
      inputSchema = Map(
        "type" -> "object",
        "properties" -> Map(
          "files" -> Map("type" -> "array", "items" -> Map("type" -> "string"),
            "description" -> "Absolute paths of .thy files to check"),
          "line" -> Map("type" -> "integer",
            "description" -> ("If set, check only the prefix of the (single) " +
              "file up to line N (1-based). files must contain exactly one path."))),
        "required" -> List("files"),
        "additionalProperties" -> false),
      handler = params =>
        submit_by_mode_mcp(session, resources, checkFiles(params), checkLine(params)) match {
          case Left(msg) => Left("check_async: " + msg)
          case Right(job) =>
            Check.logStart(log, "mcp-async", job.theories)
            // Log the boundary when the backgrounded check finishes (no waiter).
            val _ = job.subscribe {
              case Check.Event.Finished(ok, reason) =>
                Check.logFinish(log, "mcp-async", job.elapsedMs, ok, reason)
              case _ =>
            }
            Right(McpToolResult.fromMap(job.statusJson.asInstanceOf[Map[String, Any]]))
        })

  /** `check_status`: report the current/last check's state (running/ok/failed),
    * elapsed time, per-theory node status, and reason on failure. No argument —
    * there is at most one check. */
  private val checkStatusTool: McpTool =
    McpTool(
      name = "check_status",
      description = "Status of the current (or last) check: state " +
        "(running/ok/failed), elapsed time, per-theory processing status, and " +
        "the failure reason if any. No argument — at most one check runs at a time.",
      inputSchema = Map(
        "type" -> "object", "properties" -> Map(), "additionalProperties" -> false),
      handler = _ =>
        Check.current match {
          case Some(job) => Right(McpToolResult.fromMap(job.statusJson.asInstanceOf[Map[String, Any]]))
          case None => Right(McpToolResult.fromMap(Map("state" -> "idle")))
        })

  /** `check_cancel`: abort the in-flight check (reason "cancelled"). No argument;
    * a no-op if nothing is running. */
  private val checkCancelTool: McpTool =
    McpTool(
      name = "check_cancel",
      description = "Cancel the in-flight check (reason \"cancelled\"). No " +
        "argument — at most one check runs at a time. A no-op if none is running.",
      inputSchema = Map(
        "type" -> "object", "properties" -> Map(), "additionalProperties" -> false),
      handler = _ => {
        val running = Check.current.exists(_.isRunning)
        if (running) Check.current.foreach(_.cancel("cancelled"))
        Right(McpToolResult.fromMap(Map(
          "cancelled" -> running,
          "message" -> (if (running) "cancellation requested" else "no check running"))))
      })

  /* ---- check param helpers (shared by check / check_async) ---- */

  private def checkFiles(params: McpToolParams): List[String] =
    params.toMap.get("files") match {
      case Some(l: List[_]) => l.collect { case s: String => s }
      case _ => Nil
    }
  private def checkTimeoutSecs(params: McpToolParams): Int =
    params.toMap.get("timeout_secs") match {
      case Some(n: Long) => n.toInt
      case Some(n: Int) => n
      case Some(n: Double) => n.toInt
      case _ => 600
    }
  private def checkLine(params: McpToolParams): Option[Int] =
    params.toMap.get("line") match {
      case Some(n: Long) => Some(n.toInt)
      case Some(n: Int) => Some(n)
      case Some(n: Double) => Some(n.toInt)
      case _ => None
    }
  /** Shared full-vs-partial submit dispatcher for the MCP tools. */
  private def submit_by_mode_mcp(
    session: Headless.Session, resources: Headless.Resources,
    files: List[String], line: Option[Int]
  ): Either[String, Check.Job] =
    line match {
      case Some(l) => Check.submitPartial(session, resources, files, l)
      case None => Check.submit(session, resources, files)
    }
}


/** IRConnection for the headless ic2 host. The I/R client + session are already
 *  live (from IRLauncher), so `connect` is a no-op reachability check.
 *  `resolveFile` completes a file argument against the session's loaded theory
 *  nodes and reads its text from disk (no jEdit buffers). */
final class Ic2IRConnection(launched: IRLauncher.Launched, val session: Session)
extends IRConnection {

  def connect(irHome: Option[String]): Either[String, String] =
    if (launched.client.isConnected) Right(launched.irDir)
    else Left("I/R REPL not reachable (repl.py bridge down)")

  def client: Option[IRClient] = Some(launched.client)

  /** Complete `file` against the loaded session nodes (suffix match on the node
   *  path, like I/Q's autocomplete but over the document graph, not jEdit
   *  buffers) and read the completed file from disk. An absolute path that
   *  exists is taken as-is. */
  def resolveFile(file: String): Either[String, (String, String)] = {
    val candidates =
      session.snapshot().version.nodes.iterator
        .map(_._1.node).filter(_.nonEmpty).toList.distinct
    val resolved =
      candidates.filter(_.endsWith(file)) match {
        case List(one) => Right(one)
        case Nil =>
          val f = new java.io.File(file)
          if (f.isFile) Right(f.getPath)
          else Left(s"No loaded theory matching '$file' (and not an existing file path)")
        case many =>
          Left(s"Multiple loaded theories match '$file': ${many.mkString(", ")}")
      }
    resolved.flatMap { path =>
      try Right((path, File.read(new java.io.File(path))))
      catch { case exn: Throwable => Left(s"Cannot read $path: ${exn.getMessage}") }
    }
  }
}
