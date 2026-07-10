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
 *  There is AT MOST ONE check in flight at a time, server-wide: `use_theories`
 *  is not safe to run concurrently on the one `Headless.Session` (the calls
 *  share a single document state + version history), so `submit` refuses a new
 *  check while one is running. The caller cancels the running check and
 *  resubmits the merged set of theories. Because checks never overlap, there is
 *  no registry, no job ids, and no per-check bookkeeping — just `slot`. */
object Check {

  /* Headless.Session is batch-oriented: its "cancel" only flips
   * progress.stopped (the ML kernel keeps running the tactic), and its liveness
   * signals over-count forked proofs. ic2 needs live progress and a real stop,
   * so it reaches below the public API in two places (details in each docstring):
   *   (a) Timing_Tracker — reports which commands are genuinely executing.
   *   (b) cancelViaEdit() — reclaims a still-running forked proof after stop().
   */

  /** Delegates to `SessionTools.resolveFileTargets`, which is the shared
    * file→(Node.Name, theory-string) resolver used by both this check
    * pipeline and the parse-only loader (`SessionTools.parseFiles`). */
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
   * Job: a single check (the one running `use_theories`), held by `slot`.
   *
   * `submit` is non-blocking: it resolves targets, starts a worker running
   * use_theories, parks the Job in `slot`, and returns. It REFUSES if a job is
   * already running (Left) — checks never overlap. A Job outlives the
   * connection/request that started it.
   *
   * Blocking is a CALLER-SIDE policy on top of submit: subscribe to the job's
   * events, await its terminal state, and (for the wire path) cancel the job if
   * the caller's own connection drops. The Job itself never knows or cares
   * whether anyone is watching.
   *
   * The Job carries a Job_Progress doing the session-generic work: track
   * per-theory Node_Status, FIRST-ERROR STOP (set the failed theory + stop(),
   * which use_theories polls and cancels), and fan typed Events out to
   * subscribers. Each transport renders Events its own way (wire JSON events;
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
    runningCommands: List[RunningCommand] = Nil
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
    * Returns Nil when no tracker is bound. The threshold is applied by the
    * CLIENT (`--long-running`), so this reports every live command. */
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
      runningCommands: Map[Document.Node.Name, List[RunningCommand]] = Map.empty
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

  /** Progress driver for a Job: the single Progress passed to use_theories.
    * Records per-theory status, performs first-error stop, and fans Events to
    * the job's subscribers. A background ticker re-emits Progress events with
    * fresh elapsed times so long-running-command payloads keep updating even
    * when the document itself is quiet (a spinning command triggers no
    * commands_changed events). Session-generic; carries no transport. */
  private final class Job_Progress(job: Job, session: Headless.Session) extends Progress {
    private val per_theory =
      Synchronized(Map.empty[Document.Node.Name, Document_Status.Node_Status])
    private val error_latch = Synchronized(false)
    private val last_emit = Synchronized[Option[Long]](None)
    private val emit_interval_ms: Long = 200
    private val tick_interval_ms: Long = 500
    @volatile private var ticker: Option[Thread] = None
    @volatile private var ticker_stop: Boolean = false

    def error_emitted: Boolean = error_latch.value
    private def claim_error(): Boolean = error_latch.change_result(e => (true, !e))
    def snapshot_status: Map[Document.Node.Name, Document_Status.Node_Status] = per_theory.value

    // Partial-mode watchdog (check --line): once the target command is armed,
    // fire `reached()` as soon as it reports is_terminated. Single-shot. The
    // ticker polls it (a spinning target may emit no fresh nodes_status
    // callback, so we can't rely on that path alone).
    @volatile private var partial_target: Option[(Command, () => Unit)] = None
    private val partial_fired = new java.util.concurrent.atomic.AtomicBoolean(false)
    def set_partial_target(
      name: Document.Node.Name, cmd: Command, reached: () => Unit
    ): Unit = { val _ = name; partial_target = Some((cmd, reached)) }
    private def check_partial_reached(): Unit = {
      if (partial_fired.get) return
      partial_target.foreach { case (cmd, reached) =>
        try {
          val state = session.get_state()
          state.stable_tip_version.foreach { version =>
            val cs = state.command_status(version, cmd)
            if (cs.is_terminated && partial_fired.compareAndSet(false, true))
              try reached() catch { case _: Throwable => }
          }
        } catch { case _: Throwable => /* best-effort */ }
      }
    }

    /** Idempotent; exits when `ticker_stop` or the first-error latch fires. */
    def start_ticker(): Unit = synchronized {
      if (ticker.isDefined) return
      val t = new Thread(new Runnable {
        def run(): Unit = {
          while (!ticker_stop && !error_emitted) {
            try {
              check_partial_reached()
              val cur = per_theory.value
              if (cur.nonEmpty) {
                val running = snapshotRunning(cur)
                if (running.nonEmpty)
                  job.fan(Event.Progress(cur.toList.sortBy(_._1.theory), running))
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

    /** Stop the ticker WITHOUT triggering the Progress cancel path — used from
      * the worker's `finally` after use_theories returns normally. */
    def stop_ticker(): Unit = ticker_stop = true

    override def stop(): Unit = { ticker_stop = true; super.stop() }

    private def snapshotRunning(
      status: Map[Document.Node.Name, Document_Status.Node_Status]
    ): Map[Document.Node.Name, List[RunningCommand]] =
      status.iterator
        .filter { case (_, st) => !st.consolidated }
        .flatMap { case (name, _) =>
          val rcs = runningCommandsFor(session, name)
          if (rcs.isEmpty) None else Some(name -> rcs)
        }.toMap

    override def nodes_status(ns: Progress.Nodes_Status): Unit = {
      if (stopped || error_emitted) return
      // Partial mode: check the line-reached watchdog on every callback (the
      // primary trigger while use_theories streams status); the ticker polls
      // it too, for a target whose spin emits no fresh callback.
      check_partial_reached()
      val updated = per_theory.change_result { cache =>
        var c = cache
        for (name <- ns.domain) { val st = ns(name); if (!st.is_empty) c = c + (name -> st) }
        (c, c)
      }
      updated.find { case (_, st) => st.failed > 0 } match {
        case Some((name, _)) =>
          if (claim_error()) {
            val state = session.get_state()
            val snap = if (state.stable_tip_version.isDefined) Some(state.snapshot(name)) else None
            emit_error_from(name, snap)
            super.stop()   // first-error stop: use_theories polls stopped and cancels
          }
        case None =>
          val now = System.currentTimeMillis()
          val emit = last_emit.change_result {
            case Some(t) if now - t < emit_interval_ms => (false, Some(t))
            case _ => (true, Some(now))
          }
          if (emit)
            job.fan(Event.Progress(updated.toList.sortBy(_._1.theory), snapshotRunning(updated)))
      }
    }

    /** Emit a final Progress snapshot (end-state percentages). No live commands
      * remain here (the run has settled), so `runningCommands` is empty. */
    def flush_final(): Unit = {
      val cur = per_theory.value
      if (cur.nonEmpty) job.fan(Event.Progress(cur.toList.sortBy(_._1.theory)))
    }

    /** Post-result fallback: result is failure but the live callback never saw
      * it (consolidation on the final tick). Emit the first error, once. */
    def emit_post_result_error(result: Headless.Use_Theories_Result): Unit =
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

  /** What granularity a Job targets. Full-theory checks run `use_theories` (the
    * common case). A partial check limits evaluation to a prefix of ONE theory
    * ending at a resolved command — it drives `session.update` with a bounded
    * perspective directly and consumes `commands_changed` callbacks to track
    * progress.
    *
    * Both modes reuse the same event fan-out, cancel-running-execs +
    * cancel-pulse, subscribe API, and status JSON — they differ ONLY in the
    * worker body. The UI (wire events, MCP progress notifications, ANSI/plain
    * bars) is identical: from the client's point of view a partial check is a
    * fast full check on a single-theory job. */
  sealed trait Mode
  object Mode {
    case object Full extends Mode
    /** Partial-check target: the node under test, its theory-string (as
      * `use_theories` expects — the same value Full mode passes, derived from
      * resolveFileTargets, NOT the already-qualified `target.theory`), and the
      * 1-based caret line. partial_body runs `use_theories(targetTheory)` and
      * stops it once the command at `line` has been processed. */
    final case class Partial(
      target: Document.Node.Name, targetTheory: String, line: Int
    ) extends Mode
  }

  /** A check job: a worker thread running `use_theories` (Full mode, or Partial
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
    // The settled per-theory status from use_theories' result — the reliable
    // terminal state (the last live nodes_status callback lags consolidation),
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
    /** Cancel the check — mechanism (b). `progress.stop()` flips
      * `progress.stopped`, so `use_theories` unwinds (cancel_result +
      * unload_theories, un-scheduling not-yet-dispatched commands). That alone
      * does NOT interrupt a running ML tactic — its unload edit is text-neutral
      * — so the worker's `finally` runs `cancelViaEdit()` once use_theories has
      * returned, which reclaims any still-running fork via a text-changing tail
      * edit. */
    def cancel(reason: String = "cancelled"): Unit = {
      if (cancelReason.isEmpty) cancelReason = Some(reason)
      progress.stop()
    }

    /** Reclaim any still-running forked proofs after `use_theories` has returned
      * (its `finally` ran `unload_theories`, so the node is no longer required).
      * A text-changing tail edit per incomplete target node — batched into one
      * `session.update` — makes PIDE re-split the tail and cancel the superseded
      * execs and their forks (see SessionTools.resetNodeTails); the batch stop
      * path skips this because its unload edit leaves the text unchanged. Safe
      * to call unconditionally: a consolidated node has no running command, so
      * `cancelFrontier` returns None and the edit is a no-op. Best-effort. */
    private def cancelViaEdit(): Unit =
      try {
        val cuts = nodeNames.flatMap(n => SessionTools.cancelFrontier(session, n).map(n -> _))
        SessionTools.resetNodeTails(session, cuts)
      } catch { case _: Throwable => /* best-effort */ }

    def await(): Outcome = { latch.await(); state }
    /** Bounded await; returns true if it reached a terminal state in time. */
    def await(ms: Long): Boolean = latch.await(ms, java.util.concurrent.TimeUnit.MILLISECONDS)

    private[Check] def start(theoryStrings: List[String]): Unit = {
      startMs = System.currentTimeMillis()
      fan(Event.Started(theories))
      progress.start_ticker()
      val body: Runnable = mode match {
        case Mode.Full => full_body(theoryStrings)
        case p: Mode.Partial => partial_body(p)
      }
      val t = new Thread(body, "ic2-check")
      t.setDaemon(true)
      worker = t
      t.start()
    }

    /** The Full-mode worker: run `use_theories` and classify the outcome from
      * its result + the observed cancel/first-error flags. */
    private def full_body(theoryStrings: List[String]): Runnable = new Runnable {
      def run(): Unit = {
        val result =
          try Exn.Res(session.use_theories(theoryStrings,
            qualifier = Sessions.DRAFT, master_dir = "",
            check_delay = Time.seconds(0.2), watchdog_timeout = Time.seconds(0),
            nodes_status_delay = Time.seconds(0.2), progress = progress))
          catch { case e: Throwable => Exn.Exn(e) }
          finally {
            progress.stop_ticker()   // does NOT set progress.stopped
            progress.flush_final()
            // use_theories has returned (its finally ran unload_theories, so
            // the node is no longer required) — reclaim any still-running fork
            // now via a text-changing tail edit. No-op unless something is
            // still executing (i.e. this check was cancelled mid-flight).
            cancelViaEdit()
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
              // A first-error stop reads as failure even if use_theories also
              // returned (the cancel and the result can race on the last tick).
              if (progress.error_emitted) Outcome.Failed("first-error stop")
              else if (cancelReason.isDefined) Outcome.Failed(cancelReason.get)
              else if (r.ok) Outcome.Ok
              else { progress.emit_post_result_error(r); Outcome.Failed("errors") }
            // An interrupt the CALLER caused (timeout/disconnect/explicit
            // cancel) surfaces as that reason. But a real error must never be
            // masked as a bare interrupt: if the run actually saw a failed
            // node, classify it as the error — errors win over a no-reason
            // interrupt. Only a truly reasonless interrupt is "interrupted".
            case Exn.Exn(exn) if Exn.is_interrupt(exn) =>
              if (cancelReason.isDefined) Outcome.Failed(cancelReason.get)
              else if (progress.error_emitted) Outcome.Failed("first-error stop")
              else Outcome.Failed("interrupted")
            case Exn.Exn(e) => Outcome.Failed("exception: " + e.getMessage)
          }
        settle(out)
      }
    }

    /** The Partial-mode worker for `check FILE --line N`.
      *
      * Runs a normal `use_theories([target])` — which loads and evaluates the
      * target's whole dependency closure exactly like a full check, so the
      * prefix type-checks and Headless.Resources' bookkeeping stays
      * consistent (no direct session.update, so no double-load desync with a
      * later full check) — and STOPS it as soon as the caret line has been
      * processed:
      *
      *  - a background resolver waits for the target's commands to parse,
      *    resolves `line N` to a target Command (jEdit walk-back, same as
      *    `query state-at --line N`), and hands it to the watchdog;
      *  - the watchdog (driven by the ticker) fires `cancel("line-reached")`
      *    once the target command reaches `is_terminated`. That flips
      *    `progress.stopped` (use_theories unwinds via cancel_result +
      *    unload_theories, un-scheduling not-yet-dispatched tail commands);
      *    the `finally`'s `cancelViaEdit` then interrupts any tail command
      *    already forked.
      *
      * This can OVERSHOOT slightly: with parallel proofs enabled, commands
      * after the target line may already have been dispatched (forked) by the
      * time the target terminates, so they run until the cancel reaches them.
      * That's an accepted imprecision — it never under-evaluates the prefix,
      * and with `-o parallel_proofs=0` (sequential eval) there is no overshoot
      * at all (the test uses that for determinism). A "line-reached" cancel is
      * the SUCCESS outcome; a real first-error or other interrupt still
      * surfaces as failure.
      *
      * A partial check always ends by cancelling the tail, so its `finally`
      * runs `cancelViaEdit` (mechanism (b)): the text-changing tail edit both
      * interrupts any still-forked tail command and re-mints the abandoned tail
      * — otherwise a later check of this theory would hang on it. */
    private def partial_body(p: Mode.Partial): Runnable = new Runnable {
      def run(): Unit = {
        val out =
          try {
            arm_target_resolver(p)
            val result: Exn.Result[Headless.Use_Theories_Result] =
              try Exn.Res(session.use_theories(List(p.targetTheory),
                qualifier = Sessions.DRAFT, master_dir = "",
                check_delay = Time.seconds(0.2), watchdog_timeout = Time.seconds(0),
                nodes_status_delay = Time.seconds(0.2), progress = progress))
              catch { case e: Throwable => Exn.Exn(e) }
            classify_partial(result)
          }
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
            // A partial check always ends by cancelling the tail (line-reached
            // fires cancel). The text-changing tail edit interrupts any tail
            // command still forked AND re-mints the tail's exec_ids, so a later
            // check of this theory resumes and evaluates the remainder instead
            // of hanging on the abandoned (never-consolidated) tail.
            cancelViaEdit()
          }
        settle(out)
      }
    }

    /** Background poller: wait (bounded) for the target node's commands to
      * appear (use_theories' change_parser is async), resolve `line N` to a
      * Command, install it as the watchdog target on Job_Progress. If it
      * can't resolve (theory shorter than N, parse error), cancel with a
      * clear reason so the outcome is reported cleanly rather than hanging. */
    private def arm_target_resolver(p: Mode.Partial): Unit = {
      val t = new Thread(new Runnable {
        def run(): Unit = {
          val deadline = System.currentTimeMillis() + 30000
          var resolved: Option[Command] = None
          while (resolved.isEmpty && System.currentTimeMillis() < deadline
                 && !progress.stopped && isRunning) {
            SessionTools.commandsUpToLine(session, p.target, p.line) match {
              case Right((_, cmd, _)) => resolved = Some(cmd)
              case Left(_) => try Thread.sleep(100) catch { case _: InterruptedException => return }
            }
          }
          resolved match {
            case Some(cmd) => progress.set_partial_target(p.target, cmd, () => cancel("line-reached"))
            case None => if (cancelReason.isEmpty && isRunning) cancel("could not resolve line " + p.line)
          }
        }
      }, "ic2-partial-target-resolver")
      t.setDaemon(true)
      t.start()
    }

    /** Outcome classification for partial mode. A "line-reached" cancel is
      * SUCCESS — the target was reached, the tail was intentionally
      * abandoned. Everything else (first-error stop, other cancel reasons,
      * genuine interrupts) surfaces as failure, matching Full mode. */
    private def classify_partial(result: Exn.Result[Headless.Use_Theories_Result]): Outcome =
      result match {
        case Exn.Res(r) =>
          if (progress.error_emitted) Outcome.Failed("first-error stop")
          else if (cancelReason.contains("line-reached")) Outcome.Ok
          else if (cancelReason.isDefined) Outcome.Failed(cancelReason.get)
          else if (r.ok) Outcome.Ok
          else { progress.emit_post_result_error(r); Outcome.Failed("errors") }
        case Exn.Exn(exn) if Exn.is_interrupt(exn) =>
          if (cancelReason.contains("line-reached")) Outcome.Ok
          else if (cancelReason.isDefined) Outcome.Failed(cancelReason.get)
          else if (progress.error_emitted) Outcome.Failed("first-error stop")
          else Outcome.Failed("interrupted")
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
      * Prefers use_theories' result (the reliable consolidated state); falls
      * back to the live-recorded status if the worker hasn't returned. */
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
          .map { case (n, s) => nodeStatusJson(n, s) }) ++
      (st match { case Outcome.Failed(r) if r.nonEmpty => JSON.Object("reason" -> r); case _ => JSON.Object() })
    }
  }

  /** The single in-flight check slot. At most one check runs at a time
    * (use_theories is not concurrency-safe on one session), so there is no
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
      val job = new Job(resolved.map(_._1.theory), resolved.map(_._1), session)
      slot.set(Some(job))
      job.start(resolved.map(_._2))
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
      val (name, theoryStr) = resolved.head
      val mode = Mode.Partial(name, theoryStr, line = line)
      val job = new Job(List(name.theory), List(name), session,
        mode = mode, resources = Some(resources))
      slot.set(Some(job))
      job.start(Nil)   // Partial worker ignores theoryStrings
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
          .flatMap(_ => server.register(loadFilesTool(session, resources, progress)))
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
      case Check.Event.Progress(nodes, _) => sink(progressDict(processed(nodes), total))
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

  /** MCP `load_files`: parse the given .thy files into the session's document
    * graph without evaluating them. Wraps `SessionTools.parseFiles`. On
    * success returns `{loaded: [<node paths>], count: N}`; on failure the
    * tool returns an isError result carrying the resolution/header-parse
    * message. */
  private def loadFilesTool(
    session: Headless.Session, resources: Headless.Resources, log: Progress
  ): McpTool =
    McpTool(
      name = "load_files",
      description = "Parse .thy files into the session's document graph " +
        "WITHOUT evaluating any commands. The Scala side splits each theory " +
        "into commands (fixing spans/IDs/offsets), so `list_files`, " +
        "`get_entities`, `get_command_info`, and friends can then see the " +
        "theory shape — but no proof state is produced, no ML work runs. Use " +
        "for cheap structural exploration; call `check` afterwards to " +
        "actually evaluate. Files must be absolute .thy paths. Header " +
        "imports must be locatable in the session.",
      inputSchema = Map(
        "type" -> "object",
        "properties" -> Map(
          "files" -> Map("type" -> "array", "items" -> Map("type" -> "string"),
            "description" -> "Absolute paths of .thy files to parse-load")),
        "required" -> List("files"),
        "additionalProperties" -> false),
      handler = params =>
        SessionTools.parseFiles(session, resources, checkFiles(params)) match {
          case Left(msg) => Left("load_files: " + msg)
          case Right(names) =>
            log.echo("[mcp] load-files: " + names.length + " theory node(s)")
            Right(McpToolResult.fromMap(Map(
              "loaded" -> names.map(_.node),
              "count" -> names.length)))
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
