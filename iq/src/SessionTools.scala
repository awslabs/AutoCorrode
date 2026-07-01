/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/* Session-generic diagnostic / introspection logic.

   A family of read-only analyses over an `isabelle.Session` that work
   identically for the live PIDE session (Isabelle/jEdit) and a headless
   `Headless.Session` (ic2): list nodes, processing status, diagnostics, sorry
   positions, document info, declared entities, proof blocks, and per-command /
   per-selection introspection (command info, context + goal state).

   Everything here reads only the document SNAPSHOT (Document.Version /
   Document.Snapshot / Command markup via Rendering / Protocol) — base PIDE API,
   no jEdit. The two host-specific concerns it deliberately does NOT do are
   resolved by the caller and passed in:

     - PATH COMPLETION against the editor's open buffers / tracked files. Here
       the candidate set is the session's loaded NODES (version.nodes). The
       jEdit difference (Document_Model = open buffers + tracked files) is a
       superset for unprocessed-but-open files and a subset for loaded-but-never
       -opened imports; see resolveNode.
     - TEXT SOURCE. jEdit reads the live (possibly unsaved) buffer; here the
       node's own source is reconstructed from its command spans, so text
       offsets and the commands they index can never drift apart.

   Overlay-driven operations (get_definitions, explore — which RUN the
   isar_explore print function in the prover) are intentionally out of scope:
   they are not snapshot-generic. They stay on the I/Q side / belong with I/R.

   In `package isabelle` so it is shareable into `package isabelle.ic2`. */

package isabelle


object SessionTools {

  /* ---- keyword tables / patterns (ported from IQServer, kept identical) ---- */

  /** Declaration commands enumerated by `entities`. */
  val EntityKeywords: Set[String] =
    Set("lemma", "theorem", "corollary", "proposition", "schematic_goal",
      "definition", "abbreviation", "lift_definition", "fun", "function",
      "primrec", "datatype", "codatatype", "type_synonym", "record", "typedef",
      "inductive", "coinductive", "nominal_inductive", "locale", "class",
      "instantiation", "interpretation")

  /** Extracts the declared name following an entity keyword. */
  val EntityNamePattern =
    ("""(?:lemma|theorem|corollary|proposition|schematic_goal|definition|""" +
     """abbreviation|lift_definition|fun|function|primrec|datatype|codatatype|""" +
     """type_synonym|record|typedef|inductive|coinductive|nominal_inductive|""" +
     """locale|class|instantiation|interpretation)\s+([A-Za-z0-9_']+)""").r

  /** Commands that begin a proof block (for `proofBlocks`). */
  val ProofBlockStarters: Set[String] =
    Set("lemma", "theorem", "corollary", "proposition", "schematic_goal", "proof")

  private val ProofBlockStructuralEnders: Set[String] =
    Set("qed", "done", "sorry", "oops")

  /** Goal/statement openers and closers for the keyword-balance proof-context
    * test (`inProofContext`). */
  private val ContextProofOpeners: Set[String] =
    Set("lemma", "theorem", "corollary", "proposition", "schematic_goal", "proof",
      "have", "show", "obtain", "next", "fix", "assume", "define", "induction",
      "coinduction", "cases")
  private val ContextProofClosers: Set[String] =
    Set("qed", "done", "end", "sorry", "oops", "\\<close>")

  private val ProofStarters: Set[String] =
    Set("lemma", "theorem", "corollary", "proposition", "schematic_goal")

  private val SorryKeywords: Set[String] = Set("sorry", "oops")

  private def isMetaConstant(name: String): Boolean =
    name.startsWith("Pure.") || name == "Trueprop" || name == "HOL.eq" ||
      name == "HOL.implies" || name == "HOL.conj" || name == "HOL.disj" ||
      name == "HOL.All" || name == "HOL.Ex" || name == "HOL.Not" ||
      name == "HOL.True" || name == "HOL.False"


  /* ---- severity (wire-aligned with I/Q's DiagnosticsSeverity) ---- */

  sealed trait Severity { def wire: String }
  object Severity {
    case object Error extends Severity { val wire = "error" }
    case object Warning extends Severity { val wire = "warning" }
    def fromWire(s: String): Either[String, Severity] = s.trim match {
      case "error" => Right(Error)
      case "warning" => Right(Warning)
      case other => Left(s"severity must be 'error' or 'warning', got '$other'")
    }
  }

  private def severityFilter(severity: Severity): XML.Elem => Boolean = severity match {
    case Severity.Error => Protocol.is_error
    case Severity.Warning => elem => Protocol.is_warning(elem) || Protocol.is_legacy(elem)
  }


  /* ---- node resolution (session-generic; the candidate set is loaded nodes) ---- */

  /** All non-empty node paths the session currently has in its document graph
    * (loaded/checked theories + their import ancestors). For a file-less heap
    * theory (e.g. `Main`) the "path" is the theory name. */
  def nodePaths(session: Session): List[String] =
    session.snapshot().version.nodes.iterator.map(_._1.node).filter(_.nonEmpty).toList.distinct

  private def stripExt(path: String): String = {
    val dot = path.lastIndexOf('.')
    val slash = math.max(path.lastIndexOf('/'), path.lastIndexOf('\\'))
    if (dot > slash) path.substring(0, dot) else path
  }

  /** Resolve a (possibly partial) file argument to a loaded `Node.Name`.
    *
    * Matching mirrors I/Q's autoCompleteFilePath: case-insensitive,
    * extension-insensitive suffix match, requiring a UNIQUE hit. Unlike I/Q the
    * candidates are the session's loaded nodes, not jEdit's open buffers — so a
    * file must have been loaded/checked (or be an import) to resolve. As a
    * fallback an absolute path that matches a node by canonical file identity is
    * accepted (covers exact paths regardless of the suffix heuristic). */
  def resolveNode(session: Session, file: String): Either[String, Document.Node.Name] = {
    val snapshot = session.snapshot()
    val names = snapshot.version.nodes.iterator.map(_._1).filter(_.node.nonEmpty).toList
    val needle = stripExt(file).toLowerCase
    val matches = names.filter(n => stripExt(n.node).toLowerCase.endsWith(needle)).distinct
    matches match {
      case List(one) => Right(one)
      case Nil =>
        // Fallback: exact existing path, matched against node file identity.
        val f = new java.io.File(file)
        if (f.isFile)
          names.find(n => n.node.nonEmpty && File.eq(n.path.file, f)) match {
            case Some(n) => Right(n)
            case None => Left(s"File '$file' exists but is not a loaded session node " +
              "(check it first, or it is outside the session)")
          }
        else Left(s"No loaded theory matching '$file'")
      case many =>
        Left(s"Multiple loaded theories match '$file': " +
          many.map(_.node).sorted.mkString(", "))
    }
  }

  /** The node's source text, deferring to PIDE's own `Node.source`: the blob
    * text for an auxiliary/blob-backed node, otherwise the command spans
    * concatenated in order. Empty if the node is absent or has no commands (i.e.
    * not processed). This is the self-consistent text whose offsets index the
    * very commands queried below — `command_iterator` advances by
    * `command.length`, which is defined as `source.length`, so the span-concat
    * branch and the offset system agree by construction. (Using `Node.source`
    * rather than concatenating ourselves also returns the real text for a blob
    * node, where a bare span-concat would yield nothing.)
    *
    * NB this is the SNAPSHOT's text; it does not see a host editor's unsaved
    * buffer edits. A host that needs live-buffer semantics injects its own text
    * source rather than relying on this. */
  def nodeText(session: Session, name: Document.Node.Name): String = {
    val node = session.snapshot(node_name = name).get_node(name)
    if (node == null) "" else node.source
  }


  /* ---- command resolution (file + offset|pattern -> Command) ---- */

  /** Resolve a source location to the command spanning it. `offset` (clamped to
    * the node text) takes precedence; otherwise `pattern` is located as a unique
    * substring (Isabelle-symbol aware via IQNormalization) and the command at
    * the end of the match is returned. Session-generic — the same resolution
    * IRTools.initFromSourceLocation needs, now shared. */
  def resolveCommand(
    session: Session, file: String, offset: Option[Int], pattern: Option[String]
  ): Either[String, Command] =
    resolveNode(session, file).flatMap { name =>
      val content = nodeText(session, name)
      val charOffset: Either[String, Int] =
        offset match {
          case Some(o) =>
            Right(if (content.isEmpty) 0 else math.max(0, math.min(o, content.length - 1)))
          case None =>
            pattern.map(_.trim).filter(_.nonEmpty) match {
              case Some(pat) =>
                IQNormalization.findUniqueMatch(content, pat) match {
                  case Right((start, _)) => Right(start + pat.length - 1)
                  case Left(IQNormalization.SubstringNotFound) =>
                    Left(s"Pattern '$pat' not found in ${name.node}")
                  case Left(IQNormalization.SubstringNotUnique) =>
                    Left(s"Pattern '$pat' matches multiple locations in ${name.node}; use 'offset'")
                  case Left(IQNormalization.SubstringEmpty) => Left("Pattern cannot be empty")
                }
              case None => Left("specify either offset or pattern")
            }
        }
      charOffset.flatMap(commandAt(session, name, _))
    }

  /** The command spanning `offset` in node `name`, from the snapshot. */
  def commandAt(
    session: Session, name: Document.Node.Name, offset: Int
  ): Either[String, Command] = {
    val node = session.snapshot(node_name = name).get_node(name)
    if (node == null || node.commands.isEmpty)
      Left(s"Node not loaded or empty for ${name.node} (is it checked?)")
    else
      node.command_iterator(Text.Range(offset, offset + 1)).toList.headOption match {
        case Some((command, _)) => Right(command)
        case None => Left(s"No command found at offset $offset in ${name.node}")
      }
  }


  /* ============================ file-scope tools ============================ */

  /** list_files: the loaded nodes with per-node processing status. The headless
    * analogue of I/Q's list_files — reports the document graph, not editor
    * buffers (there are none). `filterTheory` keeps only theory / only
    * non-theory nodes. */
  def listFiles(session: Session, filterTheory: Option[Boolean]): Map[String, Any] = {
    val snapshot = session.snapshot()
    val now = Date.now()
    val files =
      snapshot.version.nodes.iterator.toList.map(_._1)
        .filter(_.node.nonEmpty)
        .filter(n => filterTheory.forall(_ == n.is_theory))
        .sortBy(_.node)
        .map { name =>
          val st = Document_Status.Node_Status.make(now, snapshot.state, snapshot.version, name)
          Map[String, Any](
            "theory" -> name.theory,
            "node" -> name.node,
            "is_theory" -> name.is_theory,
            "percentage" -> st.percentage,
            "finished" -> st.finished,
            "warned" -> st.warned,
            "failed" -> st.failed,
            "consolidated" -> st.consolidated)
        }
    Map("count" -> files.length, "files" -> files)
  }

  /** processing_status: PIDE processing counts for one node. */
  def processingStatus(session: Session, name: Document.Node.Name): Map[String, Any] = {
    val snapshot = session.snapshot(node_name = name)
    val st = Document_Status.Node_Status.make(Date.now(), snapshot.state, snapshot.version, name)
    Map(
      "path" -> name.node,
      "node_name" -> name.toString,
      "fully_processed" -> (st.terminated && st.unprocessed == 0 && st.running == 0),
      "unprocessed" -> st.unprocessed,
      "running" -> st.running,
      "finished" -> st.finished,
      "failed" -> st.failed,
      "has_errors" -> (st.failed > 0),
      "error_count" -> st.failed,
      "consolidated" -> st.consolidated)
  }

  /** Diagnostics (errors or warnings) within `range` of `name`, via PIDE
    * message markup. Lines computed from the supplied node text. */
  private def diagnosticsInRange(
    snapshot: Document.Snapshot, range: Text.Range, severity: Severity, lineDoc: Line.Document
  ): List[Map[String, Any]] =
    Rendering.text_messages(snapshot, range, severityFilter(severity))
      .flatMap { case Text.Info(messageRange, elem) =>
        val message = XML.content(elem).trim
        if (message.isEmpty) None
        else Some(Map[String, Any](
          "line" -> lineNumber(lineDoc, messageRange.start),
          "start_offset" -> messageRange.start,
          "end_offset" -> messageRange.stop,
          "message" -> message))
      }.distinct.toList

  /** get_diagnostics, file scope: all errors/warnings in the node. */
  def diagnostics(session: Session, name: Document.Node.Name, severity: Severity): Map[String, Any] = {
    val snapshot = session.snapshot(node_name = name)
    val content = nodeText(session, name)
    val diags = diagnosticsInRange(
      snapshot, Text.Range(0, math.max(content.length, 1)), severity, Line.Document(content))
    Map(
      "scope" -> "file",
      "severity" -> severity.wire,
      "path" -> name.node,
      "node_name" -> name.toString,
      "count" -> diags.length,
      "diagnostics" -> diags)
  }

  /** get_sorry_positions: sorry/oops commands with line + enclosing proof. */
  def sorryPositions(session: Session, name: Document.Node.Name): Map[String, Any] = {
    val snapshot = session.snapshot(node_name = name)
    val node = snapshot.get_node(name)
    val content = nodeText(session, name)
    val lineDoc = Line.Document(content)
    if (node == null || node.commands.isEmpty)
      Map("path" -> name.node, "count" -> 0, "positions" -> List.empty[Map[String, Any]])
    else {
      val commands = node.command_iterator().toList
      def enclosingProof(sorryIndex: Int): String =
        commands.take(sorryIndex).reverse.collectFirst {
          case (cmd, _) if ProofStarters.contains(cmd.span.name) =>
            EntityNamePattern.findFirstMatchIn(cmd.source.take(200))
              .map(_.group(1)).getOrElse(s"${cmd.span.name} (unnamed)")
        }.getOrElse("(unknown)")
      val positions = commands.zipWithIndex.collect {
        case ((cmd, offset), idx) if SorryKeywords.contains(cmd.span.name) =>
          Map[String, Any](
            "line" -> lineNumber(lineDoc, offset),
            "keyword" -> cmd.span.name,
            "offset" -> offset,
            "in_proof" -> enclosingProof(idx))
      }
      Map("path" -> name.node, "count" -> positions.length, "positions" -> positions)
    }
  }

  /** get_entities: declaration commands (lemma/definition/fun/...) with name,
    * keyword, line, offsets, and a source preview. */
  def entities(session: Session, name: Document.Node.Name, maxResults: Int): Map[String, Any] = {
    val snapshot = session.snapshot(node_name = name)
    val node = snapshot.get_node(name)
    val content = nodeText(session, name)
    val lineDoc = Line.Document(content)
    if (node == null)
      Map("path" -> name.node, "node_name" -> name.toString, "total_entities" -> 0,
        "returned_entities" -> 0, "truncated" -> false, "entities" -> List.empty[Map[String, Any]])
    else {
      val all = node.command_iterator().toList.collect {
        case (cmd, cmdOffset) if EntityKeywords.contains(cmd.span.name) =>
          val nm = EntityNamePattern.findFirstMatchIn(cmd.source.take(300))
            .map(_.group(1)).getOrElse("(unnamed)")
          Map[String, Any](
            "line" -> lineNumber(lineDoc, cmdOffset),
            "keyword" -> cmd.span.name,
            "name" -> nm,
            "start_offset" -> cmdOffset,
            "end_offset" -> (cmdOffset + cmd.length),
            "source_preview" -> cmd.source.take(160).trim)
      }
      val shown = all.take(maxResults)
      Map(
        "path" -> name.node,
        "node_name" -> name.toString,
        "total_entities" -> all.length,
        "returned_entities" -> shown.length,
        "truncated" -> (all.length > shown.length),
        "entities" -> shown)
    }
  }

  /** get_proof_blocks, file scope: every proof block in the node (>= minChars). */
  def proofBlocks(session: Session, name: Document.Node.Name, minChars: Int): Map[String, Any] = {
    val snapshot = session.snapshot(node_name = name)
    val node = snapshot.get_node(name)
    val content = nodeText(session, name)
    if (node == null)
      Map("path" -> name.node, "scope" -> "file", "count" -> 0,
        "blocks" -> List.empty[Map[String, Any]])
    else {
      val commands = node.command_iterator().toList
      val blocks = extractProofBlocks(commands, Some(Line.Document(content)), minChars)
      Map("path" -> name.node, "scope" -> "file", "count" -> blocks.length, "blocks" -> blocks)
    }
  }

  /** document_info: whole-theory error/warning counts + per-command summary. */
  def documentInfo(session: Session, name: Document.Node.Name): Map[String, Any] = {
    val snapshot = session.snapshot(node_name = name)
    val state = snapshot.state
    val version = snapshot.version
    val node = snapshot.get_node(name)
    var failed = 0; var finished = 0; var unprocessed = 0; var total = 0
    var anyTerminated = true; var canceled = false
    val it = if (node == null) Iterator.empty else node.commands.iterator
    for (command <- it if command.source.trim.nonEmpty) {
      val cs = state.command_status(version, command)
      total += 1
      if (cs.is_failed) failed += 1
      else if (cs.is_running || cs.is_unprocessed) unprocessed += 1
      else if (cs.is_finished || cs.is_warned) finished += 1
      else unprocessed += 1
      if (cs.is_canceled) canceled = true
      if (!cs.is_terminated) anyTerminated = false
    }
    val errors = diagnostics(session, name, Severity.Error)("count").asInstanceOf[Int]
    val warnings = diagnostics(session, name, Severity.Warning)("count").asInstanceOf[Int]
    Map(
      "path" -> name.node,
      "node_name" -> name.toString,
      "total_commands" -> total,
      "finished" -> finished,
      "unprocessed" -> unprocessed,
      "failed" -> failed,
      "canceled" -> canceled,
      "fully_processed" -> (anyTerminated && unprocessed == 0),
      "error_count" -> errors,
      "warning_count" -> warnings,
      "has_errors" -> (errors > 0))
  }


  /* ========================= command-scope tools ========================= */

  /** Command metadata: id, keyword, type, source, range. */
  def commandInfo(session: Session, command: Command): Map[String, Any] = {
    val base = Map[String, Any](
      "id" -> command.id,
      "length" -> command.length,
      "keyword" -> command.span.name,
      "command_type" -> determineCommandType(command.source),
      "source" -> command.source)
    commandRange(session, command) match {
      case Some((nodePath, start, stop)) =>
        base ++ Map("node_path" -> nodePath, "start_offset" -> start, "end_offset" -> stop)
      case None => base
    }
  }

  /** Status (summary + timing seconds) of a command in the snapshot. */
  def commandStatus(session: Session, command: Command): Map[String, Any] = {
    val snapshot = session.snapshot(node_name = command.node_name)
    val states = snapshot.state.command_states(snapshot.version, command)
    val status = Document_Status.Command_Status.merge(states.iterator.map(_.document_status))
    val timing = status.timings.sum(Date.now()).seconds
    val summary =
      if (status.is_failed) "failed"
      else if (status.is_canceled) "canceled"
      else if (status.is_running) "running"
      else if (status.is_finished) "finished"
      else if (status.is_terminated) "finished"
      else if (status.is_unprocessed) "unprocessed"
      else if (status.runs > 0 || status.forks > 0) "finished"
      else "unknown"
    Map("summary" -> summary, "timing_seconds" -> timing)
  }

  /** The positioned output messages (errors, warnings, writeln, ...) attached to
    * a command, collected over its text range via Rendering.text_messages — the
    * same path the diagnostics tools use, which walks markup keyed to source
    * offsets. NOTE this deliberately does NOT surface the proof STATE message: a
    * proof state carries no source position, so the range walk never sees it.
    * Goal text is therefore read separately in `goalState`, from
    * snapshot.command_results(command) filtered by Protocol.is_state. */
  private def commandMessages(session: Session, command: Command): List[XML.Elem] = {
    val snapshot = session.snapshot(node_name = command.node_name)
    val start = commandStart(session, command)
    val range = Text.Range(start, start + command.length)
    Rendering.text_messages(snapshot, range).map(_.info)
  }

  /** get_command_info-style payload at a resolved command: metadata + status +
    * the command's output text (errors/warnings/writeln). This is NOT the proof
    * goal state — that has no positioned markup and so never appears here; use
    * `goalState` / get_context_info for goal text. */
  def commandReport(session: Session, command: Command): Map[String, Any] = {
    val resultsText = commandMessages(session, command)
      .map(e => XML.content(e).trim).filter(_.nonEmpty).distinct.mkString("\n\n")
    commandInfo(session, command) ++ Map(
      "status" -> commandStatus(session, command),
      "results_text" -> resultsText)
  }

  /** get_diagnostics, selection scope: errors/warnings within the command. */
  def diagnosticsAtCommand(session: Session, command: Command, severity: Severity): Map[String, Any] = {
    val snapshot = session.snapshot(node_name = command.node_name)
    val content = nodeText(session, command.node_name)
    val start = commandStart(session, command)
    val range = Text.Range(start, start + command.length)
    val diags = diagnosticsInRange(snapshot, range, severity, Line.Document(content))
    Map(
      "scope" -> "selection",
      "severity" -> severity.wire,
      "node_path" -> command.node_name.node,
      "count" -> diags.length,
      "diagnostics" -> diags)
  }

  /** True iff the command sits inside an open proof, via a keyword balance over
    * the spans from the node start up to (and including) the command. */
  def inProofContext(session: Session, command: Command): Boolean = {
    val snapshot = session.snapshot(node_name = command.node_name)
    val node = snapshot.get_node(command.node_name)
    if (node == null || node.commands.isEmpty) false
    else {
      val start = node.command_start(command).getOrElse(0)
      val keywords =
        node.command_iterator(Text.Range(0, math.max(0, start + 1))).toList.map(_._1.span.name)
      var depth = 0
      val iter = keywords.reverseIterator
      while (iter.hasNext) {
        val kw = iter.next()
        if (ContextProofClosers.contains(kw)) depth += 1
        else if (ContextProofOpeners.contains(kw)) {
          if (depth > 0) depth -= 1 else return true
        }
      }
      false
    }
  }

  /** get_context_info: command metadata + proof-context flag + goal state. */
  def contextInfo(session: Session, command: Command): Map[String, Any] = {
    val goal = goalState(session, command)
    Map(
      "command" -> commandInfo(session, command),
      "in_proof_context" -> inProofContext(session, command),
      "has_goal" -> goal.get("has_goal").contains(true),
      "goal" -> goal)
  }

  /** Goal state at a command: text, subgoal count, free vars, constants —
    * parsed from the command's proof-STATE messages. Headless analogue of
    * I/Q's PIDE.editor.output, reconstructed from the command's results +
    * Protocol.is_state partition.
    *
    * `has_goal` is keyed on the presence of a STATE message (the prover's proof
    * state, gated by editor_output_state, which the daemon turns on), NOT on
    * "any output". A non-goal command (e.g. `definition`, `datatype`) emits
    * writeln/other output but no STATE message, so it correctly reports
    * has_goal:false — folding that incidental output in used to mislabel such
    * commands has_goal:true with the output text as a bogus "goal".
    *
    * The STATE message must be read from the command's RESULTS map
    * (`snapshot.command_results`), NOT from the range-based `text_messages`
    * path: a proof state is a command result with no positioned marker in the
    * source text, so the range walk never surfaces it (this is why context/
    * command-info used to report has_goal:false everywhere). This mirrors the
    * reference `Editor.output`, which likewise partitions STATE out of
    * `snapshot.command_results(command)`. `command_results` is itself robust to
    * version identity: `command_states_self` falls back to the static state and
    * finally `command.init_state` when the assigned execs aren't found. */
  def goalState(session: Session, command: Command): Map[String, Any] = {
    val empty = Map[String, Any](
      "has_goal" -> false, "goal_text" -> "", "num_subgoals" -> 0,
      "free_vars" -> List.empty[String], "constants" -> List.empty[String])
    try {
      val snapshot = session.snapshot(node_name = command.node_name)
      val states =
        (for {
          (_, msg) <- snapshot.command_results(command).iterator
          if !Protocol.is_result(msg) && Protocol.is_state(msg)
        } yield msg).toList
      if (states.isEmpty) empty else analyzeGoalMessages(states)
    } catch { case ex: Throwable => empty + ("analysis_error" -> ex.getMessage) }
  }


  /* ---- shared helpers ---- */

  private def lineNumber(lineDoc: Line.Document, offset: Int): Int =
    scala.util.Try(lineDoc.position(offset).line + 1).toOption.getOrElse(0)

  private def commandStart(session: Session, command: Command): Int = {
    val node = session.snapshot(node_name = command.node_name).get_node(command.node_name)
    if (node == null) 0 else node.command_start(command).getOrElse(0)
  }

  private def commandRange(session: Session, command: Command): Option[(String, Int, Int)] = {
    val node = session.snapshot(node_name = command.node_name).get_node(command.node_name)
    if (node == null) None
    else node.command_start(command).map(start => (command.node_name.node, start, start + command.length))
  }

  private def determineCommandType(source: String): String = {
    val t = source.trim
    if (t.startsWith("lemma ") || t.startsWith("theorem ") ||
        t.startsWith("corollary ") || t.startsWith("proposition ")) "statement"
    else if (t.startsWith("proof") || t == "proof") "proof_start"
    else if (t.startsWith("apply ")) "proof_method"
    else if (t.startsWith("by ")) "proof_method"
    else if (t == "qed" || t.startsWith("qed ")) "proof_end"
    else if (t.startsWith("definition ") || t.startsWith("fun ") || t.startsWith("primrec ")) "definition"
    else if (t.startsWith("datatype ") || t.startsWith("type_synonym ")) "type_definition"
    else if (t.startsWith("import ") || t.startsWith("theory ")) "theory_structure"
    else if (t.startsWith("declare ") || t.startsWith("notation ")) "declaration"
    else "other"
  }

  private def analyzeGoalMessages(messages: List[XML.Tree]): Map[String, Any] = {
    val text = messages.map(elem => XML.content(elem).trim).filter(_.nonEmpty).mkString("\n\n")
    if (text.isEmpty)
      Map("has_goal" -> false, "goal_text" -> "", "num_subgoals" -> 0,
        "free_vars" -> List.empty[String], "constants" -> List.empty[String])
    else {
      val freeVars = scala.collection.mutable.LinkedHashSet[String]()
      val constants = scala.collection.mutable.LinkedHashSet[String]()
      var numSubgoals = 0
      def walk(tree: XML.Tree): Unit = tree match {
        case XML.Elem(Markup(Markup.FREE, props), body) =>
          Markup.Name.unapply(props).foreach(freeVars.add); body.foreach(walk)
        case XML.Elem(Markup("fixed", props), body) =>
          Markup.Name.unapply(props).foreach(freeVars.add); body.foreach(walk)
        case XML.Elem(Markup(Markup.CONSTANT, props), body) =>
          Markup.Name.unapply(props).foreach(n => if (!isMetaConstant(n)) { val _ = constants.add(n) })
          body.foreach(walk)
        case XML.Elem(Markup("subgoal", _), body) => numSubgoals += 1; body.foreach(walk)
        case XML.Elem(_, body) => body.foreach(walk)
        case XML.Text(_) =>
      }
      messages.foreach(walk)
      Map(
        "has_goal" -> true,
        "goal_text" -> text,
        "num_subgoals" -> math.max(numSubgoals, 1),
        "free_vars" -> freeVars.toList,
        "constants" -> constants.toList)
    }
  }

  private def extractProofBlocks(
    commands: List[(Command, Int)], lineDoc: Option[Line.Document], minChars: Int
  ): List[Map[String, Any]] = {
    val blocks = scala.collection.mutable.ListBuffer.empty[Map[String, Any]]
    var i = 0
    while (i < commands.length) {
      if (ProofBlockStarters.contains(commands(i)._1.span.name)) {
        extractProofBlockAt(commands, i, lineDoc) match {
          case Some(block) =>
            val proofText = block.get("proof_text").map(_.toString).getOrElse("")
            if (proofText.length >= minChars) blocks += block
            val consumed = block.get("command_count").collect {
              case v: Int => v; case v: Long => v.toInt }.getOrElse(1)
            i += math.max(1, consumed)
          case None => i += 1
        }
      } else i += 1
    }
    blocks.toList
  }

  private def extractProofBlockAt(
    commands: List[(Command, Int)], anchorIndex: Int, lineDoc: Option[Line.Document]
  ): Option[Map[String, Any]] = {
    if (anchorIndex < 0 || anchorIndex >= commands.length) None
    else {
      var startIndex = -1; var i = anchorIndex
      while (i >= 0 && startIndex < 0) {
        if (ProofBlockStarters.contains(commands(i)._1.span.name)) startIndex = i
        i -= 1
      }
      if (startIndex < 0) None
      else {
        val parts = scala.collection.mutable.ListBuffer.empty[String]
        var depth = 0; var j = startIndex; var foundEnd = false
        while (j < commands.length && !foundEnd) {
          val (cmd, _) = commands(j)
          val kw = cmd.span.name
          parts += cmd.source
          if (kw == "proof") depth += 1
          if (kw == "by" && depth == 0) foundEnd = true
          else if (ProofBlockStructuralEnders.contains(kw)) {
            if (depth <= 1) foundEnd = true else depth -= 1
          }
          j += 1
        }
        if (!foundEnd) None
        else {
          val endIndex = j - 1
          val startOffset = commands(startIndex)._2
          val endOffset = commands(endIndex)._2 + commands(endIndex)._1.length
          val proofText = parts.mkString("\n")
          Some(Map[String, Any](
            "proof_text" -> proofText,
            "start_offset" -> startOffset,
            "end_offset" -> endOffset,
            "start_line" -> lineDoc.map(d => lineNumber(d, startOffset)).getOrElse(0),
            "end_line" -> lineDoc.map(d => lineNumber(d, endOffset)).getOrElse(0),
            "command_count" -> (endIndex - startIndex + 1),
            "is_apply_style" -> proofText.linesIterator.exists(_.trim.startsWith("apply"))))
        }
      }
    }
  }


  /* ============================ shared dispatch ============================ *
   * One name->analysis table over the typed functions above, so every surface
   * that exposes these tools (the MCP SessionClient and the ic2 `query` wire op
   * + CLI) routes through the SAME mapping and can't drift. Each entry takes a
   * normalized param map (string keys; values Long/Double/Boolean/String as the
   * JSON layer produces) and returns the result map or a Left error string. */

  /** The catalogue: tool name in wire order, paired with a one-line summary.
    * The summary is advisory (CLI help); the MCP descriptions live in
    * SessionClient and stay the canonical, fuller text. */
  val queryTools: List[(String, String)] = List(
    "list_files" -> "loaded theory nodes + each node's processing status",
    "get_processing_status" -> "PIDE processing-status counts for a theory",
    "get_document_info" -> "whole-theory command/error/warning totals",
    "get_diagnostics" -> "errors or warnings (file or selection scope)",
    "get_sorry_positions" -> "sorry/oops positions with enclosing proof",
    "get_entities" -> "declared entities (lemma/definition/fun/...)",
    "get_proof_blocks" -> "proof blocks with text and line ranges",
    "get_command_info" -> "command metadata/status/result at a selection",
    "get_context_info" -> "proof-context + goal state at a selection")

  val queryToolNames: List[String] = queryTools.map(_._1)

  /* param extractors over the normalized map (shared by every caller). */
  private def reqStr(p: Map[String, Any], key: String): Either[String, String] =
    p.get(key) match {
      case Some(s: String) if s.trim.nonEmpty => Right(s.trim)
      case _ => Left(s"Missing required parameter: $key")
    }
  private def optInt(p: Map[String, Any], key: String): Option[Int] =
    p.get(key) match {
      case Some(n: Long) => Some(n.toInt)
      case Some(n: Int) => Some(n)
      case Some(n: Double) => Some(n.toInt)
      case _ => None
    }
  private def optBool(p: Map[String, Any], key: String): Option[Boolean] =
    p.get(key) match { case Some(b: Boolean) => Some(b); case _ => None }
  private def optStr(p: Map[String, Any], key: String): Option[String] =
    p.get(key).collect { case s: String if s.trim.nonEmpty => s.trim }
  private def severityOf(p: Map[String, Any]): Either[String, Severity] =
    Severity.fromWire(p.get("severity").map(_.toString).getOrElse("error"))

  private def withNode(session: Session, p: Map[String, Any])(
    f: Document.Node.Name => Map[String, Any]
  ): Either[String, Map[String, Any]] =
    reqStr(p, "path").flatMap(resolveNode(session, _)).map(f)

  private def withCommand(session: Session, p: Map[String, Any])(
    f: Command => Map[String, Any]
  ): Either[String, Map[String, Any]] =
    reqStr(p, "path")
      .flatMap(resolveCommand(session, _, optInt(p, "offset"), optStr(p, "pattern")))
      .map(f)

  /** Run a query tool by name over `params`. The single dispatch shared by the
    * MCP SessionClient and the wire `query` op. Left on unknown tool, bad
    * params, or a resolution error. */
  def dispatch(
    session: Session, tool: String, params: Map[String, Any]
  ): Either[String, Map[String, Any]] =
    tool match {
      case "list_files" =>
        Right(listFiles(session, optBool(params, "filter_theory")))
      case "get_processing_status" =>
        withNode(session, params)(processingStatus(session, _))
      case "get_document_info" =>
        withNode(session, params)(documentInfo(session, _))
      case "get_diagnostics" =>
        severityOf(params).flatMap { sev =>
          optStr(params, "scope").getOrElse("file") match {
            case "file" => withNode(session, params)(diagnostics(session, _, sev))
            case "selection" => withCommand(session, params)(diagnosticsAtCommand(session, _, sev))
            case other => Left(s"scope must be 'file' or 'selection', got '$other'")
          }
        }
      case "get_sorry_positions" =>
        withNode(session, params)(sorryPositions(session, _))
      case "get_entities" =>
        val max = optInt(params, "max_results").filter(_ > 0).getOrElse(500)
        withNode(session, params)(entities(session, _, max))
      case "get_proof_blocks" =>
        val min = optInt(params, "min_chars").getOrElse(0)
        withNode(session, params)(proofBlocks(session, _, min))
      case "get_command_info" =>
        withCommand(session, params)(commandReport(session, _))
      case "get_context_info" =>
        withCommand(session, params)(contextInfo(session, _))
      case other =>
        Left("unknown query tool: " + other +
          " (known: " + queryToolNames.mkString(", ") + ")")
    }
}
