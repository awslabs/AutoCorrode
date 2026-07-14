/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

enum CommandSelectionTarget(val wire: String) {
  case Current extends CommandSelectionTarget("current")
  case FileOffset extends CommandSelectionTarget("file_offset")
  case FilePattern extends CommandSelectionTarget("file_pattern")
}

object CommandSelectionTarget {
  private val byWire: Map[String, CommandSelectionTarget] =
    CommandSelectionTarget.values.map(value => value.wire -> value).toMap

  def fromWire(raw: String): Either[String, CommandSelectionTarget] =
    byWire.get(raw.trim.toLowerCase(java.util.Locale.ROOT)) match {
      case Some(value) => Right(value)
      case None => Left(raw)
    }
}

enum GetCommandMode(val wire: String) {
  case Current extends GetCommandMode("current")
  case Line extends GetCommandMode("line")
  case Offset extends GetCommandMode("offset")
}

object GetCommandMode {
  private val byWire: Map[String, GetCommandMode] =
    GetCommandMode.values.map(value => value.wire -> value).toMap

  def fromWire(raw: String): Either[String, GetCommandMode] =
    byWire.get(raw.trim.toLowerCase(java.util.Locale.ROOT)) match {
      case Some(value) => Right(value)
      case None => Left(raw)
    }
}

enum ReadFileMode(val wire: String) {
  case Line extends ReadFileMode("Line")
  case Search extends ReadFileMode("Search")
}

object ReadFileMode {
  private val byWire: Map[String, ReadFileMode] =
    ReadFileMode.values.map(value => value.wire -> value).toMap

  def fromWire(raw: String): Either[String, ReadFileMode] =
    byWire.get(raw.trim) match {
      case Some(value) => Right(value)
      case None => Left(raw)
    }
}

enum ExploreQuery(val wire: String, val internalName: String) {
  case Proof extends ExploreQuery("proof", "isar_explore")
  case Sledgehammer extends ExploreQuery("sledgehammer", "sledgehammer")
  case FindTheorems extends ExploreQuery("find_theorems", "find_theorems")
  // print_state is a core Isabelle query print function (Pure/PIDE/query_operation.ML),
  // always available — no Isar_Explore.thy import needed. Takes no arguments.
  case State extends ExploreQuery("state", "print_state")
}

object ExploreQuery {
  private val byWire: Map[String, ExploreQuery] =
    ExploreQuery.values.map(value => value.wire -> value).toMap

  def fromWire(raw: String): Either[String, ExploreQuery] =
    byWire.get(raw.trim.toLowerCase(java.util.Locale.ROOT)) match {
      case Some(value) => Right(value)
      case None => Left(raw)
    }
}

enum ProofBlocksScope(val wire: String) {
  case Selection extends ProofBlocksScope("selection")
  case File extends ProofBlocksScope("file")
}

object ProofBlocksScope {
  private val byWire: Map[String, ProofBlocksScope] =
    ProofBlocksScope.values.map(value => value.wire -> value).toMap

  def fromWire(raw: String): Either[String, ProofBlocksScope] =
    byWire.get(raw.trim.toLowerCase(java.util.Locale.ROOT)) match {
      case Some(value) => Right(value)
      case None => Left(raw)
    }
}

enum DiagnosticsSeverity(val wire: String) {
  case Error extends DiagnosticsSeverity("error")
  case Warning extends DiagnosticsSeverity("warning")
}

object DiagnosticsSeverity {
  private val byWire: Map[String, DiagnosticsSeverity] =
    DiagnosticsSeverity.values.map(value => value.wire -> value).toMap

  def fromWire(raw: String): Either[String, DiagnosticsSeverity] =
    byWire.get(raw.trim.toLowerCase(java.util.Locale.ROOT)) match {
      case Some(value) => Right(value)
      case None => Left(raw)
    }
}

enum DiagnosticsScope(val wire: String) {
  case Selection extends DiagnosticsScope("selection")
  case File extends DiagnosticsScope("file")
}

object DiagnosticsScope {
  private val byWire: Map[String, DiagnosticsScope] =
    DiagnosticsScope.values.map(value => value.wire -> value).toMap

  def fromWire(raw: String): Either[String, DiagnosticsScope] =
    byWire.get(raw.trim.toLowerCase(java.util.Locale.ROOT)) match {
      case Some(value) => Right(value)
      case None => Left(raw)
    }
}

/**
 * write_file's check_context_scope parameter. Controls how widely the
 * wait/recheck window extends around the inserted text. The 'commands'
 * array stays scoped to the inserted text in every case; the scope only
 * widens what we wait on and what gets reflected in file_summary timing.
 *
 * - Command: just the inserted text.
 * - Block:   the innermost enclosing 'proof ... qed' (the current proof
 *            layer). If the edit isn't inside any 'proof' keyword (e.g. a
 *            bare 'lemma … by …', or a lemma statement before its proof
 *            block), falls back to the surrounding lemma/theorem block and
 *            is reported as Proof.
 * - Proof:   the OUTERMOST enclosing 'proof ... qed' (the entire proof of
 *            the enclosing lemma). For an edit inside a non-nested proof,
 *            Block and Proof coincide; inside a nested proof, Proof is
 *            strictly wider than Block. For edits outside any 'proof' it is
 *            the surrounding lemma/theorem block (same fallback as Block).
 * - File:    the whole theory.
 */
enum CheckContextScope(val wire: String) {
  case Command extends CheckContextScope("command")
  case Block   extends CheckContextScope("block")
  case Proof   extends CheckContextScope("proof")
  case File    extends CheckContextScope("file")
}

object CheckContextScope {
  private val byWire: Map[String, CheckContextScope] =
    CheckContextScope.values.map(value => value.wire -> value).toMap

  def fromWire(raw: String): Either[String, CheckContextScope] =
    byWire.get(raw.trim.toLowerCase(java.util.Locale.ROOT)) match {
      case Some(value) => Right(value)
      case None => Left(raw)
    }
}

/* The IQ-specific selection/scope enums above are consumed by the IQ tool
   handlers. JSON-RPC request/tool-call decoding lives in McpProtocol. */
