/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle.JSON

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

object IQProtocol {
  final case class JsonRpcRequest(
    method: String,
    id: Option[Any],
    params: Map[String, JSON.T],
    raw: Map[String, JSON.T]
  )

  final case class ToolCall(
    toolName: IQToolName,
    arguments: Map[String, JSON.T]
  )

  private def validRequestId(value: JSON.T): Boolean = {
    value match {
      case _: String => true
      case _: Int => true
      case _: Long => true
      case _: Double => true
      case _: Float => true
      case _: BigInt => true
      case _: BigDecimal => true
      case _: java.lang.Integer => true
      case _: java.lang.Long => true
      case _: java.lang.Double => true
      case _: java.lang.Float => true
      case null => true
      case _ => false
    }
  }

  def decodeJsonRpcRequest(json: JSON.T): Either[String, JsonRpcRequest] = {
    json match {
      case JSON.Object(obj) =>
        val method = obj.get("method") match {
          case Some(name: String) if name.trim.nonEmpty => name.trim
          case Some(_: String) => return Left("Invalid request: 'method' must be non-empty")
          case Some(_) => return Left("Invalid request: 'method' must be a string")
          case None => return Left("Invalid request: missing 'method'")
        }

        val id = obj.get("id") match {
          case Some(value) if validRequestId(value) => Some(value)
          case Some(_) => return Left("Invalid request: 'id' must be string, number, or null")
          case None => None
        }

        val params = obj.get("params") match {
          case Some(JSON.Object(p)) => p
          case Some(_) => return Left("Invalid request: 'params' must be an object")
          case None => Map.empty[String, JSON.T]
        }

        Right(JsonRpcRequest(method = method, id = id, params = params, raw = obj))

      case _ =>
        Left("Invalid request: payload must be a JSON object")
    }
  }

  private def extractTokenValue(value: JSON.T): Option[String] =
    value match {
      case token: String => Option(token.trim).filter(_.nonEmpty)
      case _ => None
    }

  def extractAuthToken(request: JsonRpcRequest): Option[String] = {
    request.raw
      .get("auth_token")
      .flatMap(extractTokenValue)
      .orElse(request.params.get("auth_token").flatMap(extractTokenValue))
  }

  def decodeToolCall(request: JsonRpcRequest): Either[String, ToolCall] = {
    val toolNameRaw = request.params.get("name") match {
      case Some(name: String) if name.trim.nonEmpty => name.trim
      case Some(_: String) =>
        return Left("Invalid params: tool 'name' must be non-empty")
      case Some(_) =>
        return Left("Invalid params: tool 'name' must be a string")
      case None =>
        return Left("Invalid params: missing required field 'name'")
    }

    val toolName = IQToolName.fromWire(toolNameRaw) match {
      case Right(value) => value
      case Left(raw) => return Left(s"Unknown tool: $raw")
    }

    val arguments = request.params.get("arguments") match {
      case Some(JSON.Object(args)) => args
      case Some(_) =>
        return Left("Invalid params: tool 'arguments' must be an object")
      case None => Map.empty[String, JSON.T]
    }

    Right(ToolCall(toolName = toolName, arguments = arguments))
  }
}
