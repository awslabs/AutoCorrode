/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/** Decoder functions for I/Q MCP protocol responses.
  *
  * Converts JSON payloads (as Map[String, Any] from Isabelle JSON.parse)
  * into typed protocol result objects. Internal to IQMcpClient.
  */
private[assistant] object IQMcpDecoder {
  import IQMcpProtocol._

  // --- Type coercion helpers ---
  // These are package-private so they can be reused by IQMcpClient

  private[assistant] def asObject(value: Any): Option[Map[String, Any]] = value match {
    case JSON.Object(obj) => Some(obj)
    case obj: Map[?, ?] =>
      Some(obj.collect { case (k: String, v) => k -> v }.toMap)
    case _ => None
  }

  private[assistant] def asList(value: Any): Option[List[Any]] = value match {
    case xs: List[?] => Some(xs.asInstanceOf[List[Any]])
    case _ => None
  }

  private def asInt(value: Any): Option[Int] = value match {
    case i: Int => Some(i)
    case l: Long if l.isValidInt => Some(l.toInt)
    case d: Double if d.isWhole && d.isValidInt => Some(d.toInt)
    case s: String => scala.util.Try(s.trim.toInt).toOption
    case _ => None
  }

  private def asLong(value: Any): Option[Long] = value match {
    case i: Int => Some(i.toLong)
    case l: Long => Some(l)
    case d: Double if d.isWhole => Some(d.toLong)
    case s: String => scala.util.Try(s.trim.toLong).toOption
    case _ => None
  }

  private def asStringList(value: Any): List[String] = value match {
    case xs: List[?] =>
      xs.collect { case v if v != null => v.toString.trim }.filter(_.nonEmpty)
    case _ => List.empty
  }

  // --- Field extractors ---
  //
  // Each extractor takes a payload and a key. If the key is absent the
  // `default` is returned silently (absent optional fields are normal). If
  // the key is present but the value has an unexpected type, the default is
  // still returned, but a warning is logged to the Isabelle output so the
  // mismatch is diagnosable from the jEdit log. That keeps the Assistant
  // resilient to server version drift while making shape violations loud.

  private def logShapeMismatch(
      key: String,
      expected: String,
      value: Any
  ): Unit = {
    val actual = if (value == null) "null" else value.getClass.getSimpleName
    // Truncate the rendered value for logging so a pathological payload can
    // not flood the Isabelle output panel.
    val rendered = {
      val s = String.valueOf(value)
      if (s.length > 120) s.take(120) + "…" else s
    }
    Output.warning(
      s"[Assistant] I/Q MCP: field '$key' expected $expected, got $actual ($rendered)"
    )
  }

  def boolField(payload: Map[String, Any], key: String, default: Boolean): Boolean =
    payload.get(key) match {
      case None => default
      case Some(value: Boolean) => value
      case Some(value: String) =>
        value.trim.toLowerCase match {
          case "true" => true
          case "false" => false
          case _ =>
            logShapeMismatch(key, "boolean", value)
            default
        }
      case Some(value: Int) => value != 0
      case Some(value: Long) => value != 0L
      case Some(value: Double) => value != 0.0
      case Some(other) =>
        logShapeMismatch(key, "boolean", other)
        default
    }

  def stringField(payload: Map[String, Any], key: String): String =
    payload.get(key) match {
      case None => ""
      case Some(value: String) => value
      // Numbers and booleans render fine via toString; objects and arrays
      // almost certainly indicate a schema mismatch.
      case Some(value: Boolean) => value.toString
      case Some(value: Int) => value.toString
      case Some(value: Long) => value.toString
      case Some(value: Double) => value.toString
      case Some(other) =>
        logShapeMismatch(key, "string", other)
        other.toString
    }

  def intField(
      payload: Map[String, Any],
      key: String,
      default: Int
  ): Int = payload.get(key) match {
    case None => default
    case Some(value) =>
      asInt(value).getOrElse {
        logShapeMismatch(key, "integer", value)
        default
      }
  }

  def longField(
      payload: Map[String, Any],
      key: String,
      default: Long
  ): Long = payload.get(key) match {
    case None => default
    case Some(value) =>
      asLong(value).getOrElse {
        logShapeMismatch(key, "long", value)
        default
      }
  }

  def mapField(payload: Map[String, Any], key: String): Map[String, Any] =
    payload.get(key) match {
      case None => Map.empty
      case Some(value) =>
        asObject(value).getOrElse {
          logShapeMismatch(key, "object", value)
          Map.empty
        }
    }

  def listField(payload: Map[String, Any], key: String): List[Any] =
    payload.get(key) match {
      case None => List.empty
      case Some(value) =>
        asList(value).getOrElse {
          logShapeMismatch(key, "array", value)
          List.empty
        }
    }

  // --- Decode functions ---

  def decodeExploreResult(payload: Map[String, Any]): ExploreResult = {
    ExploreResult(
      success = boolField(payload, "success", default = false),
      results = stringField(payload, "results"),
      message = stringField(payload, "message"),
      timedOut = boolField(payload, "timed_out", default = false),
      error = payload.get("error").map(_.toString).filter(_.nonEmpty)
    )
  }

  private def decodeSelection(payload: Map[String, Any]): CommandSelection = {
    val selectionType =
      payload.get("command_selection").map(_.toString.trim).getOrElse("")
    selectionType match {
      case "current" =>
        CurrentSelection
      case "file_offset" =>
        FileOffsetSelection(
          path = stringField(payload, "path"),
          requestedOffset = payload.get("requested_offset").flatMap(asInt),
          normalizedOffset = payload.get("normalized_offset").flatMap(asInt)
        )
      case "file_pattern" =>
        FilePatternSelection(
          path = stringField(payload, "path"),
          pattern = stringField(payload, "pattern")
        )
      case other =>
        UnknownSelection(other)
    }
  }

  private def decodeCommandInfo(payload: Map[String, Any]): CommandInfo =
    CommandInfo(
      id = longField(payload, "id", 0L),
      length = intField(payload, "length", 0),
      source = stringField(payload, "source"),
      keyword = stringField(payload, "keyword"),
      nodePath = payload
        .get("node_path")
        .map(_.toString.trim)
        .filter(_.nonEmpty),
      startOffset = payload.get("start_offset").flatMap(asInt),
      endOffset = payload.get("end_offset").flatMap(asInt)
    )

  private def decodeGoalInfo(payload: Map[String, Any]): GoalInfo =
    GoalInfo(
      hasGoal = boolField(payload, "has_goal", default = false),
      goalText = stringField(payload, "goal_text"),
      numSubgoals = intField(payload, "num_subgoals", default = 0),
      freeVars = payload.get("free_vars").map(asStringList).getOrElse(List.empty),
      constants = payload.get("constants").map(asStringList).getOrElse(List.empty),
      analysisError = payload
        .get("analysis_error")
        .map(_.toString.trim)
        .filter(_.nonEmpty)
    )

  private def decodeDiagnosticSeverity(raw: String): DiagnosticSeverity =
    raw.trim.toLowerCase match {
      case "warning" => DiagnosticSeverity.Warning
      case _ => DiagnosticSeverity.Error
    }

  private def decodeDiagnosticScope(raw: String): DiagnosticScope =
    raw.trim.toLowerCase match {
      case "file" => DiagnosticScope.File
      case _ => DiagnosticScope.Selection
    }

  private def decodeProofBlocksScope(raw: String): ProofBlocksScope =
    raw.trim.toLowerCase match {
      case "file" => ProofBlocksScope.File
      case _ => ProofBlocksScope.Selection
    }

  def decodeResolvedCommandTarget(
      payload: Map[String, Any]
  ): ResolvedCommandTarget =
    ResolvedCommandTarget(
      selection = decodeSelection(mapField(payload, "selection")),
      command = decodeCommandInfo(mapField(payload, "command"))
    )

  def decodeContextInfoResult(
      payload: Map[String, Any]
  ): ContextInfoResult =
    ContextInfoResult(
      selection = decodeSelection(mapField(payload, "selection")),
      command = decodeCommandInfo(mapField(payload, "command")),
      inProofContext = boolField(payload, "in_proof_context", default = false),
      hasGoal = boolField(payload, "has_goal", default = false),
      goal = decodeGoalInfo(mapField(payload, "goal"))
    )

  def decodeEntitiesResult(
      payload: Map[String, Any]
  ): EntitiesResult = {
    val entities = listField(payload, "entities").flatMap { raw =>
      asObject(raw).map { entity =>
        EntityInfo(
          line = intField(entity, "line", 0),
          keyword = stringField(entity, "keyword"),
          name = stringField(entity, "name"),
          startOffset = intField(entity, "start_offset", 0),
          endOffset = intField(entity, "end_offset", 0),
          sourcePreview = stringField(entity, "source_preview")
        )
      }
    }
    EntitiesResult(
      path = stringField(payload, "path"),
      nodeName = stringField(payload, "node_name"),
      totalEntities = intField(payload, "total_entities", entities.length),
      returnedEntities = intField(payload, "returned_entities", entities.length),
      truncated = boolField(payload, "truncated", default = false),
      entities = entities
    )
  }

  def decodeTypeAtSelectionResult(
      payload: Map[String, Any]
  ): TypeAtSelectionResult =
    TypeAtSelectionResult(
      selection = decodeSelection(mapField(payload, "selection")),
      command = decodeCommandInfo(mapField(payload, "command")),
      hasType = boolField(payload, "has_type", default = false),
      typeText = stringField(payload, "type_text"),
      term = stringField(payload, "term"),
      typ = stringField(payload, "type"),
      line = intField(payload, "line", 0),
      startOffset = payload.get("start_offset").flatMap(asInt),
      endOffset = payload.get("end_offset").flatMap(asInt),
      message = payload.get("message").map(_.toString).filter(_.nonEmpty)
    )

  def decodeProofBlocksResult(
      payload: Map[String, Any]
  ): ProofBlocksResult = {
    val blocks = listField(payload, "proof_blocks").flatMap { raw =>
      asObject(raw).map { block =>
        ProofBlockInfo(
          proofText = stringField(block, "proof_text"),
          startOffset = intField(block, "start_offset", 0),
          endOffset = intField(block, "end_offset", 0),
          startLine = intField(block, "start_line", 0),
          endLine = intField(block, "end_line", 0),
          commandCount = intField(block, "command_count", 0),
          isApplyStyle = boolField(block, "is_apply_style", default = false)
        )
      }
    }
    ProofBlocksResult(
      scope = decodeProofBlocksScope(stringField(payload, "scope")),
      path = payload.get("path").map(_.toString.trim).filter(_.nonEmpty),
      nodeName = payload.get("node_name").map(_.toString.trim).filter(_.nonEmpty),
      totalBlocks = intField(payload, "total_blocks", blocks.length),
      returnedBlocks = intField(payload, "returned_blocks", blocks.length),
      truncated = boolField(payload, "truncated", default = false),
      proofBlocks = blocks,
      selection = asObject(payload.getOrElse("selection", Map.empty))
        .map(decodeSelection),
      command = asObject(payload.getOrElse("command", Map.empty))
        .map(decodeCommandInfo),
      message = payload.get("message").map(_.toString.trim).filter(_.nonEmpty)
    )
  }

  def decodeProofContextResult(
      payload: Map[String, Any]
  ): ProofContextResult =
    ProofContextResult(
      selection = decodeSelection(mapField(payload, "selection")),
      command = decodeCommandInfo(mapField(payload, "command")),
      success = boolField(payload, "success", default = false),
      timedOut = boolField(payload, "timed_out", default = false),
      hasContext = boolField(payload, "has_context", default = false),
      context = stringField(payload, "context"),
      message = stringField(payload, "message"),
      error = payload.get("error").map(_.toString).filter(_.nonEmpty)
    )

  def decodeDefinitionsResult(
      payload: Map[String, Any]
  ): DefinitionsResult =
    DefinitionsResult(
      selection = decodeSelection(mapField(payload, "selection")),
      command = decodeCommandInfo(mapField(payload, "command")),
      names = payload.get("names").map(asStringList).getOrElse(List.empty),
      success = boolField(payload, "success", default = false),
      timedOut = boolField(payload, "timed_out", default = false),
      hasDefinitions = boolField(payload, "has_definitions", default = false),
      definitions = stringField(payload, "definitions"),
      message = stringField(payload, "message"),
      error = payload.get("error").map(_.toString).filter(_.nonEmpty)
    )

  def decodeDiagnosticsResult(
      payload: Map[String, Any]
  ): DiagnosticsResult = {
    val diagnostics = listField(payload, "diagnostics").flatMap { raw =>
      asObject(raw).map { diag =>
        DiagnosticEntry(
          line = intField(diag, "line", 0),
          startOffset = intField(diag, "start_offset", 0),
          endOffset = intField(diag, "end_offset", 0),
          message = stringField(diag, "message")
        )
      }
    }
    DiagnosticsResult(
      scope = decodeDiagnosticScope(stringField(payload, "scope")),
      severity = decodeDiagnosticSeverity(stringField(payload, "severity")),
      count = intField(payload, "count", diagnostics.length),
      diagnostics = diagnostics,
      path = payload.get("path").map(_.toString),
      nodeName = payload.get("node_name").map(_.toString),
      selection = asObject(payload.getOrElse("selection", Map.empty))
        .map(decodeSelection),
      command = asObject(payload.getOrElse("command", Map.empty))
        .map(decodeCommandInfo)
    )
  }

  def decodeFileStatsResult(
      payload: Map[String, Any]
  ): FileStatsResult =
    FileStatsResult(
      path = stringField(payload, "path"),
      lineCount = intField(payload, "line_count", 0),
      entityCount = intField(payload, "entity_count", 0),
      fullyProcessed = boolField(payload, "fully_processed", default = false),
      hasErrors = boolField(payload, "has_errors", default = false),
      errorCount = intField(payload, "error_count", 0),
      warningCount = intField(payload, "warning_count", 0)
    )

  def decodeProcessingStatusResult(
      payload: Map[String, Any]
  ): ProcessingStatusResult =
    ProcessingStatusResult(
      path = stringField(payload, "path"),
      fullyProcessed = boolField(payload, "fully_processed", default = false),
      unprocessed = intField(payload, "unprocessed", 0),
      running = intField(payload, "running", 0),
      finished = intField(payload, "finished", 0),
      failed = intField(payload, "failed", 0),
      hasErrors = boolField(payload, "has_errors", default = false),
      errorCount = intField(payload, "error_count", 0),
      consolidated = boolField(payload, "consolidated", default = false)
    )

  def decodeSorryPositionsResult(
      payload: Map[String, Any]
  ): SorryPositionsResult = {
    val positions = listField(payload, "positions").flatMap { raw =>
      asObject(raw).map { pos =>
        SorryPosition(
          line = intField(pos, "line", 0),
          keyword = stringField(pos, "keyword"),
          offset = intField(pos, "offset", 0),
          inProof = stringField(pos, "in_proof")
        )
      }
    }
    SorryPositionsResult(
      path = stringField(payload, "path"),
      count = intField(payload, "count", positions.length),
      positions = positions
    )
  }

  private def decodeListedFile(payload: Map[String, Any]): ListedFile =
    ListedFile(
      path = stringField(payload, "path"),
      isTheory = boolField(payload, "is_theory", default = false),
      isOpen = boolField(payload, "is_open", default = false),
      theoryName = payload.get("theory_name").map(_.toString.trim).filter(_.nonEmpty)
    )

  def decodeListFilesResult(
      payload: Map[String, Any]
  ): ListFilesResult = {
    val files = listField(payload, "files").flatMap(raw =>
      asObject(raw).map(decodeListedFile)
    )
    ListFilesResult(
      files = files,
      totalCount = intField(payload, "total_count", files.length),
      openCount = intField(payload, "open_count", files.count(_.isOpen)),
      theoryCount = intField(payload, "theory_count", files.count(_.isTheory))
    )
  }

  def decodeWriteFileResult(payload: Map[String, Any]): WriteFileResult = {
    val commands = listField(payload, "commands").flatMap(asObject)
    val summary = mapField(payload, "summary")
    WriteFileResult(commands = commands, summary = summary)
  }

  def decodeOpenFileResult(
      payload: Map[String, Any]
  ): OpenFileResult =
    OpenFileResult(
      path = stringField(payload, "path"),
      created = boolField(payload, "created", default = false),
      overwritten = boolField(payload, "overwritten", default = false),
      opened = boolField(payload, "opened", default = false),
      inView = boolField(payload, "in_view", default = true),
      tracked = boolField(payload, "tracked", default = false),
      message = stringField(payload, "message")
    )

  def decodeReadFileSearchMatches(
      payload: Map[String, Any]
  ): List[ReadFileSearchMatch] =
    payload.get("content").flatMap(asList).getOrElse(List.empty).flatMap(raw =>
      asObject(raw).map { item =>
        ReadFileSearchMatch(
          lineNumber = intField(item, "line_number", 0),
          context = stringField(item, "context")
        )
      }
    )
}