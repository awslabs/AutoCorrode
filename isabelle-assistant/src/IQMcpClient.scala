/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

import java.io.{BufferedReader, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.net.{InetSocketAddress, Socket}
import java.nio.charset.StandardCharsets
import java.util.concurrent.atomic.AtomicLong
import java.util.Locale
import scala.util.control.NonFatal

/** Thin client for talking to the local I/Q MCP server over JSON-RPC.
  *
  * This keeps assistant-side orchestration code decoupled from direct Isabelle
  * runtime execution whenever an equivalent I/Q capability exists.
  */
object IQMcpClient {

  final case class ExploreResult(
      success: Boolean,
      results: String,
      message: String,
      timedOut: Boolean,
      error: Option[String]
  )

  final case class ListedFile(
      path: String,
      isTheory: Boolean,
      isOpen: Boolean,
      theoryName: Option[String]
  )

  final case class ListFilesResult(
      files: List[ListedFile],
      totalCount: Int,
      openCount: Int,
      theoryCount: Int
  )

  final case class ReadFileSearchMatch(
      lineNumber: Int,
      context: String
  )

  final case class WriteFileResult(
      commands: List[Map[String, Any]],
      summary: Map[String, Any]
  )

  final case class OpenFileResult(
      path: String,
      created: Boolean,
      overwritten: Boolean,
      opened: Boolean,
      inView: Boolean,
      message: String
  )

  sealed trait CommandSelection
  case object CurrentSelection extends CommandSelection
  final case class FileOffsetSelection(
      path: String,
      requestedOffset: Option[Int],
      normalizedOffset: Option[Int]
  ) extends CommandSelection
  final case class FilePatternSelection(path: String, pattern: String)
      extends CommandSelection
  final case class UnknownSelection(raw: String) extends CommandSelection

  final case class CommandInfo(
      id: Long,
      length: Int,
      source: String,
      keyword: String,
      nodePath: Option[String],
      startOffset: Option[Int],
      endOffset: Option[Int]
  )

  final case class ResolvedCommandTarget(
      selection: CommandSelection,
      command: CommandInfo
  )

  final case class GoalInfo(
      hasGoal: Boolean,
      goalText: String,
      numSubgoals: Int,
      freeVars: List[String],
      constants: List[String],
      analysisError: Option[String]
  )

  final case class ContextInfoResult(
      selection: CommandSelection,
      command: CommandInfo,
      inProofContext: Boolean,
      hasGoal: Boolean,
      goal: GoalInfo
  )

  final case class EntityInfo(
      line: Int,
      keyword: String,
      name: String,
      startOffset: Int,
      endOffset: Int,
      sourcePreview: String
  )

  final case class EntitiesResult(
      path: String,
      nodeName: String,
      totalEntities: Int,
      returnedEntities: Int,
      truncated: Boolean,
      entities: List[EntityInfo]
  )

  final case class TypeAtSelectionResult(
      selection: CommandSelection,
      command: CommandInfo,
      hasType: Boolean,
      typeText: String,
      term: String,
      typ: String,
      line: Int,
      startOffset: Option[Int],
      endOffset: Option[Int],
      message: Option[String]
  )

  final case class ProofBlockInfo(
      proofText: String,
      startOffset: Int,
      endOffset: Int,
      startLine: Int,
      endLine: Int,
      commandCount: Int,
      isApplyStyle: Boolean
  )

  enum ProofBlocksScope(val wire: String) {
    case Selection extends ProofBlocksScope("selection")
    case File extends ProofBlocksScope("file")
  }

  final case class ProofBlocksResult(
      scope: ProofBlocksScope,
      path: Option[String],
      nodeName: Option[String],
      totalBlocks: Int,
      returnedBlocks: Int,
      truncated: Boolean,
      proofBlocks: List[ProofBlockInfo],
      selection: Option[CommandSelection],
      command: Option[CommandInfo],
      message: Option[String]
  )

  final case class ProofContextResult(
      selection: CommandSelection,
      command: CommandInfo,
      success: Boolean,
      timedOut: Boolean,
      hasContext: Boolean,
      context: String,
      message: String,
      error: Option[String]
  )

  final case class DefinitionsResult(
      selection: CommandSelection,
      command: CommandInfo,
      names: List[String],
      success: Boolean,
      timedOut: Boolean,
      hasDefinitions: Boolean,
      definitions: String,
      message: String,
      error: Option[String]
  )

  enum DiagnosticSeverity(val wire: String) {
    case Error extends DiagnosticSeverity("error")
    case Warning extends DiagnosticSeverity("warning")
  }

  enum DiagnosticScope(val wire: String) {
    case Selection extends DiagnosticScope("selection")
    case File extends DiagnosticScope("file")
  }

  final case class DiagnosticEntry(
      line: Int,
      startOffset: Int,
      endOffset: Int,
      message: String
  )

  final case class DiagnosticsResult(
      scope: DiagnosticScope,
      severity: DiagnosticSeverity,
      count: Int,
      diagnostics: List[DiagnosticEntry],
      path: Option[String],
      nodeName: Option[String],
      selection: Option[CommandSelection],
      command: Option[CommandInfo]
  )

  private val requestCounter = new AtomicLong(0L)
  private val host = "127.0.0.1"
  private val connectTimeoutMs = 250
  private val minSocketTimeoutMs = 1000

  private def nextRequestId(): String =
    s"assistant-${requestCounter.incrementAndGet()}"

  private def authTokenFromEnv(): Option[String] =
    Option(Isabelle_System.getenv("IQ_MCP_AUTH_TOKEN"))
      .map(_.trim)
      .filter(_.nonEmpty)

  private def asObject(value: Any): Option[Map[String, Any]] = value match {
    case JSON.Object(obj) => Some(obj)
    case obj: Map[?, ?] =>
      Some(obj.collect { case (k: String, v) => k -> v }.toMap)
    case _ => None
  }

  private def asList(value: Any): Option[List[Any]] = value match {
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

  private def decodeJsonValue(value: Any): Any = value match {
    case JSON.Object(obj) => obj.view.mapValues(decodeJsonValue).toMap
    case xs: List[?] => xs.map(decodeJsonValue)
    case other => other
  }

  private def parseEmbeddedPayload(text: String): Either[String, Map[String, Any]] = {
    try {
      JSON.parse(text) match {
        case JSON.Object(obj) =>
          Right(obj.view.mapValues(decodeJsonValue).toMap)
        case _ => Left("I/Q MCP payload is not a JSON object")
      }
    } catch {
      case NonFatal(ex) => Left(s"Failed to parse I/Q MCP payload: ${ex.getMessage}")
    }
  }

  private val mutationRootsDeniedPattern =
    """(?s).*Path '([^']+)' is outside allowed mutation roots:\s*(.+)\s*""".r
  private val readRootsDeniedPattern =
    """(?s).*Path '([^']+)' is outside allowed read roots:\s*(.+)\s*""".r

  private def normalizeErrorMessage(message: String): String = {
    val raw = Option(message).map(_.trim).getOrElse("")
    val withoutPrefix = raw.stripPrefix("Tool execution error:").trim
    if (withoutPrefix.nonEmpty) withoutPrefix else raw
  }

  private def summarizeRoots(roots: String): String = {
    val compact = Option(roots).map(_.trim.replaceAll("\\s+", " ")).getOrElse("")
    if (compact.length <= 600) compact
    else compact.take(600) + "..."
  }

  private def rootDeniedMessage(
      toolName: Option[String],
      path: String,
      rootKind: String,
      roots: String
  ): String = {
    val operation = if (rootKind == "mutation") "write/create" else "read"
    val toolPrefix = toolName.map(name => s"Tool '$name' failed. ").getOrElse("")
    s"${toolPrefix}I/Q denied this $operation request because path '$path' is outside allowed $rootKind roots.\n" +
      s"Allowed $rootKind roots: ${summarizeRoots(roots)}\n" +
      "Fix: Plugins -> Plugin Options -> I/Q -> Security. Update the allowed roots and save.\n" +
      "Saving restarts only the I/Q MCP server (no Isabelle/jEdit restart)."
  }

  private[assistant] def makeToolErrorUserFriendly(
      message: String,
      toolName: Option[String] = None
  ): String = {
    val normalized = normalizeErrorMessage(message)
    normalized match {
      case mutationRootsDeniedPattern(path, roots) =>
        rootDeniedMessage(toolName, path, "mutation", roots)
      case readRootsDeniedPattern(path, roots) =>
        rootDeniedMessage(toolName, path, "read", roots)
      case other =>
        val lower = other.toLowerCase(Locale.ROOT)
        if (lower.contains("outside allowed mutation roots")) {
          rootDeniedMessage(
            toolName,
            "<unknown>",
            "mutation",
            "see I/Q server error details"
          )
        } else if (lower.contains("outside allowed read roots")) {
          rootDeniedMessage(
            toolName,
            "<unknown>",
            "read",
            "see I/Q server error details"
          )
        } else if (other.nonEmpty) {
          other
        } else {
          "Unknown I/Q MCP error"
        }
    }
  }

  private[assistant] def parseToolCallResponse(
      rawResponse: String,
      toolName: Option[String] = None
  ): Either[String, Map[String, Any]] = {
    try {
      JSON.parse(rawResponse) match {
        case JSON.Object(root) =>
          root.get("error").flatMap(asObject) match {
            case Some(errorObj) =>
              val msg = errorObj
                .get("message")
                .map(_.toString)
                .getOrElse("Unknown I/Q MCP error")
              Left(makeToolErrorUserFriendly(msg, toolName))
            case None =>
              val payloadTextOpt =
                for {
                  resultObj <- root.get("result").flatMap(asObject)
                  content <- resultObj.get("content").flatMap(asList)
                  textObj <- content.iterator.flatMap(asObject).find(obj => obj.get("type").contains("text"))
                  text <- textObj.get("text").map(_.toString)
                } yield text

              payloadTextOpt match {
                case Some(text) => parseEmbeddedPayload(text)
                case None => Left("I/Q MCP response missing result content")
              }
          }
        case _ => Left("I/Q MCP response is not a JSON object")
      }
    } catch {
      case NonFatal(ex) =>
        Left(
          makeToolErrorUserFriendly(
            s"Failed to parse I/Q MCP response: ${ex.getMessage}",
            toolName
          )
        )
    }
  }

  def callTool(
      toolName: String,
      arguments: Map[String, Any],
      timeoutMs: Long
  ): Either[String, Map[String, Any]] = {
    if (toolName.trim.isEmpty) {
      return Left("Tool name is required")
    }

    val tokenOpt = authTokenFromEnv()
    val params = tokenOpt match {
      case Some(token) =>
        Map("name" -> toolName, "arguments" -> arguments, "auth_token" -> token)
      case None =>
        Map("name" -> toolName, "arguments" -> arguments)
    }
    val baseRequest = Map(
      "jsonrpc" -> "2.0",
      "id" -> nextRequestId(),
      "method" -> "tools/call",
      "params" -> params
    )
    val request = tokenOpt match {
      case Some(token) => baseRequest + ("auth_token" -> token)
      case None => baseRequest
    }

    val socketTimeoutMs = {
      val raw = timeoutMs + AssistantConstants.TIMEOUT_BUFFER_MS
      val bounded = math.max(minSocketTimeoutMs.toLong, math.min(raw, Int.MaxValue.toLong))
      bounded.toInt
    }

    var socket: Socket = null
    var reader: BufferedReader = null
    var writer: PrintWriter = null

    try {
      socket = new Socket()
      socket.connect(
        new InetSocketAddress(host, AssistantConstants.DEFAULT_MCP_PORT),
        connectTimeoutMs
      )
      socket.setSoTimeout(socketTimeoutMs)

      reader = new BufferedReader(
        new InputStreamReader(socket.getInputStream, StandardCharsets.UTF_8)
      )
      writer = new PrintWriter(
        new OutputStreamWriter(socket.getOutputStream, StandardCharsets.UTF_8),
        true
      )

      writer.println(JSON.Format(request))
      val responseLine = reader.readLine()

      if (responseLine == null) {
        Left("I/Q MCP server closed connection without a response")
      } else {
        parseToolCallResponse(responseLine, Some(toolName))
      }
    } catch {
      case NonFatal(ex) =>
        Left(
          makeToolErrorUserFriendly(
            Option(ex.getMessage).getOrElse(ex.getClass.getSimpleName),
            Some(toolName)
          )
        )
    } finally {
      if (writer != null) {
        try writer.close()
        catch { case NonFatal(_) => () }
      }
      if (reader != null) {
        try reader.close()
        catch { case NonFatal(_) => () }
      }
      if (socket != null) {
        try socket.close()
        catch { case NonFatal(_) => () }
      }
    }
  }

  private def boolField(payload: Map[String, Any], key: String, default: Boolean): Boolean =
    payload.get(key) match {
      case Some(value: Boolean) => value
      case Some(value: String) => value.trim.toLowerCase match {
          case "true" => true
          case "false" => false
          case _ => default
        }
      case Some(value: Int) => value != 0
      case Some(value: Long) => value != 0L
      case Some(value: Double) => value != 0.0
      case _ => default
    }

  private def stringField(payload: Map[String, Any], key: String): String =
    payload.get(key).map(_.toString).getOrElse("")

  private def intField(
      payload: Map[String, Any],
      key: String,
      default: Int
  ): Int =
    payload.get(key).flatMap(asInt).getOrElse(default)

  private def longField(
      payload: Map[String, Any],
      key: String,
      default: Long
  ): Long =
    payload.get(key).flatMap(asLong).getOrElse(default)

  private def mapField(payload: Map[String, Any], key: String): Map[String, Any] =
    payload.get(key).flatMap(asObject).getOrElse(Map.empty)

  private def listField(payload: Map[String, Any], key: String): List[Any] =
    payload.get(key).flatMap(asList).getOrElse(List.empty)

  private[assistant] def decodeExploreResult(payload: Map[String, Any]): ExploreResult = {
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

  private def decodeDiagnosticSeverity(
      raw: String
  ): DiagnosticSeverity =
    raw.trim.toLowerCase match {
      case "warning" => DiagnosticSeverity.Warning
      case _ => DiagnosticSeverity.Error
    }

  private def decodeDiagnosticScope(raw: String): DiagnosticScope =
    raw.trim.toLowerCase match {
      case "file" => DiagnosticScope.File
      case _ => DiagnosticScope.Selection
    }

  private[assistant] def decodeResolvedCommandTarget(
      payload: Map[String, Any]
  ): ResolvedCommandTarget =
    ResolvedCommandTarget(
      selection = decodeSelection(mapField(payload, "selection")),
      command = decodeCommandInfo(mapField(payload, "command"))
    )

  private[assistant] def decodeContextInfoResult(
      payload: Map[String, Any]
  ): ContextInfoResult =
    ContextInfoResult(
      selection = decodeSelection(mapField(payload, "selection")),
      command = decodeCommandInfo(mapField(payload, "command")),
      inProofContext = boolField(payload, "in_proof_context", default = false),
      hasGoal = boolField(payload, "has_goal", default = false),
      goal = decodeGoalInfo(mapField(payload, "goal"))
    )

  private[assistant] def decodeEntitiesResult(
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

  private[assistant] def decodeTypeAtSelectionResult(
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

  private def decodeProofBlocksScope(raw: String): ProofBlocksScope =
    raw.trim.toLowerCase match {
      case "file" => ProofBlocksScope.File
      case _ => ProofBlocksScope.Selection
    }

  private[assistant] def decodeProofBlocksResult(
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

  private[assistant] def decodeProofContextResult(
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

  private[assistant] def decodeDefinitionsResult(
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

  private[assistant] def decodeDiagnosticsResult(
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

  private def decodeListedFile(payload: Map[String, Any]): ListedFile =
    ListedFile(
      path = stringField(payload, "path"),
      isTheory = boolField(payload, "is_theory", default = false),
      isOpen = boolField(payload, "is_open", default = false),
      theoryName = payload.get("theory_name").map(_.toString.trim).filter(_.nonEmpty)
    )

  private[assistant] def decodeListFilesResult(
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

  private def decodeWriteFileResult(payload: Map[String, Any]): WriteFileResult = {
    val commands = listField(payload, "commands").flatMap(asObject)
    val summary = mapField(payload, "summary")
    WriteFileResult(commands = commands, summary = summary)
  }

  private[assistant] def decodeOpenFileResult(
      payload: Map[String, Any]
  ): OpenFileResult =
    OpenFileResult(
      path = stringField(payload, "path"),
      created = boolField(payload, "created", default = false),
      overwritten = boolField(payload, "overwritten", default = false),
      opened = boolField(payload, "opened", default = false),
      inView = boolField(payload, "in_view", default = true),
      message = stringField(payload, "message")
    )

  private[assistant] def decodeReadFileSearchMatches(
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

  private def normalizedToolTimeout(timeoutMs: Long): Long =
    math.max(1L, timeoutMs)

  def callListFiles(
      filterOpen: Option[Boolean] = None,
      filterTheory: Option[Boolean] = None,
      sortBy: Option[String] = Some("path"),
      timeoutMs: Long = AssistantConstants.CONTEXT_FETCH_TIMEOUT
  ): Either[String, ListFilesResult] = {
    val args = Map.newBuilder[String, Any]
    filterOpen.foreach(v => args += ("filter_open" -> v))
    filterTheory.foreach(v => args += ("filter_theory" -> v))
    sortBy.map(_.trim).filter(_.nonEmpty).foreach(v => args += ("sort_by" -> v))
    callTool("list_files", args.result(), normalizedToolTimeout(timeoutMs))
      .map(decodeListFilesResult)
  }

  def callReadFileLine(
      path: String,
      startLine: Option[Int],
      endLine: Option[Int],
      timeoutMs: Long
  ): Either[String, String] = {
    val args = Map.newBuilder[String, Any]
    args += ("path" -> path)
    args += ("mode" -> "Line")
    startLine.foreach(v => args += ("start_line" -> v))
    endLine.foreach(v => args += ("end_line" -> v))
    callTool("read_file", args.result(), normalizedToolTimeout(timeoutMs)).map(
      payload => payload.get("content").map(_.toString).getOrElse("")
    )
  }

  def callReadFileSearch(
      path: String,
      pattern: String,
      contextLines: Int,
      timeoutMs: Long
  ): Either[String, List[ReadFileSearchMatch]] = {
    val args = Map(
      "path" -> path,
      "mode" -> "Search",
      "pattern" -> pattern,
      "context_lines" -> math.max(0, contextLines)
    )
    callTool("read_file", args, normalizedToolTimeout(timeoutMs))
      .map(decodeReadFileSearchMatches)
  }

  def callWriteFileLine(
      path: String,
      startLine: Int,
      endLine: Int,
      newText: String,
      timeoutMs: Long,
      waitUntilProcessed: Boolean = true
  ): Either[String, WriteFileResult] = {
    val args = Map(
      "command" -> "line",
      "path" -> path,
      "start_line" -> startLine,
      "end_line" -> endLine,
      "new_str" -> newText,
      "wait_until_processed" -> waitUntilProcessed
    )
    callTool("write_file", args, normalizedToolTimeout(timeoutMs))
      .map(decodeWriteFileResult)
  }

  def callWriteFileInsert(
      path: String,
      insertAfterLine: Int,
      newText: String,
      timeoutMs: Long,
      waitUntilProcessed: Boolean = true
  ): Either[String, WriteFileResult] = {
    val args = Map(
      "command" -> "insert",
      "path" -> path,
      "insert_line" -> insertAfterLine,
      "new_str" -> newText,
      "wait_until_processed" -> waitUntilProcessed
    )
    callTool("write_file", args, normalizedToolTimeout(timeoutMs))
      .map(decodeWriteFileResult)
  }

  def callOpenFile(
      path: String,
      createIfMissing: Boolean,
      inView: Boolean,
      content: Option[String] = None,
      overwriteIfExists: Boolean = false,
      timeoutMs: Long
  ): Either[String, OpenFileResult] = {
    val args = Map.newBuilder[String, Any]
    args += ("path" -> path)
    args += ("create_if_missing" -> createIfMissing)
    args += ("view" -> inView)
    if (createIfMissing) {
      content.foreach(v => args += ("content" -> v))
      if (overwriteIfExists) args += ("overwrite_if_exists" -> true)
    }
    callTool("open_file", args.result(), normalizedToolTimeout(timeoutMs))
      .map(decodeOpenFileResult)
  }

  def callResolveCommandTarget(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, ResolvedCommandTarget] =
    callTool("resolve_command_target", selectionArgs, timeoutMs)
      .map(decodeResolvedCommandTarget)

  def callGetContextInfo(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, ContextInfoResult] =
    callTool("get_context_info", selectionArgs, timeoutMs)
      .map(decodeContextInfoResult)

  def callGetEntities(
      path: String,
      maxResults: Option[Int],
      timeoutMs: Long
  ): Either[String, EntitiesResult] = {
    val args = Map("path" -> path) ++ maxResults.map("max_results" -> _)
    callTool("get_entities", args, timeoutMs).map(decodeEntitiesResult)
  }

  def callGetTypeAtSelection(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, TypeAtSelectionResult] =
    callTool("get_type_at_selection", selectionArgs, timeoutMs)
      .map(decodeTypeAtSelectionResult)

  def callGetProofBlocksForSelection(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, ProofBlocksResult] = {
    val args = Map("scope" -> ProofBlocksScope.Selection.wire) ++ selectionArgs
    callTool("get_proof_blocks", args, timeoutMs).map(decodeProofBlocksResult)
  }

  def callGetProofBlocksForFile(
      path: String,
      maxResults: Option[Int],
      minChars: Option[Int],
      timeoutMs: Long
  ): Either[String, ProofBlocksResult] = {
    val args = Map("scope" -> ProofBlocksScope.File.wire, "path" -> path) ++
      maxResults.map("max_results" -> _) ++
      minChars.map("min_chars" -> _)
    callTool("get_proof_blocks", args, timeoutMs)
      .map(decodeProofBlocksResult)
  }

  def callGetProofContext(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, ProofContextResult] =
    callTool("get_proof_context", selectionArgs, timeoutMs)
      .map(decodeProofContextResult)

  def callGetDefinitions(
      names: List[String],
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, DefinitionsResult] = {
    val args = selectionArgs + ("names" -> names.mkString(" "))
    callTool("get_definitions", args, timeoutMs).map(decodeDefinitionsResult)
  }

  def callGetDiagnostics(
      severity: DiagnosticSeverity,
      scope: DiagnosticScope,
      timeoutMs: Long,
      selectionArgs: Map[String, Any] = Map.empty,
      path: Option[String] = None
  ): Either[String, DiagnosticsResult] = {
    val baseArgs = Map("severity" -> severity.wire, "scope" -> scope.wire)
    val args = scope match {
      case DiagnosticScope.Selection => baseArgs ++ selectionArgs
      case DiagnosticScope.File => baseArgs ++ path.map("path" -> _)
    }
    callTool("get_diagnostics", args, timeoutMs).map(decodeDiagnosticsResult)
  }

  def callExplore(
      query: String,
      arguments: String,
      timeoutMs: Long,
      extraParams: Map[String, Any] = Map.empty
  ): Either[String, ExploreResult] = {
    val args =
      Map(
        "query" -> query,
        "command_selection" -> "current",
        "arguments" -> arguments
      ) ++ extraParams

    callTool("explore", args, timeoutMs).map(decodeExploreResult)
  }
}
