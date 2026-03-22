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
  *
  * Connection pooling with per-call socket timeouts ensures efficient reuse
  * while supporting long-running operations (sledgehammer, verification).
  */
object IQMcpClient {
  // Export protocol types for backward compatibility
  export IQMcpProtocol._

  private val requestCounter = new AtomicLong(0L)
  private val host = "127.0.0.1"
  private val connectTimeoutMs = 250
  private val minSocketTimeoutMs = 1000

  /** Read the I/Q MCP port from the system property set by the I/Q plugin,
    * falling back to the default if the property is absent or malformed. */
  private def currentPort: Int =
    try { System.getProperty("iq.mcp.port", "8765").trim.toInt }
    catch { case _: NumberFormatException => AssistantConstants.DEFAULT_MCP_PORT }

  /** Connection pool for persistent TCP connection to I/Q MCP server.
    * Reuses connections to avoid per-call socket overhead (250ms per connect).
    * Falls back to fresh connection on any I/O error.
    * Applies per-call socket timeouts to support long-running operations.
    */
  private class ConnectionPool {
    private val lock = new java.util.concurrent.locks.ReentrantLock()
    @volatile private var connection: Option[(Socket, BufferedReader, PrintWriter)] = None
    @volatile private var lastUsedMs = 0L
    private val keepaliveIntervalMs = 30000L // 30 seconds

    private def connectTo(port: Int, socketTimeout: Int): (Socket, BufferedReader, PrintWriter) = {
      val s = new Socket()
      s.connect(new InetSocketAddress(host, port), connectTimeoutMs)
      s.setSoTimeout(socketTimeout)
      val r = new BufferedReader(new InputStreamReader(s.getInputStream, StandardCharsets.UTF_8))
      val w = new PrintWriter(new OutputStreamWriter(s.getOutputStream, StandardCharsets.UTF_8), true)
      authenticateConnection(r, w)
      (s, r, w)
    }

    /** Send the authenticate tool call on a freshly opened TCP connection. */
    private def authenticateConnection(reader: BufferedReader, writer: PrintWriter): Unit = {
      resolveAuthToken().foreach { token =>
        val request = Map(
          "jsonrpc" -> "2.0",
          "id" -> nextRequestId(),
          "method" -> "tools/call",
          "params" -> Map(
            "name" -> "authenticate",
            "arguments" -> Map("token" -> token)
          )
        )
        writer.println(JSON.Format(request))
        val response = reader.readLine()
        if (response == null)
          throw new java.io.IOException("Connection closed during I/Q authentication")
        JSON.parse(response) match {
          case JSON.Object(obj) if obj.contains("error") =>
            throw new java.io.IOException("I/Q authentication failed")
          case _ => // success
        }
      }
    }
    
    def withConnection[T](timeoutMs: Long)(f: (BufferedReader, PrintWriter) => T): T = {
      lock.lock()
      try {
        val port = currentPort
        val now = System.currentTimeMillis()

        // Check if connection is stale or needs keepalive
        if (connection.isDefined && now - lastUsedMs > keepaliveIntervalMs) {
          // Send keepalive ping
          if (!pingExistingConnection()) {
            closeQuietly()
            connection = None
          }
        }
        
        // Get or create connection
        val (socket, reader, writer) = connection match {
          case Some(conn) => conn
          case None =>
            val conn = connectTo(port, minSocketTimeoutMs)
            connection = Some(conn)
            conn
        }
        
        // Apply per-call socket timeout to handle long-running operations
        val effectiveTimeout = math.max(minSocketTimeoutMs.toLong, timeoutMs + AssistantConstants.TIMEOUT_BUFFER_MS)
        val bounded = math.min(effectiveTimeout, Int.MaxValue.toLong).toInt
        socket.setSoTimeout(bounded)
        
        try {
          lastUsedMs = System.currentTimeMillis()
          f(reader, writer)
        } catch {
          case ex: java.io.IOException =>
            // I/O error - close and discard connection, then retry once with fresh connection
            closeQuietly()
            connection = None
            
            val (freshSocket, freshReader, freshWriter) = connectTo(port, bounded)
            connection = Some((freshSocket, freshReader, freshWriter))
            lastUsedMs = System.currentTimeMillis()
            
            try {
              f(freshReader, freshWriter)
            } catch {
              case ex2: Exception =>
                closeQuietly()
                connection = None
                throw ex2
            }
          case ex: Exception =>
            // Non-IO exception after request was sent - connection may be in inconsistent state
            // Discard connection but don't retry (error is likely in parsing/logic, not transport)
            closeQuietly()
            connection = None
            throw ex
        }
      } finally {
        lock.unlock()
      }
    }
    
    private def pingExistingConnection(): Boolean = {
      connection match {
        case Some((_, reader, writer)) =>
          try {
            val request = Map(
              "jsonrpc" -> "2.0",
              "id" -> nextRequestId(),
              "method" -> "ping"
            )
            writer.println(JSON.Format(request))
            val response = reader.readLine()
            // Ping returns {"result":{"status":"ok"}} not the tool_call format
            // Just verify we get a valid JSON response without an error field
            response != null && {
              JSON.parse(response) match {
                case JSON.Object(root) => !root.contains("error")
                case _ => false
              }
            }
          } catch {
            case NonFatal(_) => false
          }
        case None => false
      }
    }
    
    private def closeQuietly(): Unit = {
      connection.foreach { case (socket, reader, writer) =>
        try writer.close() catch { case NonFatal(_) => () }
        try reader.close() catch { case NonFatal(_) => () }
        try socket.close() catch { case NonFatal(_) => () }
      }
    }
    
    def close(): Unit = {
      lock.lock()
      try {
        closeQuietly()
        connection = None
      } finally {
        lock.unlock()
      }
    }
  }
  
  private val connectionPool = new ConnectionPool()

  private def nextRequestId(): String =
    s"assistant-${requestCounter.incrementAndGet()}"

  private def authTokenFromEnv(): Option[String] =
    Option(Isabelle_System.getenv("IQ_AUTH_TOKEN"))
      .map(_.trim)
      .filter(_.nonEmpty)

  /** Resolve the I/Q auth token: prefer the in-JVM system property set by the
    * I/Q plugin, fall back to the IQ_AUTH_TOKEN environment variable. */
  private def resolveAuthToken(): Option[String] =
    Option(System.getProperty("iq.mcp.auth.token"))
      .map(_.trim).filter(_.nonEmpty)
      .orElse(authTokenFromEnv())

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
          root.get("error").flatMap(IQMcpDecoder.asObject) match {
            case Some(errorObj) =>
              val msg = errorObj
                .get("message")
                .map(_.toString)
                .getOrElse("Unknown I/Q MCP error")
              Left(makeToolErrorUserFriendly(msg, toolName))
            case None =>
              val payloadTextOpt =
                for {
                  resultObj <- root.get("result").flatMap(IQMcpDecoder.asObject)
                  content <- resultObj.get("content").flatMap(IQMcpDecoder.asList)
                  textObj <- content.iterator.flatMap(IQMcpDecoder.asObject).find(obj => obj.get("type").contains("text"))
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

    val request = Map(
      "jsonrpc" -> "2.0",
      "id" -> nextRequestId(),
      "method" -> "tools/call",
      "params" -> Map("name" -> toolName, "arguments" -> arguments)
    )

    try {
      connectionPool.withConnection(timeoutMs) { (reader, writer) =>
        writer.println(JSON.Format(request))
        val responseLine = reader.readLine()

        if (responseLine == null) {
          Left("I/Q MCP server closed connection without a response")
        } else {
          parseToolCallResponse(responseLine, Some(toolName))
        }
      }
    } catch {
      case NonFatal(ex) =>
        Left(
          makeToolErrorUserFriendly(
            Option(ex.getMessage).getOrElse(ex.getClass.getSimpleName),
            Some(toolName)
          )
        )
    }
  }
  
  /** Close the connection pool. Called from plugin shutdown. */
  def closePool(): Unit = {
    connectionPool.close()
  }

  private def normalizedToolTimeout(timeoutMs: Long): Long =
    math.max(1L, timeoutMs)

  /** List theory files visible to I/Q.
    * @param filterOpen if Some(true), only include open buffers; if Some(false), exclude open buffers
    * @param filterTheory if Some(true), only include .thy files
    * @param sortBy field to sort by (e.g., "path", "name")
    * @param timeoutMs MCP call timeout in milliseconds
    * @return Either error message or structured list result with file metadata
    */
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
      .map(IQMcpDecoder.decodeListFilesResult)
  }

  /** Read lines from a file with line numbers prefixed.
    * @param path absolute path to the file
    * @param startLine first line to read (1-based), None means line 1
    * @param endLine last line to read (1-based), None or -1 means last line
    * @param timeoutMs MCP call timeout in milliseconds
    * @return Either error message or file content with line numbers (e.g., "42: content")
    */
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

  /** Search for text patterns in a file.
    * @param path absolute path to the file
    * @param pattern text pattern to search for (case-insensitive substring match)
    * @param contextLines number of context lines to include around each match
    * @param timeoutMs MCP call timeout in milliseconds
    * @return Either error message or list of matches with line numbers and context
    */
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
      .map(IQMcpDecoder.decodeReadFileSearchMatches)
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
      .map(IQMcpDecoder.decodeWriteFileResult)
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
      .map(IQMcpDecoder.decodeWriteFileResult)
  }

  /** Open a file in jEdit, optionally creating it.
    * @param path absolute path to the file
    * @param createIfMissing if true, create file if it doesn't exist
    * @param inView if true, open the file in a jEdit buffer (not just track it)
    * @param content initial content when creating a new file
    * @param overwriteIfExists if true and createIfMissing=true, overwrite existing file
    * @param timeoutMs MCP call timeout in milliseconds
    * @return Either error message or open result with creation/overwrite flags
    */
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
      .map(IQMcpDecoder.decodeOpenFileResult)
  }

  def callResolveCommandTarget(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, ResolvedCommandTarget] =
    callTool("resolve_command_target", selectionArgs, timeoutMs)
      .map(IQMcpDecoder.decodeResolvedCommandTarget)

  /** Get structured context information at a cursor position or file offset.
    * @param selectionArgs selection parameters (command_selection, path, offset)
    * @param timeoutMs MCP call timeout in milliseconds
    * @return Either error message or context info with proof state, goal, and command metadata
    */
  def callGetContextInfo(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, ContextInfoResult] =
    callTool("get_context_info", selectionArgs, timeoutMs)
      .map(IQMcpDecoder.decodeContextInfoResult)

  def callGetEntities(
      path: String,
      maxResults: Option[Int],
      timeoutMs: Long
  ): Either[String, EntitiesResult] = {
    val args = Map("path" -> path) ++ maxResults.map("max_results" -> _)
    callTool("get_entities", args, timeoutMs).map(IQMcpDecoder.decodeEntitiesResult)
  }

  def callGetTypeAtSelection(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, TypeAtSelectionResult] =
    callTool("get_type_at_selection", selectionArgs, timeoutMs)
      .map(IQMcpDecoder.decodeTypeAtSelectionResult)

  def callGetProofBlocksForSelection(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, ProofBlocksResult] = {
    val args = Map("scope" -> ProofBlocksScope.Selection.wire) ++ selectionArgs
    callTool("get_proof_blocks", args, timeoutMs).map(IQMcpDecoder.decodeProofBlocksResult)
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
      .map(IQMcpDecoder.decodeProofBlocksResult)
  }

  def callGetProofContext(
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, ProofContextResult] =
    callTool("get_proof_context", selectionArgs, timeoutMs)
      .map(IQMcpDecoder.decodeProofContextResult)

  def callGetDefinitions(
      names: List[String],
      selectionArgs: Map[String, Any],
      timeoutMs: Long
  ): Either[String, DefinitionsResult] = {
    val args = selectionArgs + ("names" -> names.mkString(" "))
    callTool("get_definitions", args, timeoutMs).map(IQMcpDecoder.decodeDefinitionsResult)
  }

  /** Get error or warning diagnostics from PIDE.
    * @param severity Error or Warning
    * @param scope Selection (at cursor) or File (entire file)
    * @param timeoutMs MCP call timeout in milliseconds
    * @param selectionArgs selection parameters for Selection scope
    * @param path file path for File scope
    * @return Either error message or diagnostics with line numbers and messages
    */
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
    callTool("get_diagnostics", args, timeoutMs).map(IQMcpDecoder.decodeDiagnosticsResult)
  }

  /** Get file statistics without reading full content.
    * @param path absolute path to the file
    * @param timeoutMs MCP call timeout in milliseconds
    * @return Either error message or file stats with line/entity counts and processing status
    */
  def callGetFileStats(
      path: String,
      timeoutMs: Long
  ): Either[String, FileStatsResult] = {
    val args = Map("path" -> path)
    callTool("get_file_stats", args, normalizedToolTimeout(timeoutMs))
      .map(IQMcpDecoder.decodeFileStatsResult)
  }

  /** Get PIDE processing status for a file.
    * @param path absolute path to the file
    * @param timeoutMs MCP call timeout in milliseconds
    * @return Either error message or processing status with command counts
    */
  def callGetProcessingStatus(
      path: String,
      timeoutMs: Long
  ): Either[String, ProcessingStatusResult] = {
    val args = Map("path" -> path)
    callTool("get_processing_status", args, normalizedToolTimeout(timeoutMs))
      .map(IQMcpDecoder.decodeProcessingStatusResult)
  }

  /** Find all sorry/oops commands in a file.
    * @param path absolute path to the file
    * @param timeoutMs MCP call timeout in milliseconds
    * @return Either error message or sorry positions with line numbers and enclosing proof names
    */
  def callGetSorryPositions(
      path: String,
      timeoutMs: Long
  ): Either[String, SorryPositionsResult] = {
    val args = Map("path" -> path)
    callTool("get_sorry_positions", args, normalizedToolTimeout(timeoutMs))
      .map(IQMcpDecoder.decodeSorryPositionsResult)
  }

  /** Execute an I/Q explore query (proof verification, sledgehammer, find_theorems, etc.).
    * @param query the query type (Proof, Sledgehammer, or FindTheorems)
    * @param arguments arguments for the query (e.g., proof text, search pattern)
    * @param timeoutMs MCP call timeout in milliseconds
    * @param extraParams additional parameters (e.g., max_results, selection context)
    * @return Either error message or explore result with success status and output
    */
  def callExplore(
      query: ExploreQueryType,
      arguments: String,
      timeoutMs: Long,
      extraParams: Map[String, Any] = Map.empty
  ): Either[String, ExploreResult] = {
    val args =
      Map(
        "query" -> query.wire,
        "command_selection" -> "current",
        "arguments" -> arguments
      ) ++ extraParams

    callTool("explore", args, timeoutMs).map(IQMcpDecoder.decodeExploreResult)
  }

  /** Lightweight ping to check if the I/Q MCP server is responsive.
    * Uses a dedicated JSON-RPC method that doesn't touch any Isabelle state.
    * Returns true if the server responds with ok status, false otherwise.
    * Reuses the connection pool for efficiency.
    */
  def ping(timeoutMs: Long = 500L): Boolean = {
    try {
      connectionPool.withConnection(timeoutMs) { (reader, writer) =>
        val request = Map(
          "jsonrpc" -> "2.0",
          "id" -> nextRequestId(),
          "method" -> "ping"
        )
        writer.println(JSON.Format(request))
        val responseLine = reader.readLine()

        if (responseLine == null) false
        else {
          // Parse ping response directly (not tool_call format)
          // Expected: {"jsonrpc":"2.0","id":"...","result":{"status":"ok"}}
          JSON.parse(responseLine) match {
            case JSON.Object(root) =>
              !root.contains("error") && {
                root.get("result").flatMap {
                  case JSON.Object(resultObj) =>
                    resultObj.get("status").map(_.toString)
                  case _ => None
                }.contains("ok")
              }
            case _ => false
          }
        }
      }
    } catch {
      case NonFatal(_) => false
    }
  }
}