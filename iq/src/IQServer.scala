/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

import org.gjt.sp.jedit.buffer.JEditBuffer
import java.nio.file.Files
import java.io.{BufferedReader, InputStreamReader, PrintWriter, BufferedWriter, OutputStreamWriter}
import java.net.{ServerSocket, Socket}
import java.util.concurrent.{ExecutorService, Executors}
import scala.util.{Try, Success, Failure}
import scala.concurrent.{Future, ExecutionContext}
import java.time.LocalTime
import java.time.format.DateTimeFormatter

import org.gjt.sp.jedit.{View, jEdit, Buffer}
import org.gjt.sp.jedit.io.VFSManager

// Data structures
/**
 * Information about an open file in Isabelle/jEdit.
 *
 * @param file_path The path to the file
 * @param is_isabelle_file Whether the file is an Isabelle theory file
 * @param is_modified Whether the file has been modified since last save
 * @param content_preview A preview of the file content (truncated)
 * @param is_in_view Whether the file is currently in a view
 * @param is_active_view Whether the file is in the active view
 */
case class OpenFileInfo(
  file_path: String,
  is_isabelle_file: Boolean,
  is_modified: Boolean,
  content_preview: String,
  is_in_view: Boolean,
  is_active_view: Boolean
)

/**
 * Information about an Isabelle command (e.g., a proof step, definition, etc.).
 *
 * @param file_path The path to the file containing the command
 * @param command_source The source code of the command
 * @param command_type The type of command (e.g., "statement", "proof_method", etc.)
 * @param results_xml XML results from processing the command
 * @param results_text Text results from processing the command
 * @param range Information about the command's position in the file
 * @param status Status information about the command's processing state
 */
case class CommandInfo(
  file_path: String,
  command_source: String,
  command_type: String,
  results_xml: List[String],
  results_text: List[String],
  range: Map[String, Any],
  status: Map[String, Any]  // New field for command status
)

/**
 * Status information about an Isabelle document.
 *
 * @param file_path The path to the document file
 * @param is_processed Whether the document has been fully processed
 * @param errors Number of errors in the document
 * @param warnings Number of warnings in the document
 * @param running Number of commands currently being processed
 * @param finished Number of commands that have finished processing
 * @param unprocessed Number of commands that have not been processed yet
 */
case class DocumentStatusInfo(
  file_path: String,
  is_processed: Boolean,
  errors: Int,
  warnings: Int,
  running: Int,
  finished: Int,
  unprocessed: Int
)

object IQLineOffsetUtils {
  private def clamp(value: Int, min: Int, max: Int): Int = {
    if (max < min) min else math.max(min, math.min(max, value))
  }

  def splitLines(text: String): Array[String] = text.split("\n", -1)

  private def safeTotalLines(totalLines: Int): Int = math.max(1, totalLines)

  def normalizeLineIndex(totalLines: Int, line: Int): Int = {
    val safeTotal = safeTotalLines(totalLines)
    val rawIndex = if (line < 0) safeTotal + line else line - 1
    clamp(rawIndex, 0, safeTotal - 1)
  }

  def normalizeLineRange(totalLines: Int, startLine: Int, endLine: Int): (Int, Int) = {
    val start = normalizeLineIndex(totalLines, startLine)
    val end = normalizeLineIndex(totalLines, endLine)
    if (start <= end) (start, end) else (end, start)
  }

  def normalizeLineBoundary(totalLines: Int, line: Int, increment: Boolean = false): Int = {
    val safeTotal = safeTotalLines(totalLines)
    val rawIndex = if (line < 0) safeTotal + line else line - 1
    val adjusted = rawIndex + (if (increment) 1 else 0)
    clamp(adjusted, 0, safeTotal)
  }

  def clampOffset(offset: Int, textLength: Int): Int =
    clamp(offset, 0, math.max(0, textLength))

  def normalizeOffsetRange(startOffset: Int, endOffset: Int, textLength: Int): (Int, Int) = {
    val start = clampOffset(startOffset, textLength)
    val end = clampOffset(endOffset, textLength)
    if (start <= end) (start, end) else (end, start)
  }

  private def lineStartOffsets(text: String): Array[Int] = {
    val starts = scala.collection.mutable.ArrayBuffer[Int](0)
    var i = 0
    while (i < text.length) {
      if (text.charAt(i) == '\n') starts += (i + 1)
      i += 1
    }
    starts.toArray
  }

  def lineNumberToOffset(
    text: String,
    line: Int,
    increment: Boolean = false,
    withLastNewLine: Boolean = true
  ): Int = {
    val starts = lineStartOffsets(text)
    val totalLines = starts.length
    val boundaryIndex = normalizeLineBoundary(totalLines, line, increment = increment)
    val boundaryOffset =
      if (boundaryIndex >= totalLines) text.length
      else starts(boundaryIndex)

    val correctedOffset =
      if (!withLastNewLine && boundaryOffset > 0 && text.charAt(boundaryOffset - 1) == '\n') {
        boundaryOffset - 1
      } else {
        boundaryOffset
      }

    clampOffset(correctedOffset, text.length)
  }

  def formatLinesWithNumbers(
    lines: Array[String],
    startLine: Int,
    endLine: Int,
    highlightLine: Option[Int] = None
  ): String = {
    if (lines.isEmpty) return ""

    val clampedStart = clamp(startLine, 0, lines.length - 1)
    val clampedEnd = clamp(endLine, 0, lines.length - 1)
    if (clampedStart > clampedEnd) return ""

    val builder = new StringBuilder()
    for (i <- clampedStart to clampedEnd) {
      val prefix = if (Some(i) == highlightLine) "→ " else "  "
      builder.append(f"$prefix${i + 1}%d:${lines(i)}\n")
    }
    builder.toString()
  }
}

// TODO: The code uses seemingly random negative error IDs. Explain where
// they come from if the values matter, or otherwise introduce an enum.

/**
 * Model-Client-Protocol (MCP) server for Isabelle/jEdit.
 *
 * This server provides a JSON-RPC interface for external clients to interact with Isabelle.
 * It handles client connections, processes requests, and returns responses according to
 * the MCP specification.
 *
 * @param port The port number to listen on (default: 8765)
 */
class IQServer(port: Int = 8765) {
  /**
   * Waits for a theory to be fully processed by marking it as required and polling until completion.
   *
   * @param model The document model for the theory
   * @param timeoutMs Maximum time to wait in milliseconds
   * @return A tuple containing (completion_succeeded, final_status)
   */
  private def waitForTheoryCompletion(
    model: Document_Model,
    timeout_ms: Option[Int],
    timeoutPerCommandMs: Option[Int] = None
  ): (Boolean, Document_Status.Node_Status) = {

    val startTime = System.currentTimeMillis()
    val node_name = model.node_name

    Output.writeln(s"I/Q Server: Waiting for theory completion: $node_name (timeout: ${timeout_ms}, timeout_per_command: ${timeoutPerCommandMs}ms)")

    // Save the original required state
    val originalRequiredState = GUI_Thread.now {
      model.node_required
    }

    GUI_Thread.now {
      Document_Model.node_required(node_name, set = true)
    }

    // Get initial status to ensure we always have a valid status object
    var currentStatus: Document_Status.Node_Status = GUI_Thread.now {
      val snapshot = Document_Model.snapshot(model)
      val state = snapshot.state
      val version = snapshot.version
      Document_Status.Node_Status.make(Date.now(), state, version, node_name)
    }

    var completed = false
    var iterations = 0
    var perCommandTimerStart: Option[Long] = None

    def is_timeout() : Boolean = {
      timeout_ms match {
        case Some(t) => (System.currentTimeMillis() - startTime) >= t
        case _ => false
      }
    }

    while (!completed && !is_timeout()) {
      currentStatus = GUI_Thread.now {
        val snapshot = Document_Model.snapshot(model)
        val state = snapshot.state
        val version = snapshot.version
        Document_Status.Node_Status.make(Date.now(), state, version, node_name)
      }

      // Check completion status
      completed = currentStatus.terminated &&
                  (currentStatus.consolidated ||
                   (currentStatus.unprocessed == 0 && currentStatus.running == 0))

      // Per-command timeout logic
      if (currentStatus.unprocessed == 0 && perCommandTimerStart.isEmpty) {
        // First time we see unprocessed == 0, start the timer
        perCommandTimerStart = Some(System.currentTimeMillis())
        Output.writeln(s"I/Q Server: All commands processed, starting per-command timer for running commands")
      }

      // Check per-command timeout abort conditions
      if (currentStatus.unprocessed == 0) {
        if (currentStatus.running == 0) {
          // No commands running, we're done
          completed = true
          Output.writeln(s"I/Q Server: No commands running, completion achieved")
        } else {
          // Check if per-command timer has fired
          timeoutPerCommandMs match {
            case Some(perCmdTimeout) =>
              val timerStart = perCommandTimerStart.get
              val perCommandElapsed = System.currentTimeMillis() - timerStart
              if (perCommandElapsed >= perCmdTimeout) {
                Output.writeln(s"I/Q Server: Per-command timeout of ${perCmdTimeout}ms exceeded (${perCommandElapsed}ms elapsed), aborting")
                completed = true
              }
            case None => // No per-command timeout set
          }
        }
      }

      iterations += 1

      // Log progress every 5 iterations (5 seconds)
      if (iterations % 5 == 0) {
        Output.writeln(s"I/Q Server: Theory completion progress - unprocessed: ${currentStatus.unprocessed}, running: ${currentStatus.running}, finished: ${currentStatus.finished}, failed: ${currentStatus.failed}, terminated: ${currentStatus.terminated}, consolidated: ${currentStatus.consolidated}")
      }

      if (!completed) {
        Thread.sleep(1000)
      }
    }

    val elapsedMs = System.currentTimeMillis() - startTime
    if (completed) {
      Output.writeln(s"I/Q Server: Theory completion succeeded after ${elapsedMs}ms")
    } else {
      Output.writeln(s"I/Q Server: Theory completion timed out after ${elapsedMs}ms")
    }

    // Restore the original required state
    GUI_Thread.now {
      Document_Model.node_required(node_name, set = originalRequiredState)
    }

    // Ensure we always return a valid status object
    (completed, currentStatus)
  }

  /**
   * Format a decimal number to one digit after the decimal point
   */
  private def formatDecimal(value: Double): Double = {
    BigDecimal(value).setScale(1, BigDecimal.RoundingMode.HALF_UP).toDouble
  }

  /** The server socket that listens for client connections */
  private var serverSocket: Option[ServerSocket] = None

  /** Flag indicating whether the server is running */
  private var isRunning = false

  /** Thread pool for handling client connections */
  private val executor: ExecutorService = Executors.newCachedThreadPool()

  /** Execution context for asynchronous operations */
  private implicit val ec: ExecutionContext = ExecutionContext.fromExecutor(executor)

  // Timestamp formatter for socket logging
  private val timeFormatter = DateTimeFormatter.ofPattern("HH:mm:ss.SSS")

  /**
   * Gets the current timestamp formatted as HH:mm:ss.SSS
   *
   * @return The formatted timestamp string
   */
  private def getTimestamp(): String = {
    LocalTime.now().format(timeFormatter)
  }

  /**
   * Starts the MCP server.
   *
   * Creates a server socket on the specified port and begins listening for client connections.
   * Each client connection is handled in a separate thread from the executor thread pool.
   */
  def start(): Unit = {
    try {
      serverSocket = Some(new ServerSocket(port))
      isRunning = true

      Output.writeln(s"I/Q Server starting on port $port")

      Future {
        serverSocket.foreach { socket =>
          while (isRunning) {
            try {
              val clientSocket = socket.accept()
              Output.writeln(s"MCP Client connected: ${clientSocket.getRemoteSocketAddress}")

              executor.submit(new Runnable {
                def run(): Unit = handleClient(clientSocket)
              })
            } catch {
              case _: java.net.SocketException if !isRunning =>
                // Server was stopped, ignore
              case ex: Exception =>
                Output.writeln(s"Error accepting client connection: ${ex.getMessage}")
            }
          }
        }
      }

    } catch {
      case ex: Exception =>
        Output.writeln(s"Failed to start MCP server: ${ex.getMessage}")
    }
  }

  /**
   * Stops the MCP server.
   *
   * Closes the server socket and shuts down the executor thread pool.
   */
  def stop(): Unit = {
    isRunning = false
    serverSocket.foreach(_.close())
    executor.shutdown()
    Output.writeln("I/Q Server stopped")
  }

  /**
   * Handles a client connection.
   *
   * Sets up input/output streams, processes client requests, and sends responses.
   * The connection is kept open until the client disconnects or an error occurs.
   *
   * @param clientSocket The client socket to handle
   */
  private def handleClient(clientSocket: Socket): Unit = {
    try {
      // Configure socket for large responses
      clientSocket.setSendBufferSize(65536)  // 64KB send buffer
      clientSocket.setTcpNoDelay(true)       // Disable Nagle's algorithm for immediate sending

      Output.writeln(s"MCP Client connected with buffer size: ${clientSocket.getSendBufferSize} (no timeout)")

      // Update client connection status
      IQCommunicationLogger.updateClientStatus(true)

      val reader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream))
      // Use a larger buffer for the PrintWriter to handle large responses
      val writer = new PrintWriter(new BufferedWriter(new OutputStreamWriter(clientSocket.getOutputStream), 65536), true)

      var line: String = null
      while ({ line = reader.readLine(); line != null }) {
        try {
          // Log incoming request if logging is enabled
          if (IQCommunicationLogger.isLoggingEnabled) {
            IQCommunicationLogger.logCommunication(s"${getTimestamp()} [RECV] $line")
          }

          processRequest(line) match {
            case Some(response) =>
              Output.writeln(s"I/Q Server: Sending response of length ${response.length} chars")
              if (response.length > 10000) {
                Output.writeln(s"I/Q Server: Large response preview: ${response.take(200)}...${response.takeRight(200)}")
              }

              // Log outgoing response if logging is enabled
              if (IQCommunicationLogger.isLoggingEnabled) {
                IQCommunicationLogger.logCommunication(s"${getTimestamp()} [SEND] $response")
              }

              // Send response with detailed logging
              val responseBytes = (response + "\n").getBytes("UTF-8")
              Output.writeln(s"I/Q Server: About to send ${responseBytes.length} bytes")

              writer.println(response)
              writer.flush() // Ensure response is sent immediately

              Output.writeln(s"I/Q Server: Response sent and flushed (${responseBytes.length} bytes)")
            case None =>
              Output.writeln(s"I/Q Server: No response needed (notification)")
          }

          // Verify the writer is still valid
          if (writer.checkError()) {
            Output.writeln("I/Q Server: WARNING - Writer error detected after sending response")
          } else {
            Output.writeln("I/Q Server: Writer status OK after sending response")
          }
        } catch {
          case ex: Exception =>
            val errorResponse = formatErrorResponse(None, -32603, s"Internal error: ${ex.getMessage}")
            writer.println(errorResponse)
        }
      }
    } catch {
      case ex: Exception =>
        Output.writeln(s"Error handling MCP client: ${ex.getMessage}")
    } finally {
      try {
        clientSocket.close()
        Output.writeln("MCP Client disconnected")

        // Update client connection status
        IQCommunicationLogger.updateClientStatus(false)
      } catch {
        case _: Exception => // Ignore close errors
      }
    }
  }

  /**
   * Processes a JSON-RPC request and generates an optional response.
   *
   * Parses the request, extracts the method and ID, and dispatches to the appropriate handler.
   * Returns None for notifications (no response needed), Some(response) for requests.
   *
   * @param requestLine The JSON-RPC request string
   * @return Some(response) for requests, None for notifications
   */
  private def processRequest(requestLine: String): Option[String] = {
    try {
      Output.writeln(s"I/Q Server: Processing request: $requestLine")

      val json = JSON.parse(requestLine)
      val (method, id) = extractMethodAndId(json)

      Output.writeln(s"I/Q Server: Parsed method='$method', id=$id")

      id match {
        case Some(requestId) =>
          val result = method match {
            case "initialize" => createInitializeResult()
            case "tools/list" => createToolsListResult()
            case "tools/call" => handleToolCallFromJson(json)
            case _ =>
              Output.writeln(s"I/Q Server: Unknown method '$method'")
              Left(s"Method not found: $method")
          }

          result match {
            case Right(data) => Some(formatSuccessResponse(requestId, data))
            case Left(error) => Some(formatErrorResponse(Some(requestId), ErrorCodes.METHOD_NOT_FOUND, error))
          }
        /* From https://www.jsonrpc.org/specification:
         *  "A Notification is a Request object without an "id" member.
         * A Request object that is a Notification signifies the Client's lack
         * of interest in the corresponding Response object, and as such no
         * Response object needs to be returned to the client.
         * The Server MUST NOT reply to a Notification, including those that
         * are within a batch request."
         */
        case None =>
          method match {
            case m if m.startsWith("notifications/") =>
              Output.writeln(s"I/Q Server: Handling notification '$method'")
              handleNotification(method, json)
              None // No response for notifications
            case _ =>
              Output.writeln(s"I/Q Server: Ignoring unknown notification '$method'")
              None // No response for notifications
          }
      }
    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Error processing request: ${ex.getMessage}")
        ex.printStackTrace()
        Some(formatErrorResponse(None, ErrorCodes.INTERNAL_ERROR, s"Internal error: ${ex.getMessage}"))
    }
  }

  /**
   * Handles JSON-RPC notifications (messages without id that don't expect responses).
   *
   * @param method The notification method name
   * @param json The parsed JSON notification
   */
  private def handleNotification(method: String, json: JSON.T): Unit = {
    method match {
      case "notifications/initialized" =>
        Output.writeln("I/Q Server: Client initialization complete")
      case _ =>
        Output.writeln(s"I/Q Server: Unknown notification method: $method")
    }
  }

  /**
   * Extracts the method and ID from a JSON-RPC request.
   *
   * @param json The parsed JSON-RPC request
   * @return A tuple containing (method, id) where id is None for notifications
   */
  private def extractMethodAndId(json: JSON.T): (String, Option[Any]) = {
    json match {
      case JSON.Object(obj) =>
        val method = obj.get("method") match {
          case Some(s: String) => s
          case Some(other) => other.toString
          case None => ""
        }

        // Preserve request ID, whatever type it may have
        // (None, Some(String), Some(Int), Some(Double), ...)
        val id = obj.get("id")

        (method, id)

      case _ =>
        Output.writeln(s"I/Q Server: JSON is not an object: $json")
        ("", None)
    }
  }

  /**
   * Wraps tool call results for JSON-RPC response.
   *
   * @param result The result data from a tool handler
   * @return Wrapped result data
   */
  private def wrapToolCallResult(result: Map[String, Any]): Map[String, Any] = {
    val serializedJson = JSON.Format(result)
    Map("content" -> List(Map("type" -> "text", "text" -> serializedJson)))
  }

  /**
   * Handles a tools/call request.
   *
   * Extracts the tool name and parameters from the request and dispatches to the appropriate handler.
   *
   * @param json The parsed JSON-RPC request
   * @return Either error message or result data
   */
  private def handleToolCallFromJson(json: JSON.T): Either[String, Map[String, Any]] = {
    try {
      Output.writeln(s"I/Q Server: Raw JSON for tool call: $json")

      val (toolName, params) = extractToolAndParams(json)
      Output.writeln(s"I/Q Server: Extracted tool='$toolName', params=$params")

      val result = toolName match {
        case "list_files" => handleListFiles(params)
        case "get_command_info" => handleGetCommand(params)
        case "get_document_info" => handleGetDocumentInfo(params)
        case "open_file" => handleOpenFile(params)
        case "create_file" => handleCreateFile(params)
        case "read_file" => handleReadTheoryFile(params)
        case "write_file" => handleWriteTheoryFile(params)
        case "explore" => handleExplore(params)
        case "save_file" => handleSaveFile(params)
        case _ =>
          Output.writeln(s"I/Q Server: Unknown tool name: '$toolName'")
          Left(s"Unknown tool: $toolName")
      }

      result.map(wrapToolCallResult)
    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Tool execution error: ${ex.getMessage}")
        ex.printStackTrace()
        Left(s"Tool execution error: ${ex.getMessage}")
    }
  }

  /**
   * Extracts the tool name and parameters from a tools/call request.
   *
   * @param json The parsed JSON-RPC request
   * @return A tuple containing (toolName, params)
   */
  private def extractToolAndParams(json: JSON.T): (String, Map[String, Any]) = {
    json match {
      case JSON.Object(obj) =>
        obj.get("params") match {
          case Some(JSON.Object(params)) =>
            val toolName = params.get("name") match {
              case Some(nameStr: String) => nameStr
              case Some(other) => other.toString
              case None => ""
            }

            val arguments = params.get("arguments") match {
              case Some(JSON.Object(args)) => extractArguments(args)
              case _ => Map.empty[String, Any]
            }

            (toolName, arguments)

          case _ => ("", Map.empty[String, Any])
        }

      case _ => ("", Map.empty[String, Any])
    }
  }

  /**
   * Extracts arguments from a JSON object and converts them to appropriate Scala types.
   *
   * @param jsonMap The JSON object containing arguments
   * @return A map of argument names to values
   */
  def extractArguments(jsonMap: Map[String, JSON.T]): Map[String, Any] = {
    jsonMap.map { case (key, value) =>
      val convertedValue = value match {
        case s: String => s
        case b: Boolean => b
        case n: Number => n.intValue()
        case other => other.toString // Fallback for other types
      }
      key -> convertedValue
    }
  }

  /**
   * Formats a successful JSON-RPC response.
   *
   * @param id The request ID
   * @param result The result data
   * @return A JSON-RPC response string
   */
  private def formatSuccessResponse(id: Any, result: Map[String, Any]): String = {
    val responseData = Map(
      "jsonrpc" -> "2.0",
      "id" -> id,
      "result" -> result
    )
    JSON.Format(responseData)
  }

  /**
   * Formats an error JSON-RPC response.
   *
   * @param id The request ID (can be None for parse errors)
   * @param code The error code
   * @param message The error message
   * @return A JSON-RPC response string
   */
  private def formatErrorResponse(id: Option[Any], code: Int, message: String): String = {
    val responseData = Map(
      "jsonrpc" -> "2.0",
      "id" -> id.orNull,
      "error" -> Map(
        "code" -> code,
        "message" -> message
      )
    )
    JSON.Format(responseData)
  }

  /**
   * Creates result data for the initialize method.
   *
   * @return Either error message or result data
   */
  private def createInitializeResult(): Either[String, Map[String, Any]] = {
    val timestamp = java.time.Instant.now().toString
    val result = Map(
      "protocolVersion" -> "2024-11-05",
      "capabilities" -> Map(
        "tools" -> Map.empty[String, Any],
        "resources" -> Map.empty[String, Any]
      ),
      "serverInfo" -> Map(
        "name" -> "isabelle-mcp-server",
        "version" -> s"1.0.0-restored-$timestamp"
      )
    )
    Right(result)
  }

  /**
   * Creates result data for the tools/list method.
   *
   * @return Either error message or result data
   */
  private def createToolsListResult(): Either[String, Map[String, Any]] = {
    val tools = List(
      Map(
        "name" -> "list_files",
        "description" -> "List all files tracked by Isabelle, both open and non-open, with detailed information",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "filter_open" -> Map(
              "type" -> "boolean",
              "description" -> "Filter to show only open files (true) or only non-open files (false)"
            ),
            "filter_theory" -> Map(
              "type" -> "boolean",
              "description" -> "Filter to show only theory files (true) or only non-theory files (false)"
            ),
            "sort_by" -> Map(
              "type" -> "string",
              "description" -> "Sort results by: 'path', 'theory', or 'type'"
            )
          ),
          "required" -> List.empty[String]
        )
      ),
      Map(
        "name" -> "get_command_info",
        "description" -> "Get status of commands (e.g. definitions or proof steps) in an Isabelle theory file. Includes detailed information about errors, warnings, and intermediate proof states, and timing.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "mode" -> Map(
              "type" -> "string",
              "description" -> "Command mode. Possible values are: 'current', to query current proof-step/command. 'line', to query commands in line range.",
              "enum" -> List("current", "line")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> "For 'line' and 'current' mode: Path to theory file. For 'current' mode, can be omitted; if present, must match the currently open file."
            ),
            "start_line" -> Map(
              "type" -> "integer",
              "description" -> "Only for 'line' mode: Start line number (1-based, inclusive; default 1). Negative numbers count from the end of the file (-1 = last line)."
            ),
            "end_line" -> Map(
              "type" -> "integer",
              "description" -> "Only for 'line' mode: End line number (1-based, inclusive; default -1). Negative numbers count from the end of the file (-1 = last line)."
            ),
            "xml_result_file" -> Map(
              "type" -> "string",
              "description" -> "Optional file path to dump full markup (e.g. references) for the results"
            ),
            "wait_until_processed" -> Map(
              "type" -> "boolean",
              "description" -> "Wait until all commands are processed successfully OR one fails before returning results (default: false)"
            ),
            "timeout" -> Map(
              "type" -> "integer",
              "description" -> "Timeout in milliseconds for wait_until_processed (default: 5000)"
            ),
            "timeout_per_command" -> Map(
              "type" -> "integer",
              "description" -> "Maximum time in milliseconds to wait for individual commands to complete (default: 5000)"
            ),
            "include_results" -> Map(
              "type" -> "boolean",
              "description" -> "Include command results in the response (default: false). When false, results are written to a temporary file and the filename is returned."
            )
          ),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "get_document_info",
        "description" -> "Get status of an Isabelle theory file, including numbers and details about errors, warnings, and timing information for all commands. Only use to check overall state of a theory. If you work on a specific section of the theory file, use get_command_info.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "path" -> Map(
              "type" -> "string",
              "description" -> "Path to the theory file"
            ),
            "include_errors" -> Map(
              "type" -> "boolean",
              "description" -> "Include detailed error information (default: true)"
            ),
            "include_warnings" -> Map(
              "type" -> "boolean",
              "description" -> "Include warning information (default: false)"
            ),
            "timing_threshold_ms" -> Map(
              "type" -> "number",
              "description" -> "Only include detailed timing information for commands that took longer than this threshold in milliseconds (default: 3000)"
            ),
            "wait_until_processed" -> Map(
              "type" -> "boolean",
              "description" -> "Wait for the theory to be fully processed before returning results. Only applies to theory files. (default: false)"
            ),
            "timeout" -> Map(
              "type" -> "number",
              "description" -> "If set, timeout in milliseconds for wait_until_processed. If unset, no timeout. Default: no timeout."
            ),
            "timeout_per_command" -> Map(
              "type" -> "integer",
              "description" -> "Maximum time in milliseconds to wait for individual commands to complete (default: 5000)"
            )
          ),
          "required" -> List("path"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "open_file",
        "description" -> "Open an existing file in Isabelle/jEdit",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "path" -> Map(
              "type" -> "string",
              "description" -> "Path to the file to open"
            ),
            "create_if_missing" -> Map(
              "type" -> "boolean",
              "description" -> "Create file if it doesn't exist (default: false)"
            ),
            "view" -> Map(
              "type" -> "boolean",
              "description" -> "Open file in jEdit view (default: true). If false, file is only tracked in FileBuffer."
            )
          ),
          "required" -> List("path")
        )
      ),
      Map(
        "name" -> "create_file",
        "description" -> "Create a new file with specified content in Isabelle/jEdit",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "path" -> Map(
              "type" -> "string",
              "description" -> "Path to the file to create"
            ),
            "content" -> Map(
              "type" -> "string",
              "description" -> "Content to write to the new file"
            ),
            "overwrite_if_exists" -> Map(
              "type" -> "boolean",
              "description" -> "Overwrite file if it already exists (default: false)"
            ),
            "view" -> Map(
              "type" -> "boolean",
              "description" -> "Open file in jEdit view (default: true). If false, file is only tracked in FileBuffer."
            )
          ),
          "required" -> List("path", "content")
        )
      ),
      Map(
        "name" -> "read_file",
        "description" -> "Read content from an Isabelle theory file. Supports reading full file or specific line ranges using structured parameters. Supports 'Line' and 'Pattern' modes.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "path" -> Map(
              "type" -> "string",
              "description" -> "Path to the theory file to read"
            ),
            "mode" -> Map(
              "type" -> "string",
              "description" -> "Mode to read the file in. 'Line' mode reads specific lines, 'Search' mode searches for a pattern.",
              "enum" -> List("Line", "Search")
            ),
            "start_line" -> Map(
              "type" -> "integer",
              "description" -> "Start line number (1-based, inclusive). Negative numbers count from the end of the file (-1 = last line). Used in 'Line' mode."
            ),
            "end_line" -> Map(
              "type" -> "integer",
              "description" -> "End line number (1-based, inclusive). Negative numbers count from the end of the file (-1 = last line). Used in 'Line' mode."
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> "Pattern to search for in the file. Used in 'Search' mode."
            ),
            "context_lines" -> Map(
              "type" -> "integer",
              "description" -> "Number of context lines to include around matching lines. Used in 'Pattern' mode."
            )
          ),
          "required" -> List("path", "mode")
        )
      ),
      Map(
        "name" -> "write_file",
        "description" -> "Write or modify content in an Isabelle theory file. Supports replacement and text insertion. Returns the status of commands affected by the edit, and statistics on how many commands where successful/failed/canceled/unprocessed.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "command" -> Map(
              "type" -> "string",
              // We actually also support 'line', but this is not advertised for now
              // to match the existing fs_write interface more closely
              "description" -> "The command to run. Allowed options are: 'str_replace', 'insert'",
              "enum" -> List("str_replace", "insert")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> "For all commands. Path to the theory file to modify. Must be open in Isabelle/jEdit."
            ),
            "new_str" -> Map(
              "type" -> "string",
              "description" -> "For all commands. The new string to write."
            ),
            "old_str" -> Map(
              "type" -> "string",
              "description" -> "For command 'str_replace'. String to replace. Must be unique."
            ),
            "insert_line" -> Map(
              "type" -> "integer",
              "description" -> "For command 'insert': Line number (1-based, inclusive) after which to insert. Negative numbers count from the end of the file (-1 = last line)."
            ),
            "start_line" -> Map(
              "type" -> "integer",
              "description" -> "For command 'line': Line number (1-based, inclusive) to start insertion. Negative numbers count from the end of the file (-1 = last line)."
            ),
            "end_line" -> Map(
              "type" -> "integer",
              "description" -> "For command 'line': End line number (1-based, inclusive). Negative numbers count from the end of the file (-1 = last line)."
            ),
            "xml_result_file" -> Map(
              "type" -> "string",
              "description" -> "For all commands. Optional file path to dump full XML results for new commands (must be full real path)"
            ),
            "wait_until_processed" -> Map(
              "type" -> "boolean",
              "description" -> "For all commands. Wait until commands are processed before returning (default: true)"
            ),
            "timeout" -> Map(
              "type" -> "integer",
              "description" -> "For all commands. Timeout in milliseconds for wait_until_processed (default: 5000)"
            ),
            "timeout_per_command" -> Map(
              "type" -> "integer",
              "description" -> "Maximum time in milliseconds to wait for individual commands to complete (default: 5000)"
            )
          ),
          "required" -> List("path"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "explore",
        "description" -> "I/Q explore. Run a query for non-invasive proof exploration: Try Isar proof scripts, find theorems, run sledgehammer, at any point in a document.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "query" -> Map(
              "type" -> "string",
              "description" -> "Query type to execute. For the `proof` query type, you need to import Isar_Explore.thy from the I/Q plugin root directory.",
              "enum" -> List("proof", "sledgehammer", "find_theorems")
            ),
            "command_selection" -> Map(
              "type" -> "string",
              "description" -> "Method of specifying the command AFTER which the proof exploration should be applied. Values are: * 'current', to apply query after current command. * 'file_offset', so specify command after which query should happen via file and absolute offset. Uses 'path' and 'offset' argument. * 'file_pattern', to specify command after which query should happen via filenme and a unique substring. Uses 'path' and 'pattern argument.",
              "enum" -> List("current", "file_offset", "file_pattern")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> "File to run the query in. Required if 'command_selection' is 'file_offset' or 'file_pattern'. MUST be a full file path with extension."
            ),
            "offset" -> Map(
              "type" -> "integer",
              "description" -> "Character offset of command AFTER which to apply the query. Required if 'command_selection' is 'file_offset'."
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> "Substring pattern to match command AFTER which to apply the query. Required if 'command_selection' is 'file_pattern'. Must match exactly once in the specified file. If you want to fix a `sorry` or replace an existing proof step, use the substring of the command/proof step BEFORE the step to rework."
            ),
            "arguments" -> Map(
              "type" -> "string",
              "description" -> "Arguments for the query. For 'proof': Isar proof methods, required. Example: 'by simp' or 'apply blast'. For 'sledgehammer': Prover names - optional, uses defaults if empty. Examples: 'cvc5 verit z3 e spass vampire zipperposition'. For 'find_theorems': search criteria - required. Examples: * Goal term pattern '\\<open>(_ :: unat) = (_ :: unat)\\<close>' (MUST include cartouche or quotes aronud the pattern) * Theorem name pattern, 'name:PATTERN'."
            )
          ),
          "required" -> List("query", "command_selection"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "save_file",
        "description" -> "Save files in Isabelle/jEdit. If path is provided, saves that specific file (if open and modified). If no path provided, saves all modified files.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "path" -> Map(
              "type" -> "string",
              "description" -> "Optional path to specific file to save. If not provided, saves all modified files."
            )
          )
        )
      )
    )

    val result = Map("tools" -> tools)
    Right(result)
  }

  /**
   * Handles the list_files tool request.
   *
   * Lists all files tracked by Isabelle, both open and non-open, with detailed information.
   * Supports filtering by open status and theory status, and sorting by various criteria.
   *
   * @param params The tool parameters
   * @return Either error message or result data
   */
  private def handleListFiles(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    try {
      Output.writeln(s"I/Q Server: Starting handleListFiles with params: $params")

      // Get all tracked files from Document_Model
      val trackedFiles = GUI_Thread.now {
        val models_map = Document_Model.get_models_map()
        Output.writeln(s"I/Q Server: Document_Model.get_models_map() returned ${models_map.size} models")

        // Get all open buffers for quick lookup
        val views = jEdit.getViews()
        val activeView = jEdit.getActiveView()
        val allBuffers = views.flatMap(_.getBuffers()).distinct
        val bufferPaths = allBuffers.map(_.getPath()).toSet

        Output.writeln(s"I/Q Server: Found ${views.length} views, ${allBuffers.length} buffers")

        // Process each model
        val processedFiles = models_map.map { case (node_name, model) =>
          val filePath = node_name.node  // Use same extraction as getAllTrackedFiles()
          val isOpen = model.isInstanceOf[Buffer_Model]
          val isTheory = node_name.is_theory
          val theoryName = if (isTheory) node_name.theory else ""

          Output.writeln(s"I/Q Server: Processing file: $filePath, isOpen: $isOpen, isTheory: $isTheory")

          // Get additional info for open files
          val (isModified, contentPreview, isInView, isActiveView) =
            if (isOpen) {
              val buffer = model.asInstanceOf[Buffer_Model].buffer
              val preview = if (buffer.getLength() > 100) {
                buffer.getText(0, 100).replace("\n", "\\n").replace("\r", "\\r")
              } else {
                buffer.getText(0, buffer.getLength()).replace("\n", "\\n").replace("\r", "\\r")
              }

              val isInAnyView = views.exists(_.getBuffers().contains(buffer))
              val isInActiveView = if (activeView != null) {
                activeView.getBuffer() == buffer
              } else {
                false
              }

              (buffer.isDirty(), preview, isInAnyView, isInActiveView)
            } else {
              (false, "", false, false)
            }

          // Calculate timing information for theory files
          val timingInfo = if (isTheory) {
            try {
              val (text_content, _) = getFileContentAndModel(filePath) match {
                case (Some(content), Some(model)) => (content, model)
                case _ => ("", model)
              }
              if (text_content.nonEmpty) {
                Some(calculateTimingInfo(model, text_content, includeDetailedCommands=false)) // Summary only for list_files
              } else {
                None
              }
            } catch {
              case ex: Exception =>
                Output.writeln(s"I/Q Server: Error calculating timing for $filePath: ${ex.getMessage}")
                None
            }
          } else {
            None
          }

          val baseMap = Map(
            "path" -> filePath,
            "node_name" -> node_name.toString,
            "is_open" -> isOpen,
            "is_theory" -> isTheory,
            "theory_name" -> theoryName,
            "is_modified" -> isModified,
            "content_preview" -> contentPreview,
            "is_in_view" -> isInView,
            "is_active_view" -> isActiveView,
            "model_type" -> (if (isOpen) "buffer" else "file")
          )

          // Add timing information if available
          timingInfo match {
            case Some(timing) => baseMap + ("timing" -> timing)
            case None => baseMap
          }
        }.toList

        Output.writeln(s"I/Q Server: Processed ${processedFiles.length} files")
        processedFiles
      }

      // Filter results based on parameters
      val filteredFiles = params.get("filter_open") match {
        case Some(true) =>
          val filtered = trackedFiles.filter(file => file("is_open").asInstanceOf[Boolean])
          Output.writeln(s"I/Q Server: Filtered to open files: ${filtered.length}")
          filtered
        case Some(false) =>
          val filtered = trackedFiles.filter(file => !file("is_open").asInstanceOf[Boolean])
          Output.writeln(s"I/Q Server: Filtered to non-open files: ${filtered.length}")
          filtered
        case _ =>
          Output.writeln(s"I/Q Server: No open filter applied: ${trackedFiles.length}")
          trackedFiles
      }

      val theoryFilteredFiles = params.get("filter_theory") match {
        case Some(true) =>
          val filtered = filteredFiles.filter(file => file("is_theory").asInstanceOf[Boolean])
          Output.writeln(s"I/Q Server: Filtered to theory files: ${filtered.length}")
          filtered
        case Some(false) =>
          val filtered = filteredFiles.filter(file => !file("is_theory").asInstanceOf[Boolean])
          Output.writeln(s"I/Q Server: Filtered to non-theory files: ${filtered.length}")
          filtered
        case _ =>
          Output.writeln(s"I/Q Server: No theory filter applied: ${filteredFiles.length}")
          filteredFiles
      }

      // Sort results if requested
      val sortedFiles = params.get("sort_by") match {
        case Some("path") => theoryFilteredFiles.sortBy(file => file("path").asInstanceOf[String])
        case Some("theory") => theoryFilteredFiles.sortBy(file => file("theory_name").asInstanceOf[String])
        case Some("type") => theoryFilteredFiles.sortBy(file => file("model_type").asInstanceOf[String])
        case _ => theoryFilteredFiles
      }

      Output.writeln(s"I/Q Server: Final sorted files count: ${sortedFiles.length}")

      val result = Map(
        "files" -> sortedFiles,
        "total_count" -> sortedFiles.length,
        "open_count" -> sortedFiles.count(f => f("is_open").asInstanceOf[Boolean]),
        "theory_count" -> sortedFiles.count(f => f("is_theory").asInstanceOf[Boolean])
      )

      Output.writeln(s"I/Q Server: Returning response with ${sortedFiles.length} files")
      Right(result)
    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Error listing files: ${ex.getMessage}")
        ex.printStackTrace()
        Left(s"Error listing files: ${ex.getMessage}")
    }
  }

  /**
   * Gets information about the current view in jEdit.
   *
   * @return A tuple containing (text content, buffer model, caret position)
   */
  private def getCurrentView(): (String, Buffer_Model, Int) = {
    GUI_Thread.now {
      val activeView = jEdit.getActiveView()
      val buffer = activeView.getBuffer()
      val buffer_model = Document_Model.get_model(buffer).get
      val text = JEdit_Lib.buffer_text(buffer)
      val textArea = activeView.getTextArea()
      val caretPos = textArea.getCaretPosition()

      (text, buffer_model, caretPos)
    }
  }

  private def handleGetCommandCore(params: Map[String, Any]):
      Either[(List[Map[String, Any]], Map[String, Any]), String] = {
    Output.writeln(s"I/Q Server: Processing get_command core request")

    val filePath = params.get("path") match {
      case Some(value: String) if value.trim.nonEmpty =>
        val partialPath = value.trim
        IQUtils.autoCompleteFilePath(partialPath) match {
          case Right(fullPath) => Some(fullPath)
          case Left(errorMsg) => return Right(errorMsg)
        }
      case _ => None
    }

    // Extract parameters

    val mode = params.get("mode") match {
      case Some(value: String) if value.trim.nonEmpty => Some(value.trim)
      case _ => None
    }

    val xmlResultFile = params.get("xml_result_file") match {
      case Some(value: String) if value.trim.nonEmpty => Some(value.trim)
      case _ => None
    }

    val startLineOpt = params.get("start_line") match {
      case Some(n: Number) => Some(n.intValue())
      case _ => None
    }

    val endLineOpt = params.get("end_line") match {
      case Some(n: Number) => Some(n.intValue())
      case _ => None
    }

    val startOffsetOpt = params.get("start_offset") match {
      case Some(n: Number) => Some(n.intValue())
      case _ => None
    }

    val endOffsetOpt = params.get("end_offset") match {
      case Some(n: Number) => Some(n.intValue())
      case _ => None
    }

    val (content, model, startOffsetRaw, endOffsetRaw) = (mode, filePath, startLineOpt, endLineOpt, startOffsetOpt, endOffsetOpt) match {
      case (Some ("line"), Some (filePath), Some (startLine), Some(endLine), _, _) =>
        // Lookup buffer associated with file
        val (content, model) = getFileContentAndModel(filePath) match {
          case (Some(content), Some(model)) => (content, model)
          case _ => return Right(s"File $filePath is not tracked by Isabelle/jEdit")
        }
        val startOffset = lineNumberToOffset(content, startLine)
        val endOffset = lineNumberToOffset(content, endLine, increment=true, withLastNewLine=false)
        (content, model, startOffset, endOffset)

      case (Some ("offset"), Some (filePath), _, _, Some(startOffset), Some(endOffset)) =>
        val (content, model) = getFileContentAndModel(filePath) match {
          case (Some(content), Some(model)) => (content, model)
          case _ => return Right(s"File $filePath is not tracked by Isabelle/jEdit")
        }
        (content, model, startOffset, endOffset)

      case (Some ("current"), filePathOpt, None, None, None, None) => // Current buffer
        val (content, model, caretPos) = getCurrentView()

        filePathOpt match {
          case Some(filePath) =>
            // If filePath is given, check that it matches the current model
            val pathModel = getFileContentAndModel(filePath) match {
              case (_, Some(model)) => model
              case _ => return Right (s"File $filePath is not tracked by Isabelle/jEdit")
            }

            if (model.node_name != pathModel.node_name) {
              return Right (s"The provided filename $filePath does not match the currently open buffer (node: ${pathModel.node_name})")
            }
          case _ =>
        }

        (content, model, caretPos, caretPos + 1)

      case _ => return Right(s"Unknown mode $mode or invalid parameters for mode.")
    }
    val (startOffset, endOffset) =
      IQLineOffsetUtils.normalizeOffsetRange(startOffsetRaw, endOffsetRaw, content.length)

    val waitUntilProcessed = params.get("wait_until_processed") match {
      case Some(value: Boolean) => value
      case _ => false
    }

    val timeoutMs = params.get("timeout") match {
      case Some(value: Number) => Some(value.longValue())
      case _ => Some(5000L) // Default timeout of 5 seconds
    }

    val timeoutPerCommandMs: Option[Int] = params.get("timeout_per_command") match {
      case Some(value: Number) => Some(value.intValue())
      case _ => Some(5000) // Default per-command timeout of 5 seconds
    }

    Output.writeln(s"I/Q Server: Parameters - mode: $mode, startLine: $startLineOpt, endLine: $endLineOpt, startOffset: $startOffsetOpt, endOffset: $endOffsetOpt, filePath: $filePath, waitUntilProcessed: $waitUntilProcessed, timeout: $timeoutMs, timeout_per_command: ${timeoutPerCommandMs}ms")

    // Determine mode and execute (with optional waiting loop)
    val startTime = System.currentTimeMillis()
    val pollIntervalMs = 500L  // 500ms
    var commandInfos: List[CommandInfo] = List.empty
    var shouldContinue = true
    var loopCount = 0
    var perCommandTimerStart: Option[Long] = None

    if (waitUntilProcessed) {
      Output.writeln(s"I/Q Server: wait_until_processed=true detected - entering polling loop with ${timeoutMs.getOrElse(0L)}ms timeout")
    } else {
      Output.writeln(s"I/Q Server: wait_until_processed=false - single retrieval mode")
    }

    while (shouldContinue) {
      loopCount += 1
      if (waitUntilProcessed) {
        Output.writeln(s"I/Q Server: Polling loop iteration $loopCount - retrieving commands...")
      }

      // Get commands using the same logic regardless of waiting
      commandInfos = GUI_Thread.now {
        getCommandsInOffsetRange(model, content, startOffset, endOffset)
      }

      if (waitUntilProcessed) {
        Output.writeln(s"I/Q Server: Retrieved ${commandInfos.length} commands in iteration $loopCount")
      }

      // Check if we should continue waiting
      if (!waitUntilProcessed || commandInfos.isEmpty) {
        // Not waiting or no commands found - exit loop
        if (waitUntilProcessed && commandInfos.isEmpty) {
          Output.writeln(s"I/Q Server: No commands found - exiting wait loop")
        }
        shouldContinue = false
      } else {
        // Check if all commands are processed OR running too long
        val allCommandsProcessedOrRunning = commandInfos.forall { info =>
          val status = info.status("status_summary").toString
          status == "finished" || status == "canceled" || status == "failed" || status == "running"
        }

        if (allCommandsProcessedOrRunning && perCommandTimerStart.isEmpty) {
          perCommandTimerStart = Some(System.currentTimeMillis())
          Output.writeln(s"I/Q Server: All commands processed or running, starting per-command timer")
        }

        val allProcessed = commandInfos.forall { info =>
          val status = info.status("status_summary").toString
          status == "finished" || status == "canceled" || status == "failed"
        }

        if (allProcessed) {
          shouldContinue = false
        } else {
          // Check per-command timeout
          timeoutPerCommandMs match {
            case Some(perCmdTimeout) =>
              perCommandTimerStart match {
                case Some(timerStart) =>
                  val perCommandElapsed = System.currentTimeMillis() - timerStart
                  if (perCommandElapsed >= perCmdTimeout) {
                    Output.writeln(s"I/Q Server: Per-command timeout of ${perCmdTimeout}ms exceeded, aborting")
                    shouldContinue = false
                  }
                case None => // Timer not started yet
              }
            case None => // No per-command timeout set
          }

          // Check global timeout
          val timedOut = System.currentTimeMillis() - startTime >= timeoutMs.getOrElse(0L)

          if (timedOut) {
            Output.writeln(s"I/Q Server: Wait timeout reached after ${timeoutMs.getOrElse(0L)}ms and $loopCount iterations")
            shouldContinue = false
          } else {
            // Log status and wait before next poll
            val statusCounts = commandInfos.groupBy { info =>
              info.status.getOrElse("status_summary", "unknown").toString
            }.view.mapValues(_.size).toMap
            Output.writeln(s"I/Q Server: Iteration $loopCount - Status: ${statusCounts.map { case (k, v) => s"$k: $v" }.mkString(", ")} - waiting ${pollIntervalMs}ms...")
            Thread.sleep(pollIntervalMs)
          }
        }
      }
    }

    val finishedCount   = commandInfos.count { info => info.status("status_summary") == "finished" }
    val failedCount     = commandInfos.count { info => info.status("status_summary") == "failed" }
    val canceledCount   = commandInfos.count { info => info.status("status_summary") == "canceled" }
    val unfinishedCount = commandInfos.length - (finishedCount + failedCount + canceledCount)
    Output.writeln(s"I/Q Server: $finishedCount commands finished, $failedCount failed, $canceledCount canceled, $unfinishedCount unfinished")

    val totalElapsed = System.currentTimeMillis() - startTime
    if (waitUntilProcessed) {
      Output.writeln(s"I/Q Server: Wait loop completed after $loopCount iterations in ${totalElapsed}ms")
    }

    // Optionally dump XML results to file for all commands
    xmlResultFile match {
      case Some(filePath) =>
        try {
          val allXmlResults = commandInfos.flatMap(_.results_xml)
          dumpXmlResultsToFile(allXmlResults, filePath)
          Output.writeln(s"I/Q Server: XML results for ${commandInfos.length} commands dumped to $filePath")
        } catch {
          case ex: Exception =>
            Output.writeln(s"I/Q Server: Failed to dump XML results to file: ${ex.getMessage}")
        }
      case None =>
        Output.writeln(s"I/Q Server: No XML result file specified")
    }

    // Create command data array
    val commandInfosTrimmed = commandInfos.filter(_.command_source.trim.nonEmpty)
    val commandsData = commandInfosTrimmed.map { case info =>
      Map(
        "command_source" -> info.command_source,
        "command_type" -> info.command_type,
        "range" -> info.range,
        "results_text" -> info.results_text,
        "status" -> info.status,
        "path" -> info.file_path
      )
    }

    val summaryBuilder = scala.collection.mutable.Map[String, Any](
      "total_commands" -> commandInfosTrimmed.length,
      "commands_failed" -> failedCount,
      "commands_finished" -> finishedCount,
      "commands_canceled" -> canceledCount,
      "commands_unprocessed" -> unfinishedCount
    )
    xmlResultFile match {
      case Some(file: String) => summaryBuilder("xml_result_file") = file
      case _ =>
    }

    val summary = summaryBuilder.toMap

    Output.writeln(s"I/Q Server: Generated command data with ${commandInfos.length} commands")
    Left((commandsData, summary))
  }

  private def handleGetCommand(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    Output.writeln("handleGetCommand")
    try {
      val (commandsData, summary) = handleGetCommandCore(params) match {
        case Left (c,s) => (c,s)
        case Right (err) => return Left(s"handleGetCommandCore failed with error: $err")
      }

      // Check include_results parameter (default: false)
      val includeResults = params.get("include_results") match {
        case Some(value: Boolean) => value
        case _ => false
      }

      val result = Map(
        "content" -> commandsData,
        "summary" -> summary
      )

      if (includeResults) {
        // Original behavior: include results in response
        Output.writeln(s"I/Q Server: Generated command response with ${commandsData.length} commands")
        Right(result)
      } else {
        // New behavior: write full results to temp file and return trimmed response
        val fullJsonResponse = JSON.Format(Map("result" -> result))

        // Create temporary file and write full response
        val tempFile = Files.createTempFile("iq_command_results_", ".json")
        Files.write(tempFile, fullJsonResponse.getBytes("UTF-8"))

        // Create trimmed response by removing result fields from commands
        val trimmedCommandsData = commandsData.map { command =>
          command - "results_text"
        }

        val trimmedResult = Map(
          "content" -> trimmedCommandsData,
          "summary" -> summary,
          "full_results_file" -> tempFile.toString
        )

        Output.writeln(s"I/Q Server: Generated trimmed command response with ${commandsData.length} commands, full results written to ${tempFile.toString}")
        Right(trimmedResult)
      }
    } catch {
      case ex: RuntimeException =>
        Left(ex.getMessage)
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Unexpected error in handleGetCommand: ${ex.getMessage}")
        ex.printStackTrace()
        Left(s"Internal error: ${ex.getMessage}")
    }
  }

  private def determineCommandType(source: String): String = {
    val trimmed = source.trim
    if (trimmed.startsWith("lemma ") || trimmed.startsWith("theorem ") ||
        trimmed.startsWith("corollary ") || trimmed.startsWith("proposition ")) {
      "statement"
    } else if (trimmed.startsWith("proof") || trimmed == "proof") {
      "proof_start"
    } else if (trimmed.startsWith("apply ")) {
      "proof_method"
    } else if (trimmed.startsWith("by ")) {
      "proof_method"
    } else if (trimmed == "qed" || trimmed.startsWith("qed ")) {
      "proof_end"
    } else if (trimmed.startsWith("definition ") || trimmed.startsWith("fun ") ||
               trimmed.startsWith("primrec ")) {
      "definition"
    } else if (trimmed.startsWith("datatype ") || trimmed.startsWith("type_synonym ")) {
      "type_definition"
    } else if (trimmed.startsWith("import ") || trimmed.startsWith("theory ")) {
      "theory_structure"
    } else if (trimmed.startsWith("declare ") || trimmed.startsWith("notation ")) {
      "declaration"
    } else {
      "other"
    }
  }

  private def getCommandsInOffsetRange(model: Document_Model, content: String, startOffset: Int, endOffset: Int): List[CommandInfo] = {
    val node_name = model.node_name
    Output.writeln(s"I/Q Server: Getting commands in offset range $startOffset-$endOffset for node: $node_name")

    val snapshot = Document_Model.snapshot(model)
    val node = snapshot.get_node(node_name)

    val targetRange = Text.Range(startOffset, endOffset)

    // Get commands that intersect with the target range
    val commandsInRange = node.command_iterator(targetRange).toList

    Output.writeln(s"I/Q Server: Found ${commandsInRange.length} commands in line range")

    commandsInRange.zipWithIndex.map { case ((command, commandStart), index) =>
      val results = snapshot.command_results(command)
      val (resultsXml, resultsText) = extractBothXmlAndText(results)
      val commandType = determineCommandType(command.source)
      val rangeInfo = getCommandRangeInfo(content, command, commandStart)
      val commandStatus = getCommandStatus(command, snapshot)

      CommandInfo(
        file_path = node_name.toString,
        command_source = command.source,
        command_type = commandType,
        results_xml = resultsXml,
        results_text = resultsText,
        range = rangeInfo,
        status = commandStatus
      )
    }
  }

  private def getCommandRangeInfo(content: String, command: Command, commandStart: Int): Map[String, Any] = {
    // val node = snapshot.get_node(command.node_name)
    // val commandStart = node.command_start(command).getOrElse(0)
    val commandEnd = commandStart + command.range.length

    val lineDoc = Line.Document(content)
    // Convert absolute document offsets to line/column positions
    val startPos = lineDoc.position(commandStart)
    val endPos = lineDoc.position(commandEnd)

    Map(
      "start_line" -> (startPos.line + 1),      // Convert to 1-based
      "start_column" -> (startPos.column + 1),  // Convert to 1-based
      "end_line" -> (endPos.line + 1),
      "end_column" -> (endPos.column + 1),
      "text_start_offset" -> commandStart,
      "text_end_offset" -> commandEnd
    )
  }

  private def dumpXmlResultsToFile(xmlResults: List[String], filePath: String): Unit = {
    import java.io.{FileWriter, BufferedWriter}
    import java.nio.file.{Paths, Files}

    // Validate file path
    val path = Paths.get(filePath)
    if (!path.isAbsolute) {
      throw new IllegalArgumentException(s"File path must be absolute: $filePath")
    }

    // Create parent directories if they don't exist
    val parentDir = path.getParent
    if (parentDir != null && !Files.exists(parentDir)) {
      Files.createDirectories(parentDir)
    }

    // Write XML results to file
    val writer = new BufferedWriter(new FileWriter(filePath))
    try {
      writer.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n")
      writer.write("<isabelle_command_results>\n")
      writer.write(s"  <timestamp>${java.time.Instant.now()}</timestamp>\n")
      writer.write(s"  <result_count>${xmlResults.length}</result_count>\n")
      writer.write("  <results>\n")

      xmlResults.zipWithIndex.foreach { case (xmlResult, index) =>
        writer.write(s"    <result index=\"$index\">\n")
        writer.write("      <![CDATA[\n")
        writer.write(xmlResult)
        writer.write("\n      ]]>\n")
        writer.write("    </result>\n")
      }

      writer.write("  </results>\n")
      writer.write("</isabelle_command_results>\n")
    } finally {
      writer.close()
    }
  }

  private def extractRawXmlFromResults(results: Command.Results): List[String] = {
    results.iterator.map { case (_, xmlElem) => xmlElem.toString }.toList
  }

  private def extractTextContentFromResults(results: Command.Results): List[String] = {
    results.iterator.map { case (_, xmlElem) => XML.content(xmlElem).trim }
      .toList.filter(_.nonEmpty)
  }

  private def extractBothXmlAndText(results: Command.Results): (List[String], List[String]) = {
    val xmlResults = extractRawXmlFromResults(results)
    val textResults = extractTextContentFromResults(results)
    (xmlResults, textResults)
  }

  private def getCommandStatus(command: Command, snapshot: Document.Snapshot): Map[String, Any] = {
    try {
      // Get all command states
      val states = snapshot.state.command_states(snapshot.version, command)
      val status = Document_Status.Command_Status.merge(states.iterator.map(_.document_status))

      // Extract timing information from status - use the new timings API
      val timing_seconds = status.timings.sum(Date.now()).seconds

      // Debug: log the actual status values
      Output.writeln(s"I/Q Server: Command status debug - unprocessed: ${status.is_unprocessed}, running: ${status.is_running}, finished: ${status.is_finished}, failed: ${status.is_failed}, terminated: ${status.is_terminated}, forks: ${status.forks}, runs: ${status.runs}, timing: ${timing_seconds}s")

      // Improved status determination logic
      val final_status_summary = {
        if (status.is_failed) "failed"
        else if (status.is_canceled) "canceled"
        else if (status.is_running) "running"
        else if (status.is_finished) "finished"
        else if (status.is_terminated && !status.is_failed && !status.is_running) "finished"  // Additional check
        else if (status.is_unprocessed) "unprocessed"
        else {
          // If none of the above, but we have some processing activity, consider it finished
          if (status.runs > 0 || status.forks > 0) "finished"
          else "unknown"
        }
      }

      Map(
        "status_summary" -> final_status_summary,
        "timing_seconds" -> formatDecimal(timing_seconds)
      )
    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Error getting command status: ${ex.getMessage}")
        Map(
          "status_summary" -> "error",
          "error" -> ex.getMessage
        )
    }
  }

  private def handleGetDocumentInfo(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    val filePath = params.getOrElse("path", "").toString match {
      case path if path.trim.nonEmpty =>
        IQUtils.autoCompleteFilePath(path.trim) match {
          case Right(fullPath) => fullPath
          case Left(errorMsg) => return Left(errorMsg)
        }
      case _ => return Left("Missing required parameter: path")
    }

    val includeErrors = params.get("include_errors") match {
      case Some(value: Boolean) => value
      case _ => true  // Default to true
    }

    val includeWarnings = params.get("include_warnings") match {
      case Some(value: Boolean) => value
      case _ => false  // Default to false
    }

    val timingThresholdMs = params.get("timing_threshold_ms") match {
      case Some(value: Number) => value.intValue()
      case _ =>
        Output.writeln(s"I/Q Server: No timing_threshold parameter provided, using 3000ms default")
        3000
    }

    val waitUntilProcessed = params.get("wait_until_processed") match {
      case Some(value: Boolean) => value
      case _ => false  // Default to false
    }

    val timeout_ms = params.get("timeout") match {
      case Some(value: Number) => Some(value.intValue())
      case _ => None
    }

    val timeoutPerCommandMs: Option[Int] = params.get("timeout_per_command") match {
      case Some(value: Number) => Some(value.intValue())
      case _ => Some(5000) // Default per-command timeout of 5 seconds
    }

    Output.writeln(s"I/Q Server: Getting document info for file: $filePath (errors: $includeErrors, warnings: $includeWarnings, timing_threshold: ${timingThresholdMs}ms, wait_until_processed: $waitUntilProcessed, timeout: ${timeout_ms} ms, timeout_per_command: ${timeoutPerCommandMs}ms)")

    // If wait_until_processed is requested and this is a theory file, wait for completion
    if (waitUntilProcessed) {
      val model = GUI_Thread.now { getFileContentAndModel(filePath) } match {
        case (Some(_), Some(model)) => model
        case _ => return Left(s"Could not get document information for file: $filePath")
      }

      Output.writeln(s"I/Q Server: Requesting theory completion for: ${model.node_name}")
      waitForTheoryCompletion(model, timeout_ms, timeoutPerCommandMs)
    }

    val documentInfo = GUI_Thread.now {
      getDocumentInfoForFile(filePath, includeErrors, includeWarnings, timingThresholdMs)
    }

    documentInfo match {
      case Some(info) => Right(info)
      case None => Left(s"Could not get document information for file: $filePath")
    }
  }

  /**
    * Gets the content of a file using Document_Model when available, falling back to file system.
    * Also returns the model if one exists.
    *
    * @param filePath The full real path to the file
    * @return A tuple containing:
    *         - Option[String]: The file content if successful, None otherwise
    *         - Option[Document_Model]: The model if one exists, None otherwise
    */
  private def getFileContentAndModel(filePath: String): (Option[String], Option[Document_Model]) = {
    try {
      // Convert the file path to a node name
      val nodeName = PIDE.resources.node_name(filePath)

      // Try to get a model for this node
      Document_Model.get_model(nodeName) match {
        case Some(model) =>
          // Get content based on model type
          val content = model match {
            case buffer_model: Buffer_Model => JEdit_Lib.buffer_text(buffer_model.buffer)
            case file_model: File_Model => file_model.content.text
          }
          (Some(content), Some(model))

        case None =>
          // No model - read directly from file system
          val file = new java.io.File(filePath)
          if (file.exists() && file.canRead()) {
            val source = scala.io.Source.fromFile(file)
            try {
              (Some(source.mkString), None)
            } finally {
              source.close()
            }
          } else {
            (None, None)
          }
      }
    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Error reading file content: ${ex.getMessage}")
        (None, None)
    }
  }

  /**
    * Gets the content of a file using Document_Model when available, falling back to file system.
    *
    * @param filePath The full real path to the file
    * @return - Option[String]: The file content if successful, None otherwise
    */
  private def getFileContent(filePath: String): Option[String] = {
    getFileContentAndModel(filePath)._1
  }

  private def getBufferModel(filePath: String): Option [(String, Buffer_Model)] = {
    getFileContentAndModel(filePath) match {
      case (Some(content), Some(model: Buffer_Model)) => Some (content, model)
      case _ => None
    }
  }

  private def lineNumberToOffset(text: String, line: Int, increment: Boolean = false, withLastNewLine: Boolean = true): Int = {
    IQLineOffsetUtils.lineNumberToOffset(
      text,
      line,
      increment = increment,
      withLastNewLine = withLastNewLine
    )
  }

  /**
   * Calculate timing information for a theory file.
   *
   * @param model The document model
   * @param text_content The file content
   * @param timingThresholdMs Only include commands above this threshold in detailed list
   * @param includeDetailedCommands Whether to include the detailed commands list
   * @return Map containing timing information
   */
  private def calculateTimingInfo(model: Document_Model, text_content: String, timingThresholdMs: Int = 0, includeDetailedCommands: Boolean = true): Map[String, Any] = {
    val node_name = model.node_name
    val snapshot = Document_Model.snapshot(model)
    val state = snapshot.state
    val version = snapshot.version
    val node = snapshot.get_node(node_name)

    // Calculate timing information using Node_Status (Overall_Timing was removed in Isabelle2025-2)
    val node_status = Document_Status.Node_Status.make(Date.now(), state, version, node_name, threshold = Time.zero)

    val baseTimingInfo = Map(
      "total_seconds" -> formatDecimal(node_status.cumulated_time.seconds),
      "total_command_count" -> node_status.command_timings.size
    )

    if (!includeDetailedCommands) {
      // For list_files, only return summary information
      baseTimingInfo
    } else {
      // For get_document_info, include detailed command information
      // Create a Line.Document for line/column position conversion
      val line_document = Line.Document(text_content)

      // Function to convert offsets to line numbers
      def offsetToLine(offset: Int): Int = {
        try {
          val pos = line_document.position(offset)
          pos.line + 1 // Convert to 1-based line numbers
        } catch {
          case _: Exception => 0 // Fallback if conversion fails
        }
      }

      // Filter commands for detailed display based on user threshold
      val threshold_time = Time.ms(timingThresholdMs)
      val commands_above_threshold = node_status.command_timings.filter { case (_, timings) =>
        timings.sum(Date.now()) >= threshold_time
      }

      Output.writeln(s"I/Q Server: calculateTimingInfo - timingThreshold=$timingThresholdMs ms")

      baseTimingInfo ++ Map(
        "timing_threshold_ms" -> timingThresholdMs,
        "commands_with_timing" -> commands_above_threshold.map { case (cmd, timings) =>
          // Get the absolute document offset for this command
          val commandStart = node.command_start(cmd).getOrElse(0)
          val start_line = offsetToLine(commandStart)
          val timing = timings.sum(Date.now())
          Map(
            "line" -> start_line,
            "source_preview" -> cmd.source.take(50), // First 50 chars for identification
            "timing_seconds" -> formatDecimal(timing.seconds)
          )
        }.toList.sortBy(_.apply("timing_seconds").asInstanceOf[Double]).reverse // Sort by timing descending
      )
    }
  }

  private def getDocumentInfoForFile(filePath: String, includeErrors: Boolean, includeWarnings: Boolean, timingThresholdMs: Int): Option[Map[String, Any]] = {

    val (text_content, model) = getFileContentAndModel(filePath) match {
      case (Some(content), Some(model)) => (content, model)
      case _ => return None
    }

    // Get a snapshot of the document
    val snapshot = Document_Model.snapshot(model)
    val result = scala.collection.mutable.Map[String, Any]()
    val nodeName = model.node_name

    result("path") = filePath
    result("node_name") = nodeName.toString
    result("is_theory") = nodeName.is_theory
    result("is_open") = model.isInstanceOf[Buffer_Model]
    result("model_type") = if (model.isInstanceOf[Buffer_Model]) "buffer" else "file"

    val node_name = model.node_name
    val state = snapshot.state
    val version = snapshot.version
    val node_status = Document_Status.Node_Status.make(Date.now(), state, version, node_name)

    result("status") = Map(
      "is_processed" -> node_status.terminated,
      "errors" -> node_status.failed,
      "warnings" -> node_status.warned,
      "running" -> node_status.running,
      "finished" -> node_status.finished,
      "unprocessed" -> node_status.unprocessed
    )

    // Add timing information using the extracted function
    result("timing") = calculateTimingInfo(model, text_content, timingThresholdMs=timingThresholdMs, includeDetailedCommands = true)

    // Add error and warning details if requested
    if (includeErrors || includeWarnings) {
      // Create a Line.Document for line/column position conversion
      val line_document = Line.Document(text_content)

      // Create the appropriate rendering
      val rendering = model match {
        case buffer_model: Buffer_Model =>
          // For Buffer_Model, use JEdit_Rendering
          JEdit_Rendering(snapshot, buffer_model, PIDE.options.value)
        case _ =>
          // For File_Model, use standard Rendering with session
          new Rendering(snapshot, PIDE.options.value, PIDE.session)
      }

      val text_range = Text.Range(0, snapshot.node.source.length)

      // Function to convert offsets to line/column positions
      def offsetToLineCol(offset: Int): (Int, Int) = {
        try {
          val pos = line_document.position(offset)
          (pos.line + 1, pos.column + 1) // Convert to 1-based
        } catch {
          case _: Exception => (0, 0) // Fallback if conversion fails
        }
      }

      if (includeErrors) {
        // Get all errors in the file
        val errors = rendering.errors(text_range)

        // Convert errors to structured format
        val errorList = errors.map { error_markup =>
          val range = error_markup.range
          val xml_elem = error_markup.info
          val message = XML.content(xml_elem.body).trim
          val (start_line, _) = offsetToLineCol(range.start)

          Map(
            "message" -> message,
            "severity" -> "error",
            "line" -> start_line,
            "markup" -> xml_elem.markup.name
          )
        }

        result("errors") = errorList
        result("error_count") = errorList.length
      }

      if (includeWarnings) {
        // Get all warnings in the file
        val warnings = rendering.warnings(text_range)

        // Convert warnings to structured format
        val warningList = warnings.map { warning_markup =>
          val range = warning_markup.range
          val xml_elem = warning_markup.info
          val message = XML.content(xml_elem.body).trim

          // Convert text offsets to line/column positions
          val (start_line, start_col) = offsetToLineCol(range.start)
          val (end_line, end_col) = offsetToLineCol(range.stop)

          Map(
            "message" -> message,
            "severity" -> "warning",
            "line" -> start_line,
            "markup" -> xml_elem.markup.name
          )
        }

        result("warnings") = warningList
        result("warning_count") = warningList.length
      }
    }

    // Set default counts if not included
    if (!result.contains("error_count")) result("error_count") = 0
    if (!result.contains("warning_count")) result("warning_count") = 0

    Some(result.toMap)
  }

  private def handleOpenFile(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    val createIfMissing = params.getOrElse("create_if_missing", "false").toString.toBoolean

    val filePath = params.getOrElse("path", "").toString match {
      case path if path.trim.nonEmpty =>
        IQUtils.autoCompleteFilePath(path.trim, trackedOnly = false, allowNonexisting = createIfMissing) match {
          case Right(fullPath) => fullPath
          case Left(errorMsg) => return Left(errorMsg)
        }
      case _ => return Left("path parameter is required")
    }
    val view = params.getOrElse("view", "true").toString.toBoolean

    Output.writeln(s"I/Q Server: Opening file: $filePath, create_if_missing: $createIfMissing, view: $view")

    try {
      val result = GUI_Thread.now {
        if (view) {
          openFileInEditor(filePath, createIfMissing)
        } else {
          openFileInBuffer(filePath, createIfMissing)
        }
      }

      // TODO: How do we make sure we don't return to the caller before
      // the file has been opened?

      val response = Map(
        "path" -> result("path"),
        "created" -> result("created").toBoolean,
        "opened" -> result("opened").toBoolean,
        "in_view" -> result.getOrElse("in_view", view.toString).toBoolean,
        "message" -> "File opened successfully"
      )
      Right(response)
    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Error in handleOpenFile: ${ex.getMessage}")
        Left(s"Error opening file: ${ex.getMessage}")
    }
  }

  private def handleCreateFile(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    val filePath = params.getOrElse("path", "").toString
    val content = params.getOrElse("content", "").toString
    val overwriteIfExists = params.getOrElse("overwrite_if_exists", "false").toString.toBoolean
    val view = params.getOrElse("view", "true").toString.toBoolean

    Output.writeln(s"I/Q Server: Creating file: $filePath, overwrite_if_exists: $overwriteIfExists, view: $view")

    if (filePath.isEmpty) {
      return Left("path parameter is required")
    }

    try {
      val result = GUI_Thread.now {
        if (view) {
          createFileWithContentAndOpen(filePath, content, overwriteIfExists)
        } else {
          createFileWithContentInBuffer(filePath, content, overwriteIfExists)
        }
      }

      val response = Map(
        "path" -> result("path"),
        "created" -> result("created").toBoolean,
        "overwritten" -> result("overwritten").toBoolean,
        "opened" -> result("opened").toBoolean,
        "in_view" -> result.getOrElse("in_view", view.toString).toBoolean,
        "message" -> "File created successfully"
      )
      Right(response)
    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Error in handleCreateFile: ${ex.getMessage}")
        Left(s"Error creating file: ${ex.getMessage}")
    }
  }

  private def handleReadTheoryFile(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    try {
      val filePath = params.getOrElse("path", "").toString match {
        case path if path.trim.nonEmpty =>
          IQUtils.autoCompleteFilePath(path.trim) match {
            case Right(fullPath) => fullPath
            case Left(errorMsg) => return Left(errorMsg)
          }
        case _ => return Left("path parameter is required")
      }

      Output.writeln(s"I/Q Server: Params $params")

      val mode_opt = params.get("mode")
      Output.writeln(s"I/Q Server: Reading theory file: $filePath in mode $mode_opt")

      val mode = mode_opt match {
        case Some(mode: String) => mode
        case _ => "Unknown"
      }

      Output.writeln(s"I/Q Server: Reading theory file: $filePath in $mode mode")

      val result = mode match {
        case "Line" =>

          val startLine: Int = params.get("start_line") match {
            case Some(line: Int) => line
            case _ => 1
          }

          val endLine: Int = params.get("end_line") match {
            case Some(line: Int) => line
            case _ => -1
          }

          // Delegate to existing resource read logic
          GUI_Thread.now {
            readTheoryFile(filePath, startLine, endLine)
          }
        case "Search" =>
          val contextLines = params.get("context_lines") match {
            case Some(lines: Number) => lines.intValue()
            case Some(lines: String) => try { lines.toInt } catch { case _: Exception => 0 }
            case _ => 0
          }
          params.get("pattern") match {
            case Some(pattern: String) =>
              GUI_Thread.now {
                searchTheoryFile(filePath, pattern, contextLines)
              }
            case _ => return Left("`pattern` argument mandatory for mode 'Pattern'")
          }
        case _ => return Left("Unknown mode")
      }

      result match {
        case Some(content) => Right(Map("content" -> content))
        case None => Left(s"Failed to read theory file: $filePath")
      }
    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Error in handleReadTheoryFile: ${ex.getMessage}")
        Left(s"Error reading theory file: ${ex.getMessage}")
    }
  }

  private def handleWriteTheoryFile(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    // Parameter extraction
    val filePath = params.getOrElse("path", "").toString match {
      case path if path.trim.nonEmpty =>
        IQUtils.autoCompleteFilePath(path.trim) match {
          case Right(fullPath) => fullPath
          case Left(errorMsg) => return Left(errorMsg)
        }
      case _ => return Left("path parameter is required")
    }

    val waitUntilProcessed = params.get("wait_until_processed") match {
      case Some(value: Boolean) => value
      case _ => true
    }

    val command = params.getOrElse("command", "").toString
    if (command.isEmpty) {
      return Left("command parameter is required")
    }

    val timeoutMs = params.get("timeout") match {
      case Some(value: Number) => Some(value.longValue())
      case _ => Some(2500L) // Default timeout of 2.5 seconds
    }

    val timeoutPerCommandMs: Option[Int] = params.get("timeout_per_command") match {
      case Some(value: Number) => Some(value.intValue())
      case _ => Some(5000) // Default per-command timeout of 5 seconds
    }

    // Lookup buffer associated with file
    // We currently require that the file is opened in jEdit
    val (content, buffer_model) = getBufferModel(filePath) match {
      case Some (content, model) => (content, model)
      case _ => return Left(s"$filePath is not opened in jEdit")
    }

    val (startOffsetRaw, endOffsetRaw, text): (Int, Int, String) = command match {
      case "line" =>
        val new_str: String = params.get("new_str") match {
          case Some(s: String) => s
          case _ => return Left("new_str parameter is required for command 'str_replace'")
        }

        val startLine: Int = params.get("start_line") match {
          case Some(line: Int) => line
          case _ => return Left("start_line parameter is required for command 'line'")
        }

        val endLine: Int = params.get("end_line") match {
          case Some(line: Int) => line
          case _ => return Left("end_line parameter is required for command 'line'")
        }

        val startOffset = lineNumberToOffset(content, startLine)
        val endOffset = lineNumberToOffset(content, endLine, increment=true, withLastNewLine=false)

        (startOffset, endOffset, new_str)

      case "str_replace" =>
        val old_str: String = params.get("old_str") match {
          case Some(s: String) => s
          case _ => return Left("old_str parameter is required for command 'str_replace'")
        }

        val new_str: String = params.get("new_str") match {
          case Some(s: String) => s
          case _ => return Left("new_str parameter is required for command 'str_replace'")
        }

        val startOffset = IQUtils.findUniqueSubstringOffset(content, old_str) match {
          case Right(offset) => offset
          case Left(IQUtils.SubstringNotFound) =>
            return Left(s"Substring not found: '$old_str'")
          case Left(IQUtils.SubstringNotUnique) =>
            return Left(s"Substring appears multiple times: '$old_str'")
          case Left(IQUtils.SubstringEmpty) =>
            return Left("old_str parameter cannot be empty")
        }

        val endOffset = startOffset + old_str.length

        (startOffset, endOffset, new_str)

      case "insert" =>
        val new_str: String = params.get("new_str") match {
          case Some(s: String) => s
          case _ => return Left("new_str parameter is required for command 'insert'")
        }

        val insertLine: Int = params.get("insert_line") match {
          case Some(line: Int) => line
          case _ => return Left("insert_line parameter is required for command 'insert'")
        }

        val startOffset = lineNumberToOffset(content, insertLine + 1) // +1 because we insert _after_ the line
        (startOffset, startOffset, new_str)

      case _ => return Left(s"command $command not implemented")
    }

    val (startOffset, endOffset) =
      IQLineOffsetUtils.normalizeOffsetRange(startOffsetRaw, endOffsetRaw, content.length)

    Output.writeln(s"I/Q Server: Writing to theory file: $filePath (waitUntilProcessed: $waitUntilProcessed, timeout: ${timeoutMs.getOrElse(0)}ms, range: $startOffset-$endOffset)")

    // Delegate to existing resource write logic
    GUI_Thread.now {
      IQUtils.replaceTextInBuffer(buffer_model, text, startOffset, endOffset)
    }

    // Wait until the edit has been processed (stable snapshot = no pending edits)
    IQUtils.blockOnStableSnapshot(buffer_model)

    Output.writeln(s"I/Q Server: Auto-calling get_command for modified range in $filePath")

    val xml_result_file = Files.createTempFile("tmp_result", ".xml").toAbsolutePath.toString
    val newEndOffset: Int = endOffset + text.length

    // Create parameters for get_command call - use current command mode for now
    val getCommandParams = scala.collection.mutable.Map[String, Any](
      "path" -> filePath,
      "mode" -> "offset",
      "start_offset" -> startOffset,
      "end_offset" -> newEndOffset,
      "xml_result_file" -> xml_result_file,
      "wait_until_processed" -> waitUntilProcessed,
      "timeout" -> timeoutMs.getOrElse(5000L),
      "timeout_per_command" -> timeoutPerCommandMs.getOrElse(5000)
    )

    // Call get_command internally
    val (commands, summary) = handleGetCommandCore(getCommandParams.toMap) match {
      case Left (c,s) => (c,s)
      case Right (err) => return Left(f"handleGetCommandCore failed with $err")
    }

    Right(Map("commands" -> commands, "summary" -> summary))
  }

  private def openFileCommon(filePath: String, createIfMissing: Boolean, inView: Boolean): Map[String, String] = {
    val file = new java.io.File(filePath)
    var fileCreated = false

    if (!file.exists() && createIfMissing) {
      // Create empty file without any default content
      val parentDir = file.getParentFile
      if (parentDir != null && !parentDir.exists()) {
        parentDir.mkdirs()
      }
      file.createNewFile()
      fileCreated = true
      Output.writeln(s"I/Q Server: Created empty file${if (inView) "" else " for buffer"}: $filePath")
    } else if (!file.exists()) {
      throw new java.io.FileNotFoundException(s"File does not exist: $filePath")
    }

    if (inView) {
      val views = jEdit.getViews()
      if (views.isEmpty) {
        throw new Exception("No jEdit views available to display the file")
      }

      val view = views(0)
      val buffer = jEdit.openFile(view, filePath)
      if (buffer == null) {
        throw new Exception(s"Failed to open file in jEdit: $filePath")
      }

      view.setBuffer(buffer)
      view.getTextArea.requestFocus()
      Output.writeln(s"I/Q Server: Opened file in jEdit: $filePath")
    } else {
      // Read file content and provide it to document model
      val content = if (file.exists()) {
        scala.io.Source.fromFile(file, "UTF-8").mkString
      } else {
        ""
      }

      val node_name = PIDE.resources.node_name(filePath)
      Document_Model.provide_files(PIDE.session, List((node_name, content)))

      Output.writeln(s"I/Q Server: Provided file to buffer: $filePath")
    }

    Map(
      "path" -> filePath,
      "created" -> fileCreated.toString,
      "opened" -> "true",
      "in_view" -> inView.toString
    )
  }

  private def openFileInEditor(filePath: String, createIfMissing: Boolean): Map[String, String] = {
    openFileCommon(filePath, createIfMissing, inView = true)
  }

  private def openFileInBuffer(filePath: String, createIfMissing: Boolean): Map[String, String] = {
    openFileCommon(filePath, createIfMissing, inView = false)
  }

  private def createFileWithContent(file: java.io.File, filePath: String, content: String): Unit = {
    val parentDir = file.getParentFile
    if (parentDir != null && !parentDir.exists()) {
      parentDir.mkdirs()
    }

    val writer = new java.io.FileWriter(file)
    try {
      if (content.nonEmpty) {
        writer.write(content)
      } else if (filePath.endsWith(".thy")) {
        val theoryName = file.getName.stripSuffix(".thy")
        val template = s"""theory $theoryName
imports Main
begin

(* Add your definitions and proofs here *)

end"""
        writer.write(template)
      }
    } finally {
      writer.close()
    }
  }

  private def createFileWithContentCommon(filePath: String, content: String, overwriteIfExists: Boolean, inView: Boolean): Map[String, String] = {
    val file = new java.io.File(filePath)
    var fileCreated = false
    var fileOverwritten = false

    if (file.exists() && !overwriteIfExists) {
      throw new Exception(s"File already exists and overwrite_if_exists is false: $filePath")
    } else if (file.exists() && overwriteIfExists) {
      fileOverwritten = true
      Output.writeln(s"I/Q Server: Overwriting existing file${if (inView) "" else " for buffer"}: $filePath")
    } else {
      fileCreated = true
      Output.writeln(s"I/Q Server: Creating new file${if (inView) "" else " for buffer"}: $filePath")
    }

    // Create the file with content
    createFileWithContent(file, filePath, content)

    if (inView) {
      // Open the file in jEdit
      val views = jEdit.getViews()
      if (views.isEmpty) {
        throw new Exception("No jEdit views available to display the file")
      }

      val view = views(0)
      val buffer = jEdit.openFile(view, filePath)
      if (buffer == null) {
        throw new Exception(s"Failed to open file in jEdit: $filePath")
      }

      view.setBuffer(buffer)
      view.getTextArea.requestFocus()
      Output.writeln(s"I/Q Server: Opened file in jEdit: $filePath")
    } else {
      // Provide the file to document model (buffer only, no view)
      val node_name = PIDE.resources.node_name(filePath)
      Document_Model.provide_files(PIDE.session, List((node_name, content)))

      Output.writeln(s"I/Q Server: Provided file to buffer: $filePath")
    }

    Map(
      "path" -> filePath,
      "created" -> fileCreated.toString,
      "overwritten" -> fileOverwritten.toString,
      "opened" -> "true",
      "in_view" -> inView.toString
    )
  }

  private def createFileWithContentAndOpen(filePath: String, content: String, overwriteIfExists: Boolean): Map[String, String] = {
    createFileWithContentCommon(filePath, content, overwriteIfExists, inView = true)
  }

  private def createFileWithContentInBuffer(filePath: String, content: String, overwriteIfExists: Boolean): Map[String, String] = {
    createFileWithContentCommon(filePath, content, overwriteIfExists, inView = false)
  }

  // Helper methods
  private def findViewForFile(filePath: String): Option[View] = {
    val views = jEdit.getViews()
    views.find { view =>
      val buffer = view.getBuffer()
      val bufferPath = buffer.getPath()

      // Try exact match first
      if (bufferPath == filePath) {
        true
      } else {
        // Try canonical path comparison
        try {
          val file1 = new java.io.File(bufferPath).getCanonicalPath
          val file2 = new java.io.File(filePath).getCanonicalPath
          file1 == file2
        } catch {
          case _: Exception => false
        }
      }
    }
  }

  /**
    * Format a range of lines with line numbers and optional highlighting
    *
    * @param lines Array of text lines
    * @param startLine Starting line index (0-based)
    * @param endLine Ending line index (0-based)
    * @param highlightLine Optional line index to highlight with an arrow (0-based)
    * @return Formatted string with line numbers and highlighting
    */
  private def formatLinesWithNumbers(
    lines: Array[String],
    startLine: Int,
    endLine: Int,
    highlightLine: Option[Int] = None
  ): String = {
    IQLineOffsetUtils.formatLinesWithNumbers(lines, startLine, endLine, highlightLine)
  }

  private def readTheoryFile(filePath: String, startLine: Int, endLine: Int): Option[String] = {
    // Get file content
    val content = getFileContent(filePath) match {
      case Some(content: String) => content
      case _ => return None
    }

    val lines = IQLineOffsetUtils.splitLines(content)
    val totalLines = lines.length
    val (startAdjusted, endAdjusted) =
      IQLineOffsetUtils.normalizeLineRange(totalLines, startLine, endLine)

    Some(formatLinesWithNumbers(lines, startAdjusted, endAdjusted, None))
  }

  /**
   * Search for a pattern in a theory file and return matching lines with context
   *
   * @param filePath The full real path to the file
   * @param pattern The pattern to search for
   * @param contextLines Number of context lines to include around matches
   * @return Option containing the search results if successful, None otherwise
   */
  private def searchTheoryFile(filePath: String, pattern: String, contextLines: Int): Option[List[Map[String, Any]]] = {
    // Get file content
    val content = getFileContent(filePath) match {
      case Some(content: String) => content
      case _ => return None
    }

    // Split content into lines
    val lines = IQLineOffsetUtils.splitLines(content)
    val totalLines = lines.length
    val safeContextLines = math.max(0, contextLines)

    // Create a regex pattern (case insensitive)
    val regex = s"(?i)$pattern".r

    // Find matching lines
    val matchingLineIndices = lines.zipWithIndex.collect {
      case (line, idx) if regex.findFirstIn(line).isDefined => idx
    }

    // Create an array of match objects with context
    val matches = matchingLineIndices.map { lineIdx =>
      val lineNum = lineIdx + 1  // Convert to 1-based

      // Calculate context range
      val startLine = math.max(0, lineIdx - safeContextLines)
      val endLine = math.min(totalLines - 1, lineIdx + safeContextLines)

      // Create match object - use a List of tuples instead of Map for better JSON serialization
      Map(
        "line_number" -> lineNum,
        "context" -> formatLinesWithNumbers(lines, startLine, endLine, Some(lineIdx))
      )
    }.toList
    Some(matches)
  }



  /**
   * Handles the explore tool request.
   *
   * Applies Isabelle exploration queries to commands, similar to I/Q Explore functionality.
   *
   * @param params The tool parameters
   * @return Either error message or result data
   */
  private def handleExplore(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    try {
      // Extract parameters
      val target = params.get("command_selection").map(_.toString).getOrElse("")
      val query = params.get("query").map(_.toString).getOrElse("")
      val arguments = params.get("arguments").map(_.toString).getOrElse("")

      // Validate required parameters - arguments required except for sledgehammer
      if (target.isEmpty || query.isEmpty) {
        return Left("Missing required parameters: target, query")
      }

      // Arguments are required for proof and find_theorems, optional for sledgehammer
      if (arguments.isEmpty && (query == "proof" || query == "find_theorems")) {
        return Left(s"Arguments are required for query type '$query'")
      }

      // Validate target type
      if (!List("current", "file_offset", "file_pattern").contains(target)) {
        return Left(s"Invalid target: $target. Must be 'current', 'file_offset', or 'file_pattern'")
      }

      // Validate query type
      if (!List("proof", "sledgehammer", "find_theorems").contains(query)) {
        return Left(s"Invalid query: $query. Must be 'proof', 'sledgehammer', or 'find_theorems'")
      }

      // Extract file-related parameters for file_offset and file_pattern targets
      val filePath = params.get("path").map(_.toString) match {
        case Some(path) if path.trim.nonEmpty =>
          IQUtils.autoCompleteFilePath(path.trim) match {
            case Right(fullPath) => Some(fullPath)
            case Left(errorMsg) => return Left(errorMsg)
          }
        case Some(_) => None
        case None => None
      }
      val offset = params.get("offset").flatMap {
        case n: Number => Some(n.intValue())
        case s: String => Try(s.toInt).toOption
        case _ => None
      }
      val pattern = params.get("pattern").map(_.toString)

      // Validate target-specific parameters
      target match {
        case "file_offset" =>
          if (filePath.isEmpty || offset.isEmpty) {
            return Left("file_offset target requires path and offset parameters")
          }
        case "file_pattern" =>
          if (filePath.isEmpty || pattern.isEmpty) {
            return Left("file_pattern target requires path and pattern parameters")
          }
        case _ => // current target needs no additional parameters
      }

      // Execute the exploration
      val result = executeExploration(target, filePath, offset, pattern, query, arguments)

      Right(result)

    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Error in handleExplore: ${ex.getMessage}")
        ex.printStackTrace()
        Left(s"Internal error: ${ex.getMessage}")
    }
  }

  /**
   * Result collector for MCP exploration queries.
   * Captures XML output and status from Extended_Query_Operation.
   */
  private class ExploreResultCollector(queryType: String) {
    var xmlResults: List[XML.Tree] = List.empty
    private var currentStatus: Extended_Query_Operation.Status = Extended_Query_Operation.Status.waiting
    private var isComplete: Boolean = false
    private var hasError: Boolean = false
    private var errorMessage: String = ""

    def statusCallback(status: Extended_Query_Operation.Status): Unit = {
      // Debug: log status changes
      Output.writeln(s"I/Q Server: Status changed to $status")

      currentStatus = status
      if (status == Extended_Query_Operation.Status.finished) {
        isComplete = true
        // Debug: log completion
        Output.writeln(s"I/Q Server: Query completed, isComplete=$isComplete, hasError=$hasError")
      }

      if (status == Extended_Query_Operation.Status.failed) {
        hasError = true
        isComplete = true
        Output.writeln("I/Q Server: Query failed, presumably because of an unknown print function")
      }
    }

    def outputCallback(snapshot: Document.Snapshot, command_results: Command.Results, output: List[XML.Tree]): Unit = {
      // Debug: log callback invocation
      Output.writeln(s"I/Q Server: outputCallback called with ${output.size} XML trees")

      // Process all XML output (output is incremental, so we need to accumulate unique results)
      if (output.nonEmpty) {
        // For sledgehammer, we want to accumulate all unique "Try this" results
        // The output contains the current state, so we should take it as the latest complete set
        xmlResults = output

        // Debug: log the XML structure to understand what we're getting
        output.foreach { tree =>
          val treeStr = tree.toString
          Output.writeln(s"I/Q Server: Received XML (${tree.getClass.getSimpleName}): ${treeStr.take(200)}")

          // Also log the extracted content to see if duplicates come from here
          val content = XML.content(tree).trim
          if (content.nonEmpty && content.contains("Try this")) {
            Output.writeln(s"I/Q Server: Extracted 'Try this' content: ${content.take(100)}")
          }
        }
      }
    }

    def getResultsAsString(): String = {
      // Debug: log result collection
      Output.writeln(s"I/Q Server: Getting results as string, xmlResults.size=${xmlResults.size}")

      if (xmlResults.isEmpty) {
        Output.writeln("I/Q Server: No XML results collected")
        return "No results"
      }

      // Debug: log XML types
      val types = xmlResults.map(_.getClass.getSimpleName).distinct
      Output.writeln(s"I/Q Server: XML result types: ${types.mkString(", ")}")

      // Convert XML results to readable text using a consistent approach
      val results = xmlResults.flatMap { tree =>
        val content = XML.content(tree).trim
        if (content.nonEmpty) {
          Output.writeln(s"I/Q Server: Extracted content: ${content.take(150)}")
          List(content)
        } else List()
      }.filter(_.nonEmpty)

      if (results.isEmpty) {
        // Debug: show raw XML if no readable content found
        val rawXml = xmlResults.map(_.toString).mkString("\n")
        s"Query completed but no readable results found. Raw XML (first 500 chars): ${rawXml.take(500)}"
      } else {
        // Apply sledgehammer-specific filtering
        if (queryType == "sledgehammer") {
          filterSledgehammerResults(results)
        } else {
          results.mkString("\n\n")
        }
      }
    }

    /**
     * Filters sledgehammer results to only include those with "Try this: .* ms)"
     * that have been successfully replayed.
     */
    private def filterSledgehammerResults(results: List[String]): String = {
      // Fixed regex to handle prover name before "Try this" and decimal milliseconds
      val tryThisPattern = """.*Try this:\s+(.+?)\s+\((\d+(?:\.\d+)?)\s*ms\)""".r

      Output.writeln(s"I/Q Server: Filtering ${results.size} total results for 'Try this' pattern")
      results.zipWithIndex.foreach { case (result, index) =>
        val hasTryThis = tryThisPattern.findFirstIn(result).isDefined
        Output.writeln(s"I/Q Server: Result $index (${result.take(50)}...): hasTryThis=$hasTryThis")
      }

      val filteredResults = results.filter { result =>
        tryThisPattern.findFirstIn(result).isDefined
      }

      Output.writeln(s"I/Q Server: After filtering: ${filteredResults.size} results")

      val distinctResults = filteredResults.distinct
      Output.writeln(s"I/Q Server: After distinct: ${distinctResults.size} results")

      if (distinctResults.isEmpty) {
        "Sledgehammer completed but found no successful proof attempts with timing information."
      } else {
        Output.writeln(s"I/Q Server: Returning ${distinctResults.size} sledgehammer results with 'Try this' pattern")
        distinctResults.foreach { result =>
          Output.writeln(s"I/Q Server: Final result: ${result.take(100)}")
        }
        distinctResults.mkString("\n\n")
      }
    }

    def isFinished(): Boolean = isComplete
    def wasSuccessful(): Boolean = isComplete && !hasError
    def getStatus(): String = currentStatus.toString
  }

  /**
   * Executes the actual exploration query using Extended_Query_Operation.
   *
   * @param target The target type (current, file_offset, file_pattern)
   * @param filePath Optional file path
   * @param offset Optional offset
   * @param pattern Optional pattern
   * @param query The query type (proof, sledgehammer, find_theorems)
   * @param arguments The query arguments
   * @return A map containing the results
   */
  private def executeExploration(
    target: String,
    filePath: Option[String],
    offset: Option[Int],
    pattern: Option[String],
    query: String,
    arguments: String
  ): Map[String, Any] = {

    try {
      // Validate target parameters using IQUtils
      IQUtils.validateTarget(target, filePath, offset, pattern) match {
        case scala.util.Failure(ex) =>
          return Map(
            "success" -> false,
            "error" -> ex.getMessage,
            "results" -> "",
            "message" -> s"Invalid target parameters: ${ex.getMessage}"
          )
        case _ => // Continue
      }

      // Convert query type from external to internal format
      val internalQuery = IQUtils.externalToInternalQuery(query)

      // Handle default arguments (only for sledgehammer)
      val finalArguments = if (arguments.trim.isEmpty && query == "sledgehammer") {
        IQUtils.getDefaultArguments("sledgehammer")
      } else {
        arguments
      }

      // Find the target command using IQUtils
      val commandResult = target match {
        case "current" => IQUtils.getCurrentCommand()
        case "file_offset" => IQUtils.findCommandAtFileOffset(filePath.get, offset.get)
        case "file_pattern" => IQUtils.findCommandByPattern(filePath.get, pattern.get)
        case _ => scala.util.Failure(new IllegalArgumentException(s"Unknown target: $target"))
      }

      commandResult match {
        case scala.util.Success(command) =>
          // Format query arguments using IQUtils
          val formattedArgs = IQUtils.formatQueryArguments(internalQuery, finalArguments)

          val targetDescription = target match {
            case "current" => "current command at cursor position"
            case "file_offset" => s"command at ${filePath.getOrElse("?")}:${offset.getOrElse("?")}"
            case "file_pattern" => s"command matching '${pattern.getOrElse("?")}' in ${filePath.getOrElse("?")}"
            case _ => "unknown target"
          }

          // Execute the actual query using Extended_Query_Operation
          val collector = new ExploreResultCollector(query)

          // Debug: log query execution start
          Output.writeln(s"I/Q Server: Starting query execution for $internalQuery with arguments: $formattedArgs")

          try {
            // All Extended_Query_Operation operations must run in GUI thread
            // Use the same pattern as I/Q Explore dockable
            val operation = GUI_Thread.now {
              // Get the active view
              val activeView = jEdit.getActiveView()
              if (activeView == null) {
                throw new RuntimeException("No active view available")
              }

              // Debug: log operation creation
              Output.writeln(s"I/Q Server: Creating Extended_Query_Operation for $internalQuery")

              // Create the query operation (same pattern as I/Q Explore)
              val operation = new Extended_Query_Operation(
                PIDE.editor,
                activeView,
                internalQuery,
                collector.statusCallback,
                collector.outputCallback,
              )

              // Debug: log activation
              Output.writeln(s"I/Q Server: Activating operation and applying query")

              // Activate and execute immediately (same as I/Q Explore)
              operation.activate()

              Output.writeln(s"I/Q Server: Formatted args: $formattedArgs")

              operation.apply_query_at_command(command, formattedArgs)
              operation
            }

            // Wait for completion with timeout - NOT in GUI thread
            val timeoutMs = 30000L // 30 seconds timeout
            val startTime = System.currentTimeMillis()
            val pollInterval = 500L // 500ms polling

            // Debug: log waiting start
            Output.writeln(s"I/Q Server: Waiting for query completion (timeout: ${timeoutMs}ms)")

            while (!collector.isFinished() && (System.currentTimeMillis() - startTime) < timeoutMs) {
              // Debug: log polling every 5 seconds
              if ((System.currentTimeMillis() - startTime) % 5000 < pollInterval) {
                Output.writeln(s"I/Q Server: Still waiting... Status: ${collector.getStatus()}, Elapsed: ${System.currentTimeMillis() - startTime}ms")
              }
              Thread.sleep(pollInterval)
            }

            // Debug: log completion or timeout
            val elapsed = System.currentTimeMillis() - startTime
            Output.writeln(s"I/Q Server: Finished waiting after ${elapsed}ms, isFinished=${collector.isFinished()}")

            // Deactivate the operation in GUI thread
            Output.writeln(s"I/Q Server: Deactivating operation")
            GUI_Thread.now {
              operation.deactivate()
            }

            // Check if we timed out
            val timedOut = !collector.isFinished()

            // Get command text for response (thread-safe)
            val cmdText = command.source.trim.replace("\n", "\\n")
            val displayText = if (cmdText.length > 200) cmdText.take(200) + "..." else cmdText

            Map(
              "success" -> (collector.wasSuccessful() && !timedOut),
              "arguments" -> finalArguments,
              "command_found" -> displayText,
              "results" -> collector.getResultsAsString(),
              "timed_out" -> timedOut,
              "message" -> (if (timedOut) "Query timed out after 30 seconds"
                           else if (collector.wasSuccessful()) "Query completed successfully"
                           else s"Query completed with errors. Note that to use the `proof` query type, you need to import Isar_Explore.thy from the I/Q plugin root directory.")
            )

          } catch {
            case ex: Exception =>
              Map(
                "success" -> false,
                "error" -> ex.getMessage,
                "results" -> "",
                "message" -> s"Failed to execute query operation: ${ex.getMessage}"
              )
          }

        case scala.util.Failure(ex) =>
          Map(
            "success" -> false,
            "error" -> ex.getMessage,
            "results" -> "",
            "message" -> s"Failed to find target command: ${ex.getMessage}"
          )
      }

    } catch {
      case ex: Exception =>
        Map(
          "success" -> false,
          "error" -> ex.getMessage,
          "results" -> "",
          "message" -> s"Failed to execute exploration: ${ex.getMessage}"
        )
    }
  }

  /**
   * Handles the save_file tool request.
   *
   * Saves files in Isabelle/jEdit. If path is provided, saves that specific file (if open and modified).
   * If no path provided, saves all modified files.
   *
   * @param params The tool parameters
   * @return Either error message or result data
   */
  private def handleSaveFile(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    try {
      Output.writeln(s"I/Q Server: Starting handleSaveFile with params: $params")

      val pathOpt = params.get("path").map(_.toString.trim).filter(_.nonEmpty)

      pathOpt match {
        case Some(path) =>
          // Save specific file
          val filePath = IQUtils.autoCompleteFilePath(path, trackedOnly = false, allowNonexisting = false) match {
            case Right(fullPath) => fullPath
            case Left(errorMsg) => return Left(errorMsg)
          }

          // Try to find the buffer for this file
          getBufferModel(filePath) match {
            case Some((_, buffer_model)) =>
              val buffer = buffer_model.buffer
              val savedFiles = if (buffer.isDirty()) {
                GUI_Thread.now {
                  buffer.save(null, null)
                }
                Output.writeln(s"I/Q Server: Saved file: $filePath")
                List(filePath)
              } else {
                Output.writeln(s"I/Q Server: File not modified, no save needed: $filePath")
                List.empty[String]
              }

              Right(Map("saved_files" -> savedFiles))

            case None =>
              Output.writeln(s"I/Q Server: File exists but not open in jEdit, no action needed: $filePath")
              Right(Map("saved_files" -> List.empty[String]))
          }

        case None =>
          // Save all modified files
          val savedFiles = GUI_Thread.now {
            val views = jEdit.getViews()
            val allBuffers = views.flatMap(_.getBuffers()).distinct
            val modifiedBuffers = allBuffers.filter(_.isDirty())

            modifiedBuffers.foreach { buffer =>
              buffer.save(null, null)
              Output.writeln(s"I/Q Server: Saved modified file: ${buffer.getPath()}")
            }

            modifiedBuffers.map(_.getPath()).toList
          }

          Right(Map("saved_files" -> savedFiles))
      }

    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Save file error: ${ex.getMessage}")
        ex.printStackTrace()
        Left(s"Save file error: ${ex.getMessage}")
    }
  }
}
