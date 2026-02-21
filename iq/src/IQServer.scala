/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

import java.nio.file.Files
import java.io.{BufferedReader, InputStreamReader, PrintWriter, BufferedWriter, OutputStreamWriter}
import java.net.{InetAddress, ServerSocket, Socket}
import java.util.Locale
import java.util.concurrent.{CountDownLatch, ExecutorService, Executors, TimeUnit}
import scala.util.Try
import scala.annotation.unused
import java.time.LocalTime
import java.time.format.DateTimeFormatter

import org.gjt.sp.jedit.{View, jEdit, Buffer}

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

object IQArgumentUtils {
  private def describeValue(value: Any): String = value match {
    case null => "null"
    case s: String => s"'$s' (String)"
    case other => s"$other (${other.getClass.getSimpleName})"
  }

  private def invalidNumericType(param: String, value: Any, expected: String): String =
    s"Invalid parameter '$param': expected $expected, got ${describeValue(value)}"

  private def parseWholeDouble(value: Double): Option[Long] = {
    if (!java.lang.Double.isFinite(value)) None
    else if (value != math.rint(value)) None
    else {
      val asLong = value.toLong
      if (asLong.toDouble == value) Some(asLong) else None
    }
  }

  def parseLongParamValue(param: String, value: Any): Either[String, Long] = value match {
    case n: java.lang.Long => Right(n.longValue())
    case n: java.lang.Integer => Right(n.longValue())
    case n: java.lang.Short => Right(n.longValue())
    case n: java.lang.Byte => Right(n.longValue())
    case n: scala.Long => Right(n)
    case n: scala.Int => Right(n.toLong)
    case n: scala.Short => Right(n.toLong)
    case n: scala.Byte => Right(n.toLong)
    case n: java.math.BigInteger =>
      if (n.bitLength() <= 63) Right(n.longValue())
      else Left(s"Invalid parameter '$param': value $n is outside Long range")
    case n: BigInt =>
      if (n.isValidLong) Right(n.toLong)
      else Left(s"Invalid parameter '$param': value $n is outside Long range")
    case d: java.lang.Double =>
      parseWholeDouble(d.doubleValue()) match {
        case Some(v) => Right(v)
        case None => Left(invalidNumericType(param, value, "integer (Long range)"))
      }
    case d: scala.Double =>
      parseWholeDouble(d) match {
        case Some(v) => Right(v)
        case None => Left(invalidNumericType(param, value, "integer (Long range)"))
      }
    case f: java.lang.Float =>
      parseWholeDouble(f.doubleValue()) match {
        case Some(v) => Right(v)
        case None => Left(invalidNumericType(param, value, "integer (Long range)"))
      }
    case f: scala.Float =>
      parseWholeDouble(f.toDouble) match {
        case Some(v) => Right(v)
        case None => Left(invalidNumericType(param, value, "integer (Long range)"))
      }
    case s: String =>
      Try(s.trim.toLong).toOption match {
        case Some(v) => Right(v)
        case None => Left(invalidNumericType(param, value, "integer (Long range)"))
      }
    case _ =>
      Left(invalidNumericType(param, value, "integer (Long range)"))
  }

  def parseIntParamValue(param: String, value: Any): Either[String, Int] = {
    parseLongParamValue(param, value).flatMap { longVal =>
      if (longVal >= Int.MinValue && longVal <= Int.MaxValue) Right(longVal.toInt)
      else Left(s"Invalid parameter '$param': value $longVal is outside Int range")
    }
  }

  def optionalIntParam(params: Map[String, Any], name: String): Either[String, Option[Int]] = {
    params.get(name) match {
      case None => Right(None)
      case Some(value) => parseIntParamValue(name, value).map(Some(_))
    }
  }

  def optionalLongParam(params: Map[String, Any], name: String): Either[String, Option[Long]] = {
    params.get(name) match {
      case None => Right(None)
      case Some(value) => parseLongParamValue(name, value).map(Some(_))
    }
  }

  def requiredIntParam(params: Map[String, Any], name: String): Either[String, Int] = {
    params.get(name) match {
      case Some(value) => parseIntParamValue(name, value)
      case None => Left(s"Missing required parameter: $name")
    }
  }

  private def convertJsonValue(value: JSON.T): Any = value match {
    case obj: Map[_, _] =>
      obj.asInstanceOf[Map[String, JSON.T]].map { case (k, v) => k -> convertJsonValue(v) }
    case list: List[_] =>
      list.map(v => convertJsonValue(v.asInstanceOf[JSON.T]))
    case s: String => s
    case b: Boolean => b
    case n: Number => n
    case null => null
    case other => other
  }

  def extractArguments(jsonMap: Map[String, JSON.T]): Map[String, Any] = {
    jsonMap.map { case (key, value) => key -> convertJsonValue(value) }
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
class IQServer(
  port: Int = 8765,
  securityConfig: IQServerSecurityConfig = IQSecurity.fromEnvironment(),
  capabilityBackendOverride: Option[IQCapabilityBackend] = None
) {
  private lazy val reflectiveOutputWriteln: Option[String => Unit] = {
    try {
      val outputClass = Class.forName("isabelle.Output$")
      val module = outputClass.getField("MODULE$").get(null)
      val writelnMethod = outputClass.getMethod("writeln", classOf[String])
      Some((message: String) => {
        val _ = writelnMethod.invoke(module, message)
      })
    } catch {
      case _: Throwable => None
    }
  }

  private def safeOutput(message: String): Unit = {
    reflectiveOutputWriteln match {
      case Some(writeln) =>
        try writeln(message)
        catch { case _: Throwable => () }
      case None => ()
    }
  }

  private def throwableMessage(ex: Throwable): String = {
    Option(ex.getMessage).map(_.trim).filter(_.nonEmpty).getOrElse(ex.getClass.getName)
  }

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
  private var acceptThread: Option[Thread] = None

  /** Flag indicating whether the server is running */
  private var isRunning = false

  /** Thread pool for handling client connections */
  private val executor: ExecutorService =
    Executors.newFixedThreadPool(securityConfig.maxClientThreads)

  // Timestamp formatter for socket logging
  private val timeFormatter = DateTimeFormatter.ofPattern("HH:mm:ss.SSS")
  private val clientAddressTL = new ThreadLocal[String]()

  /**
   * Gets the current timestamp formatted as HH:mm:ss.SSS
   *
   * @return The formatted timestamp string
   */
  private def getTimestamp(): String = {
    LocalTime.now().format(timeFormatter)
  }

  private def currentClientAddress(): String = {
    Option(clientAddressTL.get()).getOrElse("unknown")
  }

  private def getProvidedAuthToken(json: JSON.T): Option[String] = {
    def extractToken(value: Any): Option[String] = {
      value match {
        case token: String => Option(token.trim).filter(_.nonEmpty)
        case _ => None
      }
    }

    json match {
      case JSON.Object(obj) =>
        extractToken(obj.getOrElse("auth_token", null))
          .orElse {
            obj.get("params") match {
              case Some(JSON.Object(params)) => extractToken(params.getOrElse("auth_token", null))
              case _ => None
            }
          }
      case _ => None
    }
  }

  private def logSecurityEvent(message: String): Unit = {
    safeOutput(s"I/Q Server [SECURITY]: $message")
  }

  private def authorizeMutationPath(operation: String, rawPath: String): Either[String, String] = {
    IQSecurity.resolveMutationPath(rawPath, securityConfig.allowedMutationRoots) match {
      case Right(canonicalPath) =>
        logSecurityEvent(
          s"ALLOW mutation op=$operation client=${currentClientAddress()} requested='$rawPath' canonical='${canonicalPath.toString}'"
        )
        Right(canonicalPath.toString)
      case Left(errorMessage) =>
        logSecurityEvent(
          s"DENY mutation op=$operation client=${currentClientAddress()} requested='$rawPath' reason='$errorMessage'"
        )
        Left(errorMessage)
    }
  }

  private def authorizeReadPath(operation: String, rawPath: String): Either[String, String] = {
    IQSecurity.resolveReadPath(rawPath, securityConfig.allowedReadRoots) match {
      case Right(canonicalPath) =>
        logSecurityEvent(
          s"ALLOW read op=$operation client=${currentClientAddress()} requested='$rawPath' canonical='${canonicalPath.toString}'"
        )
        Right(canonicalPath.toString)
      case Left(errorMessage) =>
        logSecurityEvent(
          s"DENY read op=$operation client=${currentClientAddress()} requested='$rawPath' reason='$errorMessage'"
        )
        Left(errorMessage)
    }
  }

  // Testing hook: validates path authorization against the current server security config.
  def authorizeMutationPathForTest(operation: String, rawPath: String): Either[String, String] =
    authorizeMutationPath(operation, rawPath)

  // Testing hook: validates read-path authorization against the current server security config.
  def authorizeReadPathForTest(operation: String, rawPath: String): Either[String, String] =
    authorizeReadPath(operation, rawPath)

  private lazy val capabilityBackend: IQCapabilityBackend =
    capabilityBackendOverride.getOrElse(createDefaultCapabilityBackend())

  private def createDefaultCapabilityBackend(): IQCapabilityBackend =
    IQCapabilityBackend.fromHandlers(
      Map(
        "list_files" -> (params => handleListFiles(params)),
        "get_command_info" -> (params => handleGetCommand(params)),
        "get_document_info" -> (params => handleGetDocumentInfo(params)),
        "open_file" -> (params => handleOpenFile(params)),
        "read_file" -> (params => handleReadTheoryFile(params)),
        "write_file" -> (params => handleWriteTheoryFile(params)),
        "resolve_command_target" -> (params =>
          handleResolveCommandTarget(params)
        ),
        "get_context_info" -> (params => handleGetContextInfo(params)),
        "get_entities" -> (params => handleGetEntities(params)),
        "get_type_at_selection" -> (params =>
          handleGetTypeAtSelection(params)
        ),
        "get_proof_blocks" -> (params => handleGetProofBlocks(params)),
        "get_proof_context" -> (params => handleGetProofContext(params)),
        "get_definitions" -> (params => handleGetDefinitions(params)),
        "get_diagnostics" -> (params => handleGetDiagnostics(params)),
        "explore" -> (params => handleExplore(params)),
        "save_file" -> (params => handleSaveFile(params))
      )
    )

  /**
   * Starts the MCP server.
   *
   * Creates a server socket on the specified port and begins listening for client connections.
   * Each client connection is handled in a separate thread from the executor thread pool.
   */
  def start(): Unit = {
    try {
      val bindAddress: InetAddress = IQSecurity.resolveBindAddress(securityConfig.bindHost) match {
        case Right(address) => address
        case Left(errorMessage) => throw new IllegalArgumentException(errorMessage)
      }
      if (!securityConfig.allowRemoteBind && !bindAddress.isLoopbackAddress) {
        throw new IllegalArgumentException(
          s"Refusing to bind to non-loopback host '${securityConfig.bindHost}'. " +
          "Set IQ_MCP_ALLOW_REMOTE_BIND=true to opt in explicitly."
        )
      }

      serverSocket = Some(new ServerSocket(port, 50, bindAddress))
      isRunning = true

      val authEnabled = securityConfig.authToken.isDefined
      val mutationRoots = securityConfig.allowedMutationRoots.map(_.toString).mkString(", ")
      val readRoots = securityConfig.allowedReadRoots.map(_.toString).mkString(", ")
      Output.writeln(
        s"I/Q Server starting on ${bindAddress.getHostAddress}:$port " +
        s"(allow_remote_bind=${securityConfig.allowRemoteBind}, auth_enabled=$authEnabled, max_client_threads=${securityConfig.maxClientThreads})"
      )
      logSecurityEvent(s"Allowed mutation roots: $mutationRoots")
      logSecurityEvent(s"Allowed read roots: $readRoots")

      val thread = new Thread(
        () =>
          serverSocket.foreach { socket =>
            while (isRunning) {
              try {
                val clientSocket = socket.accept()
                Output.writeln(s"MCP Client connected: ${clientSocket.getRemoteSocketAddress}")

                val _ = executor.submit(new Runnable {
                  def run(): Unit = handleClient(clientSocket)
                })
              } catch {
                case _: java.net.SocketException if !isRunning =>
                  // Server was stopped, ignore
                case ex: Exception =>
                  Output.writeln(s"Error accepting client connection: ${ex.getMessage}")
              }
            }
          },
        "iq-mcp-accept-loop"
      )
      thread.setDaemon(true)
      thread.start()
      acceptThread = Some(thread)

    } catch {
      case ex: Exception =>
        Output.writeln(s"Failed to start MCP server: ${ex.getMessage}")
        throw ex
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
    serverSocket = None
    acceptThread.foreach { thread =>
      thread.interrupt()
      try {
        thread.join(1000)
      } catch {
        case _: InterruptedException =>
          Thread.currentThread().interrupt()
      }
    }
    acceptThread = None
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
      clientAddressTL.set(Option(clientSocket.getRemoteSocketAddress).map(_.toString).getOrElse("unknown"))

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
          val redactedLine = IQSecurity.redactAuthToken(line)

          // Log incoming request if logging is enabled
          if (IQCommunicationLogger.isLoggingEnabled) {
            IQCommunicationLogger.logCommunication(s"${getTimestamp()} [RECV] $redactedLine")
          }

          processRequest(line) match {
            case Some(response) =>
              Output.writeln(s"I/Q Server: Sending response of length ${response.length} chars")
              if (response.length > 10000) {
                Output.writeln(s"I/Q Server: Large response preview: ${response.take(200)}...${response.takeRight(200)}")
              }

              // Log outgoing response if logging is enabled
              if (IQCommunicationLogger.isLoggingEnabled) {
                IQCommunicationLogger.logCommunication(s"${getTimestamp()} [SEND] ${IQSecurity.redactAuthToken(response)}")
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
            val errorResponse =
              formatErrorResponse(
                None,
                ErrorCodes.INTERNAL_ERROR,
                s"Internal error: ${throwableMessage(ex)}"
              )
            writer.println(errorResponse)
            writer.flush()
          case err: LinkageError =>
            safeOutput(s"I/Q Server: Linkage error while handling request: ${throwableMessage(err)}")
            err.printStackTrace()
            val errorResponse =
              formatErrorResponse(
                None,
                ErrorCodes.INTERNAL_ERROR,
                s"Internal linkage error: ${throwableMessage(err)}"
              )
            writer.println(errorResponse)
            writer.flush()
        }
      }
    } catch {
      case ex: Exception =>
        Output.writeln(s"Error handling MCP client: ${ex.getMessage}")
      case err: LinkageError =>
        safeOutput(s"I/Q Server: Linkage error handling MCP client: ${throwableMessage(err)}")
        err.printStackTrace()
    } finally {
      try {
        clientSocket.close()
        Output.writeln("MCP Client disconnected")

        // Update client connection status
        IQCommunicationLogger.updateClientStatus(false)
      } catch {
        case _: Exception => // Ignore close errors
      } finally {
        clientAddressTL.remove()
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
    var requestIdForError: Option[Any] = None
    try {
      safeOutput(s"I/Q Server: Processing request: ${IQSecurity.redactAuthToken(requestLine)}")

      val json = JSON.parse(requestLine)
      val (method, id) = extractMethodAndId(json)
      requestIdForError = id

      safeOutput(s"I/Q Server: Parsed method='$method', id=$id")

      val providedToken = getProvidedAuthToken(json)
      if (!IQSecurity.isTokenAuthorized(securityConfig.authToken, providedToken)) {
        logSecurityEvent(
          s"DENY unauthorized request method='$method' id=$id client=${currentClientAddress()}"
        )
        return id match {
          case Some(requestId) =>
            Some(formatErrorResponse(Some(requestId), ErrorCodes.INVALID_REQUEST, "Unauthorized request"))
          case None =>
            None
        }
      }

      id match {
        case Some(requestId) =>
          val result: Either[(Int, String), Map[String, Any]] = method match {
            case "initialize" =>
              createInitializeResult().left.map(msg => (ErrorCodes.METHOD_NOT_FOUND, msg))
            case "tools/list" =>
              createToolsListResult().left.map(msg => (ErrorCodes.METHOD_NOT_FOUND, msg))
            case "tools/call" =>
              handleToolCallFromJson(json)
            case _ =>
              safeOutput(s"I/Q Server: Unknown method '$method'")
              Left((ErrorCodes.METHOD_NOT_FOUND, s"Method not found: $method"))
          }

          result match {
            case Right(data) => Some(formatSuccessResponse(requestId, data))
            case Left((code, error)) => Some(formatErrorResponse(Some(requestId), code, error))
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
              safeOutput(s"I/Q Server: Handling notification '$method'")
              handleNotification(method, json)
              None // No response for notifications
            case _ =>
              safeOutput(s"I/Q Server: Ignoring unknown notification '$method'")
              None // No response for notifications
          }
      }
    } catch {
      case ex: Exception =>
        safeOutput(s"I/Q Server: Error processing request: ${ex.getMessage}")
        ex.printStackTrace()
        Some(
          formatErrorResponse(
            requestIdForError,
            ErrorCodes.INTERNAL_ERROR,
            s"Internal error: ${throwableMessage(ex)}"
          )
        )
      case err: LinkageError =>
        safeOutput(s"I/Q Server: Linkage error processing request: ${throwableMessage(err)}")
        err.printStackTrace()
        Some(
          formatErrorResponse(
            requestIdForError,
            ErrorCodes.INTERNAL_ERROR,
            s"Internal linkage error: ${throwableMessage(err)}"
          )
        )
    }
  }

  // Testing hook: exposes request routing/auth behavior without opening sockets.
  def processRequestForTest(requestLine: String): Option[String] =
    processRequest(requestLine)

  /**
   * Handles JSON-RPC notifications (messages without id that don't expect responses).
   *
   * @param method The notification method name
   * @param json The parsed JSON notification
   */
  private def handleNotification(method: String, @unused json: JSON.T): Unit = {
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
  private def handleToolCallFromJson(json: JSON.T): Either[(Int, String), Map[String, Any]] = {
    try {
      safeOutput(s"I/Q Server: Raw JSON for tool call: ${IQSecurity.redactAuthToken(json.toString)}")

      val (toolName, params) = extractToolAndParams(json)
      safeOutput(s"I/Q Server: Extracted tool='$toolName', params=$params")

      val result: Either[(Int, String), Map[String, Any]] =
        capabilityBackend.invoke(toolName, params).left.map {
          case IQCapabilityInvocationError.UnknownTool(name) =>
            safeOutput(s"I/Q Server: Unknown tool name: '$name'")
            (ErrorCodes.METHOD_NOT_FOUND, s"Unknown tool: $name")
          case err =>
            (err.code, err.message)
        }

      result.map(wrapToolCallResult)
    } catch {
      case ex: Exception =>
        safeOutput(s"I/Q Server: Tool execution error: ${ex.getMessage}")
        ex.printStackTrace()
        Left((ErrorCodes.INTERNAL_ERROR, s"Tool execution error: ${ex.getMessage}"))
      case err: LinkageError =>
        safeOutput(s"I/Q Server: Tool linkage error: ${throwableMessage(err)}")
        err.printStackTrace()
        Left(
          (
            ErrorCodes.INTERNAL_ERROR,
            s"Tool execution linkage error: ${throwableMessage(err)}"
          )
        )
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
   * Extracts arguments from a JSON object while preserving JSON value kinds.
   *
   * @param jsonMap The JSON object containing arguments
   * @return A map of argument names to values
   */
  def extractArguments(jsonMap: Map[String, JSON.T]): Map[String, Any] = {
    IQArgumentUtils.extractArguments(jsonMap)
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
    val commandSelectionDescription =
      "How to select the command context. " +
        "'current': use the command at the active caret in the active jEdit view. " +
        "'file_offset': requires 'path' and 'offset'; resolves the command containing the normalized offset. " +
        "'file_pattern': requires 'path' and 'pattern'; resolves the command containing the last character of the unique literal substring match."
    val commandSelectionPathDescription =
      "File path used with 'file_offset' and 'file_pattern'. " +
        "Absolute paths are recommended. Relative/partial paths are auto-completed when possible. " +
        "Path must resolve to a readable file tracked by Isabelle/jEdit and allowed by read-root policy."
    val commandSelectionOffsetDescription =
      "0-based character offset used with 'file_offset'. " +
        "If out of bounds, it is clamped to valid file bounds (or 0 for empty content). " +
        "The selected command is the one containing the normalized offset."
    val commandSelectionPatternDescription =
      "Literal plain-text substring used with 'file_pattern'. " +
        "Trimmed before matching; matching is case-sensitive substring search (not regex). " +
        "Must match exactly once in the file. " +
        "The selected command is the one containing the last character of that match."
    val exploreSelectionDescription =
      "How to choose the anchor command for exploration. " +
        "The query is applied AFTER the resolved anchor command. " +
        "'current': anchor is command at active caret. " +
        "'file_offset': requires 'path' and 'offset'. " +
        "'file_pattern': requires 'path' and 'pattern'."
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
        "description" -> "Get command status/details (errors, warnings, proof state, timing) for a current command, line range, or offset range.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "mode" -> Map(
              "type" -> "string",
              "description" -> ("Selection mode. " +
                "'current': command at active caret (optional 'path' must match current buffer). " +
                "'line': requires 'path', 'start_line', and 'end_line'. " +
                "'offset': requires 'path', 'start_offset', and 'end_offset'."),
              "enum" -> List("current", "line", "offset")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> ("Path to target theory file. Required for mode='line' and mode='offset'. " +
                "For mode='current', optional; if provided, it must resolve to the currently active buffer.")
            ),
            "start_line" -> Map(
              "type" -> "integer",
              "description" -> ("Required for mode='line': start line (1-based, inclusive). " +
                "Negative values count from file end (-1 is last line).")
            ),
            "end_line" -> Map(
              "type" -> "integer",
              "description" -> ("Required for mode='line': end line (1-based, inclusive). " +
                "Negative values count from file end (-1 is last line).")
            ),
            "start_offset" -> Map(
              "type" -> "integer",
              "description" -> "Required for mode='offset': start character offset (0-based, inclusive)."
            ),
            "end_offset" -> Map(
              "type" -> "integer",
              "description" -> "Required for mode='offset': end character offset (0-based, exclusive)."
            ),
            "xml_result_file" -> Map(
              "type" -> "string",
              "description" -> ("Optional absolute output path for full XML markup dump. " +
                "Must be within configured mutation roots.")
            ),
            "wait_until_processed" -> Map(
              "type" -> "boolean",
              "description" -> "If true, poll until selected commands are processed/fail/cancel or timeout. Default: false."
            ),
            "timeout" -> Map(
              "type" -> "integer",
              "description" -> "Overall polling timeout in milliseconds when wait_until_processed=true. Default: 5000."
            ),
            "timeout_per_command" -> Map(
              "type" -> "integer",
              "description" -> "Per-command running grace period in milliseconds when wait_until_processed=true. Default: 5000."
            ),
            "include_results" -> Map(
              "type" -> "boolean",
              "description" -> ("If true, include full `results_text` in response. " +
                "If false (default), omit `results_text` and return `full_results_file` path to a temp JSON with full data.")
            )
          ),
          "required" -> List("mode"),
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
              "description" -> "Path to the target theory file."
            ),
            "include_errors" -> Map(
              "type" -> "boolean",
              "description" -> "Include detailed error entries. Default: true."
            ),
            "include_warnings" -> Map(
              "type" -> "boolean",
              "description" -> "Include detailed warning entries. Default: false."
            ),
            "timing_threshold_ms" -> Map(
              "type" -> "number",
              "description" -> "Only include per-command timing entries at or above this threshold (ms). Default: 3000."
            ),
            "wait_until_processed" -> Map(
              "type" -> "boolean",
              "description" -> "If true, wait for theory processing before collecting document status. Default: false."
            ),
            "timeout" -> Map(
              "type" -> "number",
              "description" -> "Optional timeout (ms) used when wait_until_processed=true."
            ),
            "timeout_per_command" -> Map(
              "type" -> "integer",
              "description" -> "Per-command running grace period in milliseconds when wait_until_processed=true. Default: 5000."
            )
          ),
          "required" -> List("path"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "open_file",
        "description" -> "Open an existing file in Isabelle/jEdit, or create one when create_if_missing=true",
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
            "content" -> Map(
              "type" -> "string",
              "description" -> "Initial content when creating a missing file. Ignored unless create_if_missing=true."
            ),
            "overwrite_if_exists" -> Map(
              "type" -> "boolean",
              "description" -> "When create_if_missing=true and content is set, overwrite existing file content if the file already exists (default: false)."
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
        "name" -> "read_file",
        "description" -> "Read content from an Isabelle theory file. Supports reading full file or specific line ranges using structured parameters. Supports 'Line' and 'Search' modes.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "path" -> Map(
              "type" -> "string",
              "description" -> "Path to the theory file to read."
            ),
            "mode" -> Map(
              "type" -> "string",
              "description" -> ("Read mode. " +
                "'Line': return formatted lines for the requested line range (defaults to full file). " +
                "'Search': return matching lines with optional surrounding context; requires 'pattern'."),
              "enum" -> List("Line", "Search")
            ),
            "start_line" -> Map(
              "type" -> "integer",
              "description" -> "Line mode only: start line (1-based, inclusive). Negative values count from end (-1 is last line). Default: 1."
            ),
            "end_line" -> Map(
              "type" -> "integer",
              "description" -> "Line mode only: end line (1-based, inclusive). Negative values count from end (-1 is last line). Default: -1."
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> "Search mode only: non-empty literal substring to match in lines (case-insensitive containment)."
            ),
            "context_lines" -> Map(
              "type" -> "integer",
              "description" -> "Search mode only: number of surrounding context lines per match. Default: 0. Negative values are treated as 0."
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
              "description" -> ("Edit operation. " +
                "'str_replace': requires 'old_str' and 'new_str'. " +
                "'insert': requires 'insert_line' and 'new_str'. " +
                "'line': requires 'start_line', 'end_line', and 'new_str'."),
              "enum" -> List("str_replace", "insert", "line")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> "Target theory file path. Must resolve inside mutation roots and already be open in Isabelle/jEdit."
            ),
            "new_str" -> Map(
              "type" -> "string",
              "description" -> "Replacement/inserted text. Required by all edit operations."
            ),
            "old_str" -> Map(
              "type" -> "string",
              "description" -> "str_replace only: literal text to replace. Must occur exactly once."
            ),
            "insert_line" -> Map(
              "type" -> "integer",
              "description" -> "insert only: insert after this line (1-based). Negative values count from end (-1 is last line)."
            ),
            "start_line" -> Map(
              "type" -> "integer",
              "description" -> "line only: start of replaced line range (1-based, inclusive). Negative values count from end."
            ),
            "end_line" -> Map(
              "type" -> "integer",
              "description" -> "line only: end of replaced line range (1-based, inclusive). Negative values count from end."
            ),
            "xml_result_file" -> Map(
              "type" -> "string",
              "description" -> "Optional absolute output path for XML results of affected commands. Must be inside mutation roots."
            ),
            "wait_until_processed" -> Map(
              "type" -> "boolean",
              "description" -> "If true, wait for affected commands to process before returning. Default: true."
            ),
            "timeout" -> Map(
              "type" -> "integer",
              "description" -> "Overall wait timeout in milliseconds when wait_until_processed=true. Default: 2500."
            ),
            "timeout_per_command" -> Map(
              "type" -> "integer",
              "description" -> "Per-command running grace period in milliseconds when wait_until_processed=true. Default: 5000."
            )
          ),
          "required" -> List("path", "command"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "resolve_command_target",
        "description" -> "Resolve a canonical command selection to a concrete Isabelle command with normalized target metadata. This performs no proof execution; it only resolves context.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "command_selection" -> Map(
              "type" -> "string",
              "description" -> commandSelectionDescription,
              "enum" -> List("current", "file_offset", "file_pattern")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPathDescription
            ),
            "offset" -> Map(
              "type" -> "integer",
              "description" -> commandSelectionOffsetDescription
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPatternDescription
            )
          ),
          "required" -> List("command_selection"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "get_context_info",
        "description" -> "Read-only context introspection at a canonical command selection. Returns command metadata, proof-context status, and nested goal-state information.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "command_selection" -> Map(
              "type" -> "string",
              "description" -> commandSelectionDescription,
              "enum" -> List("current", "file_offset", "file_pattern")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPathDescription
            ),
            "offset" -> Map(
              "type" -> "integer",
              "description" -> commandSelectionOffsetDescription
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPatternDescription
            )
          ),
          "required" -> List("command_selection"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "get_entities",
        "description" -> "Read-only entity introspection for a theory file. Enumerates declaration commands (lemma/definition/fun/etc.) with line and offset metadata.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "path" -> Map(
              "type" -> "string",
              "description" -> "Path to theory file for entity extraction."
            ),
            "max_results" -> Map(
              "type" -> "integer",
              "description" -> "Optional maximum number of entities to return (default: 500)."
            )
          ),
          "required" -> List("path"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "get_type_at_selection",
        "description" -> "Read-only type introspection at a canonical command selection. Returns the best typing annotation near the selected offset/command.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "command_selection" -> Map(
              "type" -> "string",
              "description" -> commandSelectionDescription,
              "enum" -> List("current", "file_offset", "file_pattern")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPathDescription
            ),
            "offset" -> Map(
              "type" -> "integer",
              "description" -> commandSelectionOffsetDescription
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPatternDescription
            )
          ),
          "required" -> List("command_selection"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "get_proof_blocks",
        "description" -> "Read-only proof-block extraction in either selection scope (single focused block) or file scope (multiple blocks).",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "scope" -> Map(
              "type" -> "string",
              "description" -> "Extraction scope: 'selection' or 'file' (default: selection).",
              "enum" -> List("selection", "file")
            ),
            "command_selection" -> Map(
              "type" -> "string",
              "description" -> commandSelectionDescription,
              "enum" -> List("current", "file_offset", "file_pattern")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> ("For scope='file': required target file path to scan. " +
                "For scope='selection': required when command_selection is 'file_offset' or 'file_pattern'.")
            ),
            "offset" -> Map(
              "type" -> "integer",
              "description" -> commandSelectionOffsetDescription
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPatternDescription
            ),
            "max_results" -> Map(
              "type" -> "integer",
              "description" -> "Optional maximum number of proof blocks to return for scope='file' (default: 30)."
            ),
            "min_chars" -> Map(
              "type" -> "integer",
              "description" -> "Optional minimum proof block text length for scope='file' (default: 8)."
            )
          ),
          "required" -> List("scope"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "get_proof_context",
        "description" -> "Read-only local proof-context introspection (print_context) at a canonical command selection.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "command_selection" -> Map(
              "type" -> "string",
              "description" -> commandSelectionDescription,
              "enum" -> List("current", "file_offset", "file_pattern")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPathDescription
            ),
            "offset" -> Map(
              "type" -> "integer",
              "description" -> commandSelectionOffsetDescription
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPatternDescription
            )
          ),
          "required" -> List("command_selection"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "get_definitions",
        "description" -> "Read-only definition/context lookup via Isar Explore get_defs for one or more names at a canonical command selection.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "names" -> Map(
              "type" -> "string",
              "description" -> "Whitespace-separated list of names to look up, e.g. 'map foldl list_all2'."
            ),
            "command_selection" -> Map(
              "type" -> "string",
              "description" -> commandSelectionDescription,
              "enum" -> List("current", "file_offset", "file_pattern")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPathDescription
            ),
            "offset" -> Map(
              "type" -> "integer",
              "description" -> commandSelectionOffsetDescription
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPatternDescription
            )
          ),
          "required" -> List("names", "command_selection"),
          "additionalProperties" -> false
        )
      ),
      Map(
        "name" -> "get_diagnostics",
        "description" -> "Read-only diagnostics retrieval for errors or warnings in either a canonical command selection or an entire file.",
        "inputSchema" -> Map(
          "type" -> "object",
          "properties" -> Map(
            "severity" -> Map(
              "type" -> "string",
              "description" -> "Diagnostic severity filter.",
              "enum" -> List("error", "warning")
            ),
            "scope" -> Map(
              "type" -> "string",
              "description" -> "Diagnostic scope. 'selection' inspects only the selected command range. 'file' scans full file content.",
              "enum" -> List("selection", "file")
            ),
            "command_selection" -> Map(
              "type" -> "string",
              "description" -> ("When scope='selection': " + commandSelectionDescription),
              "enum" -> List("current", "file_offset", "file_pattern")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> ("When scope='file': required file path to scan. " +
                "When scope='selection': required for command_selection='file_offset' or 'file_pattern'.")
            ),
            "offset" -> Map(
              "type" -> "integer",
              "description" -> ("When scope='selection' and command_selection='file_offset': " + commandSelectionOffsetDescription)
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> ("When scope='selection' and command_selection='file_pattern': " + commandSelectionPatternDescription)
            )
          ),
          "required" -> List("severity"),
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
              "description" -> ("Query type: " +
                "'proof' executes an Isar method/script candidate (requires Isar_Explore.thy imported). " +
                "'sledgehammer' runs sledgehammer. " +
                "'find_theorems' runs find_theorems."),
              "enum" -> List("proof", "sledgehammer", "find_theorems")
            ),
            "command_selection" -> Map(
              "type" -> "string",
              "description" -> exploreSelectionDescription,
              "enum" -> List("current", "file_offset", "file_pattern")
            ),
            "path" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPathDescription
            ),
            "offset" -> Map(
              "type" -> "integer",
              "description" -> commandSelectionOffsetDescription
            ),
            "pattern" -> Map(
              "type" -> "string",
              "description" -> commandSelectionPatternDescription
            ),
            "arguments" -> Map(
              "type" -> "string",
              "description" -> ("Query arguments, interpreted by query type. " +
                "For query='proof': REQUIRED Isar method/script text (examples: 'by simp', 'apply blast'). " +
                "For query='sledgehammer': OPTIONAL prover list; empty means tool defaults. " +
                "For query='find_theorems': REQUIRED query string passed to find_theorems (examples: 'name:map', '\\<open>(_ :: unat) = (_ :: unat)\\<close>').")
            ),
            "max_results" -> Map(
              "type" -> "integer",
              "description" -> "Optional result limit for query='find_theorems'. Values <= 0 are ignored and default 20 is used."
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
              "description" -> "Optional path to a specific file to save. If omitted, saves all modified dirty buffers that pass mutation-root policy."
            )
          ),
          "additionalProperties" -> false
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
        val views = getOpenViews()
        val activeView = jEdit.getActiveView()
        val allBuffers = views.flatMap(_.getBuffers()).distinct

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

      val (readableTrackedFiles, hiddenCount) = trackedFiles.foldLeft((List.empty[Map[String, Any]], 0)) {
        case ((acc, hidden), file) =>
          val path = file.get("path").map(_.toString).getOrElse("")
          IQSecurity.resolveReadPath(path, securityConfig.allowedReadRoots) match {
            case Right(_) => (file :: acc, hidden)
            case Left(_) => (acc, hidden + 1)
          }
      }
      if (hiddenCount > 0) {
        logSecurityEvent(
          s"Filtered $hiddenCount tracked file(s) outside allowed read roots for client=${currentClientAddress()}"
        )
      }
      val visibleTrackedFiles = readableTrackedFiles.reverse

      // Filter results based on parameters
      val filteredFiles = params.get("filter_open") match {
        case Some(true) =>
          val filtered = visibleTrackedFiles.filter(file => file("is_open").asInstanceOf[Boolean])
          Output.writeln(s"I/Q Server: Filtered to open files: ${filtered.length}")
          filtered
        case Some(false) =>
          val filtered = visibleTrackedFiles.filter(file => !file("is_open").asInstanceOf[Boolean])
          Output.writeln(s"I/Q Server: Filtered to non-open files: ${filtered.length}")
          filtered
        case _ =>
          Output.writeln(s"I/Q Server: No open filter applied: ${visibleTrackedFiles.length}")
          visibleTrackedFiles
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
          case Right(fullPath) =>
            authorizeReadPath("get_command_info(path)", fullPath) match {
              case Right(authorizedPath) => Some(authorizedPath)
              case Left(errorMsg) => return Right(errorMsg)
            }
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
    val authorizedXmlResultFile = xmlResultFile match {
      case Some(path) =>
        authorizeMutationPath("get_command_info(xml_result_file)", path) match {
          case Right(canonicalPath) => Some(canonicalPath)
          case Left(errorMsg) => return Right(errorMsg)
        }
      case None => None
    }

    val startLineOpt = IQArgumentUtils.optionalIntParam(params, "start_line") match {
      case Right(v) => v
      case Left(err) => return Right(err)
    }

    val endLineOpt = IQArgumentUtils.optionalIntParam(params, "end_line") match {
      case Right(v) => v
      case Left(err) => return Right(err)
    }

    val startOffsetOpt = IQArgumentUtils.optionalIntParam(params, "start_offset") match {
      case Right(v) => v
      case Left(err) => return Right(err)
    }

    val endOffsetOpt = IQArgumentUtils.optionalIntParam(params, "end_offset") match {
      case Right(v) => v
      case Left(err) => return Right(err)
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
        authorizeReadPath("get_command_info(current)", model.node_name.node) match {
          case Left(errorMsg) => return Right(errorMsg)
          case Right(_) =>
        }

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

    val timeoutMs = IQArgumentUtils.optionalLongParam(params, "timeout") match {
      case Right(Some(v)) => Some(v)
      case Right(None) => Some(5000L) // Default timeout of 5 seconds
      case Left(err) => return Right(err)
    }

    val timeoutPerCommandMs: Option[Int] = IQArgumentUtils.optionalIntParam(params, "timeout_per_command") match {
      case Right(Some(v)) => Some(v)
      case Right(None) => Some(5000) // Default per-command timeout of 5 seconds
      case Left(err) => return Right(err)
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
    authorizedXmlResultFile match {
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
    authorizedXmlResultFile match {
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
      val _ = Files.createDirectories(parentDir)
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
          case Right(fullPath) =>
            authorizeReadPath("get_document_info", fullPath) match {
              case Right(authorizedPath) => authorizedPath
              case Left(errorMsg) => return Left(errorMsg)
            }
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

    val timingThresholdMs = IQArgumentUtils.optionalIntParam(params, "timing_threshold_ms") match {
      case Right(Some(value)) => value
      case Right(None) =>
        Output.writeln(s"I/Q Server: No timing_threshold parameter provided, using 3000ms default")
        3000
      case Left(err) => return Left(err)
    }

    val waitUntilProcessed = params.get("wait_until_processed") match {
      case Some(value: Boolean) => value
      case _ => false  // Default to false
    }

    val timeout_ms = IQArgumentUtils.optionalIntParam(params, "timeout") match {
      case Right(value) => value
      case Left(err) => return Left(err)
    }

    val timeoutPerCommandMs: Option[Int] = IQArgumentUtils.optionalIntParam(params, "timeout_per_command") match {
      case Right(Some(value)) => Some(value)
      case Right(None) => Some(5000) // Default per-command timeout of 5 seconds
      case Left(err) => return Left(err)
    }

    Output.writeln(s"I/Q Server: Getting document info for file: $filePath (errors: $includeErrors, warnings: $includeWarnings, timing_threshold: ${timingThresholdMs}ms, wait_until_processed: $waitUntilProcessed, timeout: ${timeout_ms} ms, timeout_per_command: ${timeoutPerCommandMs}ms)")

    // If wait_until_processed is requested and this is a theory file, wait for completion
    if (waitUntilProcessed) {
      val model = GUI_Thread.now { getFileContentAndModel(filePath) } match {
        case (Some(_), Some(model)) => model
        case _ => return Left(s"Could not get document information for file: $filePath")
      }

      Output.writeln(s"I/Q Server: Requesting theory completion for: ${model.node_name}")
      val _ = waitForTheoryCompletion(model, timeout_ms, timeoutPerCommandMs)
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
    val hasContent = params.contains("content")
    val content = params.get("content").map(_.toString)
    val overwriteIfExists =
      params.getOrElse("overwrite_if_exists", "false").toString.toBoolean

    val resolvedPath = params.getOrElse("path", "").toString match {
      case path if path.trim.nonEmpty =>
        IQUtils.autoCompleteFilePath(path.trim, trackedOnly = false, allowNonexisting = createIfMissing) match {
          case Right(fullPath) => fullPath
          case Left(errorMsg) => return Left(errorMsg)
        }
      case _ => return Left("path parameter is required")
    }
    val readablePath = authorizeReadPath("open_file", resolvedPath) match {
      case Right(canonicalPath) => canonicalPath
      case Left(errorMsg) => return Left(errorMsg)
    }
    val filePath = if (createIfMissing) {
      authorizeMutationPath("open_file(create_if_missing=true)", readablePath) match {
        case Right(canonicalPath) => canonicalPath
        case Left(errorMsg) => return Left(errorMsg)
      }
    } else readablePath
    val view = params.getOrElse("view", "true").toString.toBoolean

    if (!createIfMissing && (hasContent || overwriteIfExists)) {
      return Left(
        "Parameters 'content' and 'overwrite_if_exists' require create_if_missing=true"
      )
    }
    if (overwriteIfExists && !hasContent) {
      return Left("Parameter 'overwrite_if_exists' requires parameter 'content'")
    }

    Output.writeln(
      s"I/Q Server: Opening file: $filePath, create_if_missing: $createIfMissing, view: $view, has_content: $hasContent, overwrite_if_exists: $overwriteIfExists"
    )

    try {
      val result = GUI_Thread.now {
        if (view) {
          openFileInEditor(filePath, createIfMissing, content, overwriteIfExists)
        } else {
          openFileInBuffer(filePath, createIfMissing, content, overwriteIfExists)
        }
      }

      // TODO: How do we make sure we don't return to the caller before
      // the file has been opened?

      val response = Map(
        "path" -> result("path"),
        "created" -> result("created").toBoolean,
        "overwritten" -> result.getOrElse("overwritten", "false").toBoolean,
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

  private def handleReadTheoryFile(params: Map[String, Any]): Either[String, Map[String, Any]] = {
    try {
      val filePath = params.getOrElse("path", "").toString match {
        case path if path.trim.nonEmpty =>
          IQUtils.autoCompleteFilePath(path.trim) match {
            case Right(fullPath) =>
              authorizeReadPath("read_file", fullPath) match {
                case Right(authorizedPath) => authorizedPath
                case Left(errorMsg) => return Left(errorMsg)
              }
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

          val startLine: Int = IQArgumentUtils.optionalIntParam(params, "start_line") match {
            case Right(Some(line)) => line
            case Right(None) => 1
            case Left(err) => return Left(err)
          }

          val endLine: Int = IQArgumentUtils.optionalIntParam(params, "end_line") match {
            case Right(Some(line)) => line
            case Right(None) => -1
            case Left(err) => return Left(err)
          }

          // Delegate to existing resource read logic
          GUI_Thread.now {
            readTheoryFile(filePath, startLine, endLine)
          }
        case "Search" =>
          val contextLines = IQArgumentUtils.optionalIntParam(params, "context_lines") match {
            case Right(Some(lines)) => lines
            case Right(None) => 0
            case Left(err) => return Left(err)
          }
          params.get("pattern") match {
            case Some(pattern: String) if pattern.trim.nonEmpty =>
              GUI_Thread.now {
                searchTheoryFile(filePath, pattern, contextLines)
              }
            case Some(_) => return Left("`pattern` must be non-empty for mode 'Search'")
            case _ => return Left("`pattern` argument mandatory for mode 'Search'")
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
    authorizeMutationPath("write_file", filePath) match {
      case Left(errorMsg) => return Left(errorMsg)
      case Right(_) =>
    }

    val waitUntilProcessed = params.get("wait_until_processed") match {
      case Some(value: Boolean) => value
      case _ => true
    }

    val command = params.getOrElse("command", "").toString
    if (command.isEmpty) {
      return Left("command parameter is required")
    }

    val timeoutMs = IQArgumentUtils.optionalLongParam(params, "timeout") match {
      case Right(Some(v)) => Some(v)
      case Right(None) => Some(2500L) // Default timeout of 2.5 seconds
      case Left(err) => return Left(err)
    }

    val timeoutPerCommandMs: Option[Int] = IQArgumentUtils.optionalIntParam(params, "timeout_per_command") match {
      case Right(Some(v)) => Some(v)
      case Right(None) => Some(5000) // Default per-command timeout of 5 seconds
      case Left(err) => return Left(err)
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
          case _ => return Left("new_str parameter is required for command 'line'")
        }

        val startLine: Int = IQArgumentUtils.requiredIntParam(params, "start_line") match {
          case Right(line) => line
          case Left(err) => return Left(err)
        }

        val endLine: Int = IQArgumentUtils.requiredIntParam(params, "end_line") match {
          case Right(line) => line
          case Left(err) => return Left(err)
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

        val insertLine: Int = IQArgumentUtils.requiredIntParam(params, "insert_line") match {
          case Right(line) => line
          case Left(err) => return Left(err)
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
    val _ = IQUtils.blockOnStableSnapshot(buffer_model)

    Output.writeln(s"I/Q Server: Auto-calling get_command for modified range in $filePath")

    val newEndOffset: Int = endOffset + text.length

    // Create parameters for get_command call - use current command mode for now
    val getCommandParams = scala.collection.mutable.Map[String, Any](
      "path" -> filePath,
      "mode" -> "offset",
      "start_offset" -> startOffset,
      "end_offset" -> newEndOffset,
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

  private def openFileCommon(
      filePath: String,
      createIfMissing: Boolean,
      inView: Boolean,
      content: Option[String],
      overwriteIfExists: Boolean
  ): Map[String, String] = {
    val authorizedPath =
      if (createIfMissing) {
        authorizeMutationPath("open_file_common(create)", filePath) match {
          case Right(path) => path
          case Left(error) => throw new Exception(error)
        }
      } else filePath

    val file = new java.io.File(authorizedPath)
    var fileCreated = false
    var fileOverwritten = false

    if (!file.exists() && createIfMissing) {
      content match {
        case Some(initialContent) =>
          createFileWithContent(file, authorizedPath, initialContent)
        case None =>
          // Create empty file without any default content
          val parentDir = file.getParentFile
          if (parentDir != null && !parentDir.exists()) {
            val _ = parentDir.mkdirs()
          }
          file.createNewFile()
      }
      fileCreated = true
      Output.writeln(
        s"I/Q Server: Created file${if (inView) "" else " for buffer"}: $authorizedPath"
      )
    } else if (file.exists() && createIfMissing && content.isDefined) {
      if (!overwriteIfExists) {
        throw new Exception(
          s"File already exists and overwrite_if_exists is false: $authorizedPath"
        )
      }
      createFileWithContent(file, authorizedPath, content.get)
      fileOverwritten = true
      Output.writeln(
        s"I/Q Server: Overwrote existing file${if (inView) "" else " for buffer"}: $authorizedPath"
      )
    } else if (!file.exists()) {
      throw new java.io.FileNotFoundException(s"File does not exist: $authorizedPath")
    }

    if (inView) {
      val views = getOpenViews()
      if (views.isEmpty) {
        throw new Exception("No jEdit views available to display the file")
      }

      val view = views(0)
      val buffer = jEdit.openFile(view, authorizedPath)
      if (buffer == null) {
        throw new Exception(s"Failed to open file in jEdit: $authorizedPath")
      }

      view.setBuffer(buffer)
      view.getTextArea.requestFocus()
      Output.writeln(s"I/Q Server: Opened file in jEdit: $authorizedPath")
    } else {
      // Read file content and provide it to document model
      val content = if (file.exists()) {
        scala.io.Source.fromFile(file, "UTF-8").mkString
      } else {
        ""
      }

      val node_name = PIDE.resources.node_name(authorizedPath)
      Document_Model.provide_files(PIDE.session, List((node_name, content)))

      Output.writeln(s"I/Q Server: Provided file to buffer: $authorizedPath")
    }

    Map(
      "path" -> authorizedPath,
      "created" -> fileCreated.toString,
      "overwritten" -> fileOverwritten.toString,
      "opened" -> "true",
      "in_view" -> inView.toString
    )
  }

  private def openFileInEditor(
      filePath: String,
      createIfMissing: Boolean,
      content: Option[String],
      overwriteIfExists: Boolean
  ): Map[String, String] = {
    openFileCommon(filePath, createIfMissing, inView = true, content, overwriteIfExists)
  }

  private def openFileInBuffer(
      filePath: String,
      createIfMissing: Boolean,
      content: Option[String],
      overwriteIfExists: Boolean
  ): Map[String, String] = {
    openFileCommon(filePath, createIfMissing, inView = false, content, overwriteIfExists)
  }

  private def createFileWithContent(file: java.io.File, filePath: String, content: String): Unit = {
    val parentDir = file.getParentFile
    if (parentDir != null && !parentDir.exists()) {
      val _ = parentDir.mkdirs()
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

  private def getOpenViews(): List[View] = {
    val viewManager = jEdit.getViewManager()
    if (viewManager == null) List.empty
    else {
      val views = scala.collection.mutable.ListBuffer.empty[View]
      viewManager.forEach((view: View) => views += view)
      views.toList
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

    val normalizedPattern = pattern.toLowerCase(Locale.ROOT)

    // Find matching lines
    val matchingLineIndices = lines.zipWithIndex.collect {
      case (line, idx) if line.toLowerCase(Locale.ROOT).contains(normalizedPattern) => idx
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



  private final case class AuthorizedTargetSelection(
      target: String,
      path: Option[String],
      requestedOffset: Option[Int],
      pattern: Option[String]
  )

  private def decodeAndAuthorizeTargetSelection(
      params: Map[String, Any],
      operation: String
  ): Either[String, AuthorizedTargetSelection] = {
    val target = params
      .get("command_selection")
      .map(_.toString.trim)
      .filter(_.nonEmpty)
      .getOrElse("")

    if (target.isEmpty)
      return Left("Missing required parameter: command_selection")
    if (!List("current", "file_offset", "file_pattern").contains(target))
      return Left(
        s"Invalid target: $target. Must be 'current', 'file_offset', or 'file_pattern'"
      )

    val requestedOffset = IQArgumentUtils.optionalIntParam(params, "offset") match {
      case Right(v) => v
      case Left(err) => return Left(err)
    }

    val pattern = params
      .get("pattern")
      .map(_.toString.trim)
      .filter(_.nonEmpty)

    val authorizedPath =
      if (target == "current") None
      else {
        params.get("path").map(_.toString.trim).filter(_.nonEmpty) match {
          case Some(path) =>
            IQUtils.autoCompleteFilePath(path) match {
              case Right(fullPath) =>
                authorizeReadPath(s"$operation(path)", fullPath) match {
                  case Right(pathWithinPolicy) => Some(pathWithinPolicy)
                  case Left(errorMsg) => return Left(errorMsg)
                }
              case Left(errorMsg) => return Left(errorMsg)
            }
          case None => None
        }
      }

    target match {
      case "file_offset" =>
        if (authorizedPath.isEmpty || requestedOffset.isEmpty)
          Left("file_offset target requires path and offset parameters")
        else
          Right(
            AuthorizedTargetSelection(
              target,
              authorizedPath,
              requestedOffset,
              None
            )
          )
      case "file_pattern" =>
        if (authorizedPath.isEmpty || pattern.isEmpty)
          Left("file_pattern target requires path and pattern parameters")
        else
          Right(
            AuthorizedTargetSelection(
              target,
              authorizedPath,
              None,
              pattern
            )
          )
      case _ =>
        Right(AuthorizedTargetSelection(target, None, None, None))
    }
  }

  private def resolveTargetSelection(
      selection: AuthorizedTargetSelection
  ): Either[String, IQUtils.TargetResolution] = {
    IQUtils
      .resolveCommandSelection(
        selection.target,
        selection.path,
        selection.requestedOffset,
        selection.pattern
      )
      .toEither
      .left
      .map(_.getMessage)
      .flatMap { resolved =>
        val nodePath = resolved.command.node_name.node
        if (nodePath.trim.isEmpty) Right(resolved)
        else {
          authorizeReadPath("target_selection(node_path)", nodePath) match {
            case Right(_) => Right(resolved)
            case Left(errorMsg) => Left(errorMsg)
          }
        }
      }
  }

  private def commandRangeFor(command: Command): Option[(String, Int, Int)] = {
    try {
      val snapshot = PIDE.session.snapshot()
      val node = snapshot.get_node(command.node_name)
      if (node != null) {
        val start = node.command_start(command).getOrElse(0)
        Some((command.node_name.node, start, start + command.length))
      } else None
    } catch {
      case _: Exception => None
    }
  }

  private def targetSelectionToMap(
      selection: IQUtils.CommandSelection
  ): Map[String, Any] = {
    selection match {
      case IQUtils.CurrentSelection =>
        Map("command_selection" -> "current")
      case IQUtils.FileOffsetSelection(path, requestedOffset, normalizedOffset) =>
        Map(
          "command_selection" -> "file_offset",
          "path" -> path,
          "requested_offset" -> requestedOffset,
          "normalized_offset" -> normalizedOffset
        )
      case IQUtils.FilePatternSelection(path, pattern) =>
        Map(
          "command_selection" -> "file_pattern",
          "path" -> path,
          "pattern" -> pattern
        )
    }
  }

  private def handleResolveCommandTarget(
      params: Map[String, Any]
  ): Either[String, Map[String, Any]] = {
    decodeAndAuthorizeTargetSelection(params, "resolve_command_target").flatMap {
      selection =>
        resolveTargetSelection(selection).map { resolved =>
          Map(
            "selection" -> targetSelectionToMap(resolved.selection),
            "command" -> commandInfoMap(resolved.command)
          )
        }
    }
  }

  private val ContextProofOpeners: Set[String] =
    Set(
      "lemma",
      "theorem",
      "corollary",
      "proposition",
      "schematic_goal",
      "proof",
      "have",
      "show",
      "obtain",
      "next",
      "fix",
      "assume",
      "define",
      "induction",
      "coinduction",
      "cases"
    )

  private val ContextProofClosers: Set[String] =
    Set("qed", "done", "end", "sorry", "oops", "\\<close>")

  private val EntityKeywords: Set[String] =
    Set(
      "lemma",
      "theorem",
      "corollary",
      "proposition",
      "schematic_goal",
      "definition",
      "abbreviation",
      "lift_definition",
      "fun",
      "function",
      "primrec",
      "datatype",
      "codatatype",
      "type_synonym",
      "record",
      "typedef",
      "inductive",
      "coinductive",
      "nominal_inductive",
      "locale",
      "class",
      "instantiation",
      "interpretation"
    )

  private val EntityNamePattern =
    """(?:lemma|theorem|corollary|proposition|schematic_goal|definition|abbreviation|lift_definition|fun|function|primrec|datatype|codatatype|type_synonym|record|typedef|inductive|coinductive|nominal_inductive|locale|class|instantiation|interpretation)\s+([A-Za-z0-9_']+)""".r

  private val ProofBlockStarters: Set[String] =
    Set(
      "lemma",
      "theorem",
      "corollary",
      "proposition",
      "schematic_goal",
      "proof"
    )

  private val ProofBlockStructuralEnders: Set[String] =
    Set("qed", "done", "sorry", "oops")

  private def selectionAnchorOffset(
      selection: IQUtils.CommandSelection,
      commandStart: Int
  ): Int =
    selection match {
      case IQUtils.FileOffsetSelection(_, _, normalizedOffset) =>
        normalizedOffset
      case _ =>
        commandStart
    }

  private def extractTypingAtOffset(
      snapshot: Document.Snapshot,
      anchorOffset: Int,
      fileContent: Option[String]
  ): Option[Map[String, Any]] = {
    val safeAnchor = math.max(0, anchorOffset)
    val searchStart = math.max(0, safeAnchor - 80)
    val maxEnd =
      fileContent.map(_.length).filter(_ > 0).getOrElse(safeAnchor + 80)
    val searchEnd = math.min(maxEnd, safeAnchor + 80)
    if (searchEnd <= searchStart) {
      None
    } else {
      val types = snapshot.cumulate(
        Text.Range(searchStart, searchEnd),
        List.empty[(Text.Range, String)],
        Markup.Elements(Markup.TYPING),
        _ => {
          case (acc, Text.Info(r, XML.Elem(Markup(Markup.TYPING, _), body))) =>
            Some(acc :+ (r, XML.content(body)))
          case _ => None
        }
      )

      types
        .flatMap(_._2)
        .filter { case (range, _) => range.contains(safeAnchor) }
        .sortBy { case (range, _) => range.length }
        .headOption
        .map { case (range, typ) =>
          val term = fileContent
            .flatMap { content =>
              if (range.start >= 0 && range.start < content.length) {
                val available = content.length - range.start
                val length = math.max(0, math.min(math.min(range.length, available), 120))
                if (length > 0) Some(content.substring(range.start, range.start + length))
                else None
              } else None
            }
            .getOrElse("")
          val line = fileContent
            .map(Line.Document(_))
            .flatMap(doc => scala.util.Try(doc.position(range.start).line + 1).toOption)
            .getOrElse(0)
          Map(
            "has_type" -> true,
            "type_text" -> (if (term.nonEmpty) s"$term :: $typ" else typ),
            "term" -> term,
            "type" -> typ,
            "line" -> line,
            "start_offset" -> range.start,
            "end_offset" -> range.stop
          )
        }
    }
  }

  private def extractProofBlockAtIndex(
      commands: List[(Command, Int)],
      anchorIndex: Int,
      lineDoc: Option[Line.Document]
  ): Option[Map[String, Any]] = {
    if (anchorIndex < 0 || anchorIndex >= commands.length) {
      None
    } else {
      var startIndex = -1
      var i = anchorIndex
      while (i >= 0 && startIndex < 0) {
        val kw = commands(i)._1.span.name
        if (ProofBlockStarters.contains(kw)) {
          startIndex = i
        }
        i -= 1
      }

      if (startIndex < 0) {
        None
      } else {
        val blockParts = scala.collection.mutable.ListBuffer.empty[String]
        var depth = 0
        var j = startIndex
        var foundEnd = false
        while (j < commands.length && !foundEnd) {
          val (cmd, _) = commands(j)
          val kw = cmd.span.name
          blockParts += cmd.source
          if (kw == "proof") depth += 1
          if (kw == "by" && depth == 0) {
            foundEnd = true
          } else if (ProofBlockStructuralEnders.contains(kw)) {
            if (depth <= 1) foundEnd = true
            else depth -= 1
          }
          j += 1
        }

        if (!foundEnd) {
          None
        } else {
          val endIndex = j - 1
          val startOffset = commands(startIndex)._2
          val endOffset = commands(endIndex)._2 + commands(endIndex)._1.length
          val startLine =
            lineDoc
              .flatMap(doc => scala.util.Try(doc.position(startOffset).line + 1).toOption)
              .getOrElse(0)
          val endLine =
            lineDoc
              .flatMap(doc => scala.util.Try(doc.position(endOffset).line + 1).toOption)
              .getOrElse(0)
          val proofText = blockParts.mkString("\n")
          val isApplyStyle =
            proofText.linesIterator.exists(_.trim.startsWith("apply"))
          Some(
            Map(
              "proof_text" -> proofText,
              "start_offset" -> startOffset,
              "end_offset" -> endOffset,
              "start_line" -> startLine,
              "end_line" -> endLine,
              "command_count" -> (endIndex - startIndex + 1),
              "is_apply_style" -> isApplyStyle
            )
          )
        }
      }
    }
  }

  private def extractProofBlocksFromCommands(
      commands: List[(Command, Int)],
      lineDoc: Option[Line.Document],
      minChars: Int
  ): List[Map[String, Any]] = {
    val blocks = scala.collection.mutable.ListBuffer.empty[Map[String, Any]]
    var i = 0
    while (i < commands.length) {
      val starterKw = commands(i)._1.span.name
      if (ProofBlockStarters.contains(starterKw)) {
        extractProofBlockAtIndex(commands, i, lineDoc) match {
          case Some(block) =>
            val proofText = block.get("proof_text").map(_.toString).getOrElse("")
            if (proofText.length >= minChars) {
              blocks += block
            }
            val consumed = block.get("command_count").flatMap {
              case v: Int => Some(v)
              case v: Long => Some(v.toInt)
              case _ => None
            }.getOrElse(1)
            i += math.max(1, consumed)
          case None =>
            i += 1
        }
      } else {
        i += 1
      }
    }
    blocks.toList
  }

  private def commandInfoMap(command: Command): Map[String, Any] = {
    val commandInfoBase = Map(
      "id" -> command.id,
      "length" -> command.length,
      "source" -> command.source,
      "keyword" -> command.span.name
    )
    commandRangeFor(command) match {
      case Some((nodePath, startOffset, endOffset)) =>
        commandInfoBase ++ Map(
          "node_path" -> nodePath,
          "start_offset" -> startOffset,
          "end_offset" -> endOffset
        )
      case None => commandInfoBase
    }
  }

  private def isMetaConstant(name: String): Boolean =
    name.startsWith("Pure.") || name == "Trueprop" || name == "HOL.eq" ||
      name == "HOL.implies" || name == "HOL.conj" || name == "HOL.disj" ||
      name == "HOL.All" || name == "HOL.Ex" || name == "HOL.Not" ||
      name == "HOL.True" || name == "HOL.False"

  private def extractCommandFreeVars(
      snapshot: Document.Snapshot,
      command: Command,
      startOffset: Int
  ): List[String] = {
    val range = Text.Range(startOffset, startOffset + command.length)
    val vars = snapshot.cumulate(
      range,
      List.empty[String],
      Markup.Elements(Markup.FREE, "fixed"),
      _ => {
        case (acc, Text.Info(_, XML.Elem(Markup(_, props), _))) =>
          Markup.Name.unapply(props).map(name => acc :+ name)
      }
    )
    vars.flatMap(_._2).distinct
  }

  private def analyzeGoalMessages(
      messages: List[XML.Tree],
      fallbackFreeVars: List[String]
  ): Map[String, Any] = {
    val text = messages
      .map(elem => XML.content(elem).trim)
      .filter(_.nonEmpty)
      .mkString("\n\n")
    if (text.isEmpty) {
      Map(
        "has_goal" -> false,
        "goal_text" -> "",
        "num_subgoals" -> 0,
        "free_vars" -> List.empty[String],
        "constants" -> List.empty[String]
      )
    } else {
      val freeVars = scala.collection.mutable.LinkedHashSet[String]()
      val constants = scala.collection.mutable.LinkedHashSet[String]()
      var numSubgoals = 0

      def walk(tree: XML.Tree): Unit = tree match {
        case XML.Elem(Markup(Markup.FREE, props), body) =>
          Markup.Name.unapply(props).foreach(freeVars.add)
          body.foreach(walk)
        case XML.Elem(Markup("fixed", props), body) =>
          Markup.Name.unapply(props).foreach(freeVars.add)
          body.foreach(walk)
        case XML.Elem(Markup(Markup.CONSTANT, props), body) =>
          Markup.Name.unapply(props).foreach { name =>
            if (!isMetaConstant(name)) {
              val _ = constants.add(name)
            }
          }
          body.foreach(walk)
        case XML.Elem(Markup("subgoal", _), body) =>
          numSubgoals += 1
          body.foreach(walk)
        case XML.Elem(_, body) =>
          body.foreach(walk)
        case XML.Text(_) =>
      }

      messages.foreach(walk)
      val resolvedFreeVars =
        if (freeVars.nonEmpty) freeVars.toList else fallbackFreeVars
      Map(
        "has_goal" -> true,
        "goal_text" -> text,
        "num_subgoals" -> math.max(numSubgoals, 1),
        "free_vars" -> resolvedFreeVars,
        "constants" -> constants.toList
      )
    }
  }

  private def goalStateForCommand(command: Command): Map[String, Any] = {
    try {
      val snapshot = PIDE.session.snapshot()
      val node = snapshot.get_node(command.node_name)
      if (node == null) {
        Map(
          "has_goal" -> false,
          "goal_text" -> "",
          "num_subgoals" -> 0,
          "free_vars" -> List.empty[String],
          "constants" -> List.empty[String],
          "analysis_error" -> "No snapshot node available for command"
        )
      } else {
        val startOffset = node.command_start(command).getOrElse(0)
        val output = PIDE.editor.output(snapshot, startOffset)
        val fallbackFreeVars = extractCommandFreeVars(snapshot, command, startOffset)
        analyzeGoalMessages(output.messages, fallbackFreeVars)
      }
    } catch {
      case ex: Exception =>
        Map(
          "has_goal" -> false,
          "goal_text" -> "",
          "num_subgoals" -> 0,
          "free_vars" -> List.empty[String],
          "constants" -> List.empty[String],
          "analysis_error" -> ex.getMessage
        )
    }
  }

  private def isInProofContextFromKeywords(keywords: Seq[String]): Boolean = {
    var depth = 0
    val iter = keywords.reverseIterator
    while (iter.hasNext) {
      val keyword = iter.next()
      if (ContextProofClosers.contains(keyword)) {
        depth += 1
      } else if (ContextProofOpeners.contains(keyword)) {
        if (depth > 0) depth -= 1
        else return true
      }
    }
    false
  }

  private def isInProofContextAtCommand(command: Command): Boolean = {
    try {
      val snapshot = PIDE.session.snapshot()
      val node = snapshot.get_node(command.node_name)
      if (node == null || node.commands.isEmpty) {
        false
      } else {
        val startOffset = node.command_start(command).getOrElse(0)
        val safeEnd = math.max(0, startOffset + 1)
        val keywords =
          node.command_iterator(Text.Range(0, safeEnd)).toList.map(_._1.span.name)
        isInProofContextFromKeywords(keywords)
      }
    } catch {
      case _: Exception => false
    }
  }

  private def handleGetContextInfo(
      params: Map[String, Any]
  ): Either[String, Map[String, Any]] = {
    decodeAndAuthorizeTargetSelection(params, "get_context_info").flatMap {
      selection =>
        resolveTargetSelection(selection).map { resolved =>
          val goal = goalStateForCommand(resolved.command)
          val hasGoal = goal.get("has_goal").contains(true)
          Map(
            "selection" -> targetSelectionToMap(resolved.selection),
            "command" -> commandInfoMap(resolved.command),
            "in_proof_context" -> isInProofContextAtCommand(resolved.command),
            "has_goal" -> hasGoal,
            "goal" -> goal
          )
        }
    }
  }

  private def handleGetEntities(
      params: Map[String, Any]
  ): Either[String, Map[String, Any]] = {
    val filePath = params.get("path").map(_.toString.trim).filter(_.nonEmpty) match {
      case Some(path) =>
        IQUtils.autoCompleteFilePath(path) match {
          case Right(fullPath) =>
            authorizeReadPath("get_entities(path)", fullPath) match {
              case Right(authorizedPath) => authorizedPath
              case Left(errorMsg) => return Left(errorMsg)
            }
          case Left(errorMsg) => return Left(errorMsg)
        }
      case None =>
        return Left("Missing required parameter: path")
    }

    val maxResults = IQArgumentUtils.optionalIntParam(params, "max_results") match {
      case Right(Some(v)) if v > 0 => v
      case Right(Some(_)) => return Left("Parameter 'max_results' must be > 0")
      case Right(None) => 500
      case Left(err) => return Left(err)
    }

    getFileContentAndModel(filePath) match {
      case (Some(content), Some(model)) =>
        val snapshot = Document_Model.snapshot(model)
        val node = snapshot.get_node(model.node_name)
        if (node == null) {
          Left(s"Could not load snapshot node for file: $filePath")
        } else {
          val lineDoc = Line.Document(content)
          val allEntities =
            node.command_iterator().toList.collect {
              case (cmd, cmdOffset) if EntityKeywords.contains(cmd.span.name) =>
                val name = EntityNamePattern
                  .findFirstMatchIn(cmd.source.take(300))
                  .map(_.group(1))
                  .getOrElse("(unnamed)")
                val line = lineDoc.position(cmdOffset).line + 1
                Map(
                  "line" -> line,
                  "keyword" -> cmd.span.name,
                  "name" -> name,
                  "start_offset" -> cmdOffset,
                  "end_offset" -> (cmdOffset + cmd.length),
                  "source_preview" -> cmd.source.take(160).trim
                )
            }

          val entities = allEntities.take(maxResults)
          Right(
            Map(
              "path" -> filePath,
              "node_name" -> model.node_name.toString,
              "total_entities" -> allEntities.length,
              "returned_entities" -> entities.length,
              "truncated" -> (allEntities.length > entities.length),
              "entities" -> entities
            )
          )
        }
      case _ =>
        Left(
          s"File $filePath is not tracked by Isabelle/jEdit. Open it first before requesting entities."
        )
    }
  }

  private def handleGetTypeAtSelection(
      params: Map[String, Any]
  ): Either[String, Map[String, Any]] = {
    val normalizedParams = withDefaultCurrentSelection(params)
    decodeAndAuthorizeTargetSelection(
      normalizedParams,
      "get_type_at_selection"
    ).flatMap { selection =>
      resolveTargetSelection(selection).map { resolved =>
        val command = resolved.command
        val snapshot = PIDE.session.snapshot()
        val node = snapshot.get_node(command.node_name)
        val filePath = command.node_name.node
        if (node == null) {
          Map(
            "selection" -> targetSelectionToMap(resolved.selection),
            "command" -> commandInfoMap(command),
            "has_type" -> false,
            "message" -> "No snapshot node available for selection"
          )
        } else {
          val commandStart = node.command_start(command).getOrElse(0)
          val anchorOffset =
            selectionAnchorOffset(resolved.selection, commandStart)
          val typeResult = extractTypingAtOffset(
            snapshot,
            anchorOffset,
            getFileContent(filePath)
          )
          Map(
            "selection" -> targetSelectionToMap(resolved.selection),
            "command" -> commandInfoMap(command)
          ) ++ typeResult.getOrElse(
            Map(
              "has_type" -> false,
              "message" -> "No type information available at selection"
            )
          )
        }
      }
    }
  }

  private def handleGetProofBlocks(
      params: Map[String, Any]
  ): Either[String, Map[String, Any]] = {
    val scope = params
      .get("scope")
      .map(_.toString.trim.toLowerCase(Locale.ROOT))
      .filter(_.nonEmpty) match {
      case Some(value) => value
      case None => return Left("Missing required parameter: scope")
    }

    scope match {
      case "selection" =>
        val normalizedParams = withDefaultCurrentSelection(params)
        decodeAndAuthorizeTargetSelection(
          normalizedParams,
          "get_proof_blocks(selection)"
        ).flatMap { selection =>
          resolveTargetSelection(selection).map { resolved =>
            val command = resolved.command
            val snapshot = PIDE.session.snapshot()
            val node = snapshot.get_node(command.node_name)
            val fileContent = getFileContent(command.node_name.node)
            val lineDoc = fileContent.map(Line.Document(_))

            val block = if (node == null || node.commands.isEmpty) None
            else {
              val commands = node.command_iterator().toList
              val fallbackStart = node.command_start(command).getOrElse(0)
              val anchorOffset =
                selectionAnchorOffset(resolved.selection, fallbackStart)
              val anchorIndexFromOffset =
                commands.indexWhere { case (cmd, cmdOffset) =>
                  anchorOffset >= cmdOffset && anchorOffset < cmdOffset + cmd.length
                }
              val anchorIndex =
                if (anchorIndexFromOffset >= 0) anchorIndexFromOffset
                else commands.indexWhere(_._1.id == command.id)

              if (anchorIndex >= 0)
                extractProofBlockAtIndex(commands, anchorIndex, lineDoc)
              else None
            }

            val proofBlocks = block.toList
            Map(
              "scope" -> "selection",
              "selection" -> targetSelectionToMap(resolved.selection),
              "command" -> commandInfoMap(command),
              "total_blocks" -> proofBlocks.length,
              "returned_blocks" -> proofBlocks.length,
              "truncated" -> false,
              "proof_blocks" -> proofBlocks
            ) ++ (if (proofBlocks.isEmpty)
                    Map("message" -> "No proof block found at selection")
                  else Map.empty)
          }
        }
      case "file" =>
        val filePath = params.get("path").map(_.toString.trim).filter(_.nonEmpty) match {
          case Some(path) =>
            IQUtils.autoCompleteFilePath(path) match {
              case Right(fullPath) =>
                authorizeReadPath("get_proof_blocks(path)", fullPath) match {
                  case Right(authorizedPath) => authorizedPath
                  case Left(errorMsg) => return Left(errorMsg)
                }
              case Left(errorMsg) => return Left(errorMsg)
            }
          case None =>
            return Left("scope='file' requires parameter: path")
        }

        val maxResults = IQArgumentUtils.optionalIntParam(params, "max_results") match {
          case Right(Some(v)) if v > 0 => v
          case Right(Some(_)) => return Left("Parameter 'max_results' must be > 0")
          case Right(None) => 30
          case Left(err) => return Left(err)
        }

        val minChars = IQArgumentUtils.optionalIntParam(params, "min_chars") match {
          case Right(Some(v)) if v >= 0 => v
          case Right(Some(_)) => return Left("Parameter 'min_chars' must be >= 0")
          case Right(None) => 8
          case Left(err) => return Left(err)
        }

        getFileContentAndModel(filePath) match {
          case (Some(content), Some(model)) =>
            val snapshot = Document_Model.snapshot(model)
            val node = snapshot.get_node(model.node_name)
            if (node == null || node.commands.isEmpty) {
              Right(
                Map(
                  "scope" -> "file",
                  "path" -> filePath,
                  "node_name" -> model.node_name.toString,
                  "total_blocks" -> 0,
                  "returned_blocks" -> 0,
                  "truncated" -> false,
                  "proof_blocks" -> List.empty[Map[String, Any]]
                )
              )
            } else {
              val lineDoc = Some(Line.Document(content))
              val allBlocks =
                extractProofBlocksFromCommands(
                  node.command_iterator().toList,
                  lineDoc,
                  minChars
                )
              val returned = allBlocks.take(maxResults)
              Right(
                Map(
                  "scope" -> "file",
                  "path" -> filePath,
                  "node_name" -> model.node_name.toString,
                  "total_blocks" -> allBlocks.length,
                  "returned_blocks" -> returned.length,
                  "truncated" -> (allBlocks.length > returned.length),
                  "proof_blocks" -> returned
                )
              )
            }
          case _ =>
            Left(
              s"File $filePath is not tracked by Isabelle/jEdit. Open it first before requesting proof blocks."
            )
        }
      case _ =>
        Left("Parameter 'scope' must be either 'selection' or 'file'")
    }
  }

  private def withDefaultCurrentSelection(
      params: Map[String, Any]
  ): Map[String, Any] = {
    params.get("command_selection") match {
      case Some(value) if value.toString.trim.nonEmpty => params
      case _ => params + ("command_selection" -> "current")
    }
  }

  private def boolField(payload: Map[String, Any], key: String): Boolean =
    payload.get(key) match {
      case Some(value: Boolean) => value
      case Some(value: String) => value.trim.toLowerCase(Locale.ROOT) == "true"
      case Some(value: Int) => value != 0
      case Some(value: Long) => value != 0L
      case Some(value: Double) => value != 0.0
      case _ => false
    }

  private def stringField(payload: Map[String, Any], key: String): String =
    payload.get(key).map(_.toString).getOrElse("")

  private def runProofQueryAtSelection(
      resolvedTarget: IQUtils.TargetResolution,
      arguments: String
  ): Map[String, Any] =
    executeExploration(
      resolvedTarget = resolvedTarget,
      query = "proof",
      arguments = arguments,
      maxResults = None
    )

  private def handleGetProofContext(
      params: Map[String, Any]
  ): Either[String, Map[String, Any]] = {
    val normalizedParams = withDefaultCurrentSelection(params)
    decodeAndAuthorizeTargetSelection(
      normalizedParams,
      "get_proof_context"
    ).flatMap { selection =>
      resolveTargetSelection(selection).map { resolved =>
        val queryResult = runProofQueryAtSelection(resolved, "print_context")
        val success = boolField(queryResult, "success")
        val timedOut = boolField(queryResult, "timed_out")
        val context = stringField(queryResult, "results").trim
        val message = stringField(queryResult, "message")
        val hasContext = success && context.nonEmpty && context != "No results"
        Map(
          "selection" -> targetSelectionToMap(resolved.selection),
          "command" -> commandInfoMap(resolved.command),
          "success" -> success,
          "timed_out" -> timedOut,
          "has_context" -> hasContext,
          "context" -> context,
          "message" -> message
        ) ++ queryResult.get("error").map(err => Map("error" -> err.toString)).getOrElse(Map.empty)
      }
    }
  }

  private def handleGetDefinitions(
      params: Map[String, Any]
  ): Either[String, Map[String, Any]] = {
    val namesRaw = params.get("names").map(_.toString.trim).getOrElse("")
    if (namesRaw.isEmpty) {
      return Left("Missing required parameter: names")
    }
    val names = namesRaw.split("\\s+").toList.map(_.trim).filter(_.nonEmpty).distinct
    if (names.isEmpty) {
      return Left("No valid names provided")
    }

    val normalizedParams = withDefaultCurrentSelection(params)
    decodeAndAuthorizeTargetSelection(
      normalizedParams,
      "get_definitions"
    ).flatMap { selection =>
      resolveTargetSelection(selection).map { resolved =>
        val queryResult = runProofQueryAtSelection(
          resolved,
          s"get_defs ${names.mkString(" ")}"
        )
        val success = boolField(queryResult, "success")
        val timedOut = boolField(queryResult, "timed_out")
        val definitions = stringField(queryResult, "results").trim
        val message = stringField(queryResult, "message")
        Map(
          "selection" -> targetSelectionToMap(resolved.selection),
          "command" -> commandInfoMap(resolved.command),
          "names" -> names,
          "success" -> success,
          "timed_out" -> timedOut,
          "has_definitions" -> (success && definitions.nonEmpty && definitions != "No results"),
          "definitions" -> definitions,
          "message" -> message
        ) ++ queryResult.get("error").map(err => Map("error" -> err.toString)).getOrElse(Map.empty)
      }
    }
  }

  private def diagnosticsFilterForSeverity(
      severity: String
  ): XML.Elem => Boolean = severity match {
    case "error" => Protocol.is_error
    case _ => elem => Protocol.is_warning(elem) || Protocol.is_legacy(elem)
  }

  private def collectDiagnosticsInRange(
      snapshot: Document.Snapshot,
      range: Text.Range,
      severity: String,
      lineDoc: Option[Line.Document]
  ): List[Map[String, Any]] = {
    val filter = diagnosticsFilterForSeverity(severity)
    Rendering
      .text_messages(snapshot, range, filter)
      .flatMap { case Text.Info(messageRange, elem) =>
        val message = XML.content(elem).trim
        if (message.isEmpty) None
        else {
          val line = lineDoc
            .flatMap(doc => scala.util.Try(doc.position(messageRange.start).line + 1).toOption)
            .getOrElse(0)
          Some(
            Map(
              "line" -> line,
              "start_offset" -> messageRange.start,
              "end_offset" -> messageRange.stop,
              "message" -> message
            )
          )
        }
      }
      .distinct
      .toList
  }

  private def handleGetDiagnostics(
      params: Map[String, Any]
  ): Either[String, Map[String, Any]] = {
    val severity = params
      .get("severity")
      .map(_.toString.trim.toLowerCase(Locale.ROOT))
      .getOrElse("")
    if (!Set("error", "warning").contains(severity)) {
      return Left("Parameter 'severity' must be either 'error' or 'warning'")
    }

    val scope = params
      .get("scope")
      .map(_.toString.trim.toLowerCase(Locale.ROOT))
      .filter(_.nonEmpty)
      .getOrElse("selection")
    if (!Set("selection", "file").contains(scope)) {
      return Left("Parameter 'scope' must be either 'selection' or 'file'")
    }

    if (scope == "file") {
      val filePath = params.get("path").map(_.toString.trim).filter(_.nonEmpty) match {
        case Some(path) =>
          IQUtils.autoCompleteFilePath(path) match {
            case Right(fullPath) =>
              authorizeReadPath("get_diagnostics(path)", fullPath) match {
                case Right(authorizedPath) => authorizedPath
                case Left(errorMsg) => return Left(errorMsg)
              }
            case Left(errorMsg) => return Left(errorMsg)
          }
        case None =>
          return Left("scope='file' requires parameter: path")
      }

      GUI_Thread.now {
        getFileContentAndModel(filePath) match {
          case (Some(content), Some(model)) =>
            val snapshot = Document_Model.snapshot(model)
            val diagnostics = collectDiagnosticsInRange(
              snapshot,
              Text.Range(0, content.length),
              severity,
              Some(Line.Document(content))
            )
            Right(
              Map(
                "scope" -> "file",
                "severity" -> severity,
                "path" -> filePath,
                "node_name" -> model.node_name.toString,
                "count" -> diagnostics.length,
                "diagnostics" -> diagnostics
              )
            )
          case _ =>
            Left(
              s"File $filePath is not tracked by Isabelle/jEdit. Open it first before requesting diagnostics."
            )
        }
      }
    } else {
      val normalizedParams = withDefaultCurrentSelection(params)
      decodeAndAuthorizeTargetSelection(
        normalizedParams,
        "get_diagnostics"
      ).flatMap { selection =>
        resolveTargetSelection(selection).map { resolved =>
          GUI_Thread.now {
            val command = resolved.command
            val snapshot = PIDE.session.snapshot()
            val node = snapshot.get_node(command.node_name)
            val diagnostics =
              if (node == null) List.empty[Map[String, Any]]
              else {
                val start = node.command_start(command).getOrElse(0)
                collectDiagnosticsInRange(
                  snapshot,
                  Text.Range(start, start + command.length),
                  severity,
                  getFileContent(command.node_name.node).map(Line.Document(_))
                )
              }
            Map(
              "scope" -> "selection",
              "severity" -> severity,
              "selection" -> targetSelectionToMap(resolved.selection),
              "command" -> commandInfoMap(command),
              "count" -> diagnostics.length,
              "diagnostics" -> diagnostics
            )
          }
        }
      }
    }
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
      val query = params.get("query").map(_.toString).getOrElse("")
      val arguments = params.get("arguments").map(_.toString).getOrElse("")
      val maxResults = IQArgumentUtils.optionalIntParam(params, "max_results") match {
        case Right(v) => v
        case Left(err) => return Left(err)
      }

      if (query.isEmpty) {
        return Left("Missing required parameter: query")
      }
      if (arguments.isEmpty && (query == "proof" || query == "find_theorems")) {
        return Left(s"Arguments are required for query type '$query'")
      }
      if (!List("proof", "sledgehammer", "find_theorems").contains(query)) {
        return Left(s"Invalid query: $query. Must be 'proof', 'sledgehammer', or 'find_theorems'")
      }

      decodeAndAuthorizeTargetSelection(params, "explore").flatMap { selection =>
        resolveTargetSelection(selection).map { resolvedTarget =>
          executeExploration(resolvedTarget, query, arguments, maxResults)
        }
      }
    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Error in handleExplore: ${ex.getMessage}")
        ex.printStackTrace()
        Left(s"Internal error: ${ex.getMessage}")
      case err: LinkageError =>
        Output.writeln(s"I/Q Server: Linkage error in handleExplore: ${throwableMessage(err)}")
        err.printStackTrace()
        Left(s"Internal linkage error: ${throwableMessage(err)}")
    }
  }

  /**
   * Result collector for MCP exploration queries.
   * Captures XML output and status from Extended_Query_Operation.
   */
  private class ExploreResultCollector(queryType: String) {
    @volatile private var xmlResults: List[XML.Tree] = List.empty
    @volatile private var currentStatus: Extended_Query_Operation.Status = Extended_Query_Operation.Status.waiting
    @volatile private var hasError: Boolean = false
    private val completionLatch = new CountDownLatch(1)

    def statusCallback(status: Extended_Query_Operation.Status): Unit = {
      // Debug: log status changes
      Output.writeln(s"I/Q Server: Status changed to $status")

      currentStatus = status
      if (status == Extended_Query_Operation.Status.finished) {
        completionLatch.countDown()
        // Debug: log completion
        Output.writeln(s"I/Q Server: Query completed, hasError=$hasError")
      }

      if (status == Extended_Query_Operation.Status.failed) {
        hasError = true
        completionLatch.countDown()
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
      val resultsSnapshot = xmlResults
      // Debug: log result collection
      Output.writeln(s"I/Q Server: Getting results as string, xmlResults.size=${resultsSnapshot.size}")

      if (resultsSnapshot.isEmpty) {
        Output.writeln("I/Q Server: No XML results collected")
        return "No results"
      }

      // Debug: log XML types
      val types = resultsSnapshot.map(_.getClass.getSimpleName).distinct
      Output.writeln(s"I/Q Server: XML result types: ${types.mkString(", ")}")

      // Convert XML results to readable text using a consistent approach
      val results = resultsSnapshot.flatMap { tree =>
        val content = XML.content(tree).trim
        if (content.nonEmpty) {
          Output.writeln(s"I/Q Server: Extracted content: ${content.take(150)}")
          List(content)
        } else List()
      }.filter(_.nonEmpty)

      if (results.isEmpty) {
        // Debug: show raw XML if no readable content found
        val rawXml = resultsSnapshot.map(_.toString).mkString("\n")
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

    def awaitCompletion(timeoutMs: Long): Boolean =
      completionLatch.await(timeoutMs, TimeUnit.MILLISECONDS)

    def isFinished(): Boolean = completionLatch.getCount == 0
    def wasSuccessful(): Boolean = isFinished() && !hasError
    def getStatus(): String = currentStatus.toString
  }

  /**
   * Executes the actual exploration query using Extended_Query_Operation.
   *
   * @param resolvedTarget Canonical resolved command target
   * @param query The query type (proof, sledgehammer, find_theorems)
   * @param arguments The query arguments
   * @return A map containing the results
   */
  private def executeExploration(
    resolvedTarget: IQUtils.TargetResolution,
    query: String,
    arguments: String,
    maxResults: Option[Int]
  ): Map[String, Any] = {

    try {
      // Convert query type from external to internal format
      val internalQuery = IQUtils.externalToInternalQuery(query)

      // Handle default arguments (only for sledgehammer)
      val finalArguments = if (arguments.trim.isEmpty && query == "sledgehammer") {
        IQUtils.getDefaultArguments("sledgehammer")
      } else {
        arguments
      }

      val command = resolvedTarget.command
      val formattedArgs =
        if (internalQuery == "find_theorems") {
          val resultLimit = maxResults.filter(_ > 0).getOrElse(20)
          List(resultLimit.toString, "false", finalArguments)
        } else {
          IQUtils.formatQueryArguments(internalQuery, finalArguments)
        }

      val collector = new ExploreResultCollector(query)

      Output.writeln(
        s"I/Q Server: Starting query execution for $internalQuery with arguments: $formattedArgs"
      )

      try {
        val operation = GUI_Thread.now {
          val activeView = jEdit.getActiveView()
          if (activeView == null) {
            throw new RuntimeException("No active view available")
          }

          Output.writeln(
            s"I/Q Server: Creating Extended_Query_Operation for $internalQuery"
          )

          val operation = new Extended_Query_Operation(
            PIDE.editor,
            activeView,
            internalQuery,
            collector.statusCallback,
            collector.outputCallback,
          )

          Output.writeln("I/Q Server: Activating operation and applying query")
          operation.activate()

          Output.writeln(s"I/Q Server: Formatted args: $formattedArgs")
          operation.apply_query_at_command(command, formattedArgs)
          operation
        }

        val timeoutMs = 30000L
        val startTime = System.currentTimeMillis()

        Output.writeln(
          s"I/Q Server: Waiting for query completion (timeout: ${timeoutMs}ms)"
        )
        val completedInTime = try {
          collector.awaitCompletion(timeoutMs)
        } catch {
          case _: InterruptedException =>
            Thread.currentThread().interrupt()
            Output.writeln(
              "I/Q Server: Interrupted while waiting for query completion"
            )
            false
        }

        val elapsed = System.currentTimeMillis() - startTime
        Output.writeln(
          s"I/Q Server: Finished waiting after ${elapsed}ms, isFinished=${collector.isFinished()}"
        )

        Output.writeln("I/Q Server: Deactivating operation")
        GUI_Thread.now {
          operation.deactivate()
        }

        val timedOut = !completedInTime
        val cmdText = command.source.trim.replace("\n", "\\n")
        val displayText =
          if (cmdText.length > 200) cmdText.take(200) + "..." else cmdText

        Map(
          "success" -> (collector.wasSuccessful() && !timedOut),
          "arguments" -> finalArguments,
          "selection" -> targetSelectionToMap(resolvedTarget.selection),
          "command_found" -> displayText,
          "results" -> collector.getResultsAsString(),
          "timed_out" -> timedOut,
          "message" -> (if (timedOut) "Query timed out after 30 seconds"
                        else if (collector.wasSuccessful())
                          "Query completed successfully"
                        else
                          s"Query completed with errors. Note that to use the `proof` query type, you need to import Isar_Explore.thy from the I/Q plugin root directory.")
        )

      } catch {
        case ex: Exception =>
          Map(
            "success" -> false,
            "error" -> throwableMessage(ex),
            "results" -> "",
            "message" -> s"Failed to execute query operation: ${throwableMessage(ex)}"
          )
        case err: LinkageError =>
          Map(
            "success" -> false,
            "error" -> throwableMessage(err),
            "results" -> "",
            "message" -> s"Failed to execute query operation due to linkage error: ${throwableMessage(err)}"
          )
      }

    } catch {
      case ex: Exception =>
        Map(
          "success" -> false,
          "error" -> throwableMessage(ex),
          "results" -> "",
          "message" -> s"Failed to execute exploration: ${throwableMessage(ex)}"
        )
      case err: LinkageError =>
        Map(
          "success" -> false,
          "error" -> throwableMessage(err),
          "results" -> "",
          "message" -> s"Failed to execute exploration due to linkage error: ${throwableMessage(err)}"
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
          authorizeMutationPath("save_file(path)", filePath) match {
            case Left(errorMsg) => return Left(errorMsg)
            case Right(_) =>
          }

          // Try to find the buffer for this file
          getBufferModel(filePath) match {
            case Some((_, buffer_model)) =>
              val buffer = buffer_model.buffer
              val savedFiles = if (buffer.isDirty()) {
                val _ = GUI_Thread.now {
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
          val saveResult: Either[String, List[String]] = GUI_Thread.now {
            val views = getOpenViews()
            val allBuffers = views.flatMap(_.getBuffers()).distinct
            val modifiedBuffers = allBuffers.filter(_.isDirty())

            val decisions = modifiedBuffers.map(buffer => (buffer, authorizeMutationPath("save_file(all)", buffer.getPath())))
            val deniedPaths = decisions.collect { case (buffer, Left(error)) => s"${buffer.getPath()} ($error)" }
            if (deniedPaths.nonEmpty) {
              Left(s"Refusing to save out-of-root files: ${deniedPaths.mkString(", ")}")
            } else {
              val saved = decisions.collect { case (buffer, Right(_)) =>
                buffer.save(null, null)
                Output.writeln(s"I/Q Server: Saved modified file: ${buffer.getPath()}")
                buffer.getPath()
              }.toList
              Right(saved)
            }
          }
          saveResult.map(savedFiles => Map("saved_files" -> savedFiles))
      }

    } catch {
      case ex: Exception =>
        Output.writeln(s"I/Q Server: Save file error: ${ex.getMessage}")
        ex.printStackTrace()
        Left(s"Save file error: ${ex.getMessage}")
    }
  }
}
