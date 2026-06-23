/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/* Generic, framework-neutral MCP server.

   Serves the MCP wire protocol — JSON-RPC framing, the initialize/tools/list/
   ping handshake, token authentication, tools/call dispatch, and error framing.
   It depends on no UI framework; the host customizes behavior through seams:

     - the tool set is a runtime-mutable McpToolRegistry of self-describing
       McpTool values (name + description + inputSchema + handler);
     - console/UI logging, the JSON codec, and the input-parameter transform
       are injected (defaulting to no-ops / identity).

   `authenticate` is a built-in (matched in handleClient before the registered
   tools, and prepended to tools/list); it cannot be registered or shadowed.

   The JSON-RPC decode lives in McpProtocol, which imports isabelle.JSON
   directly — the only Isabelle coupling of this layer. */

import isabelle.JSON

import java.io.{BufferedReader, InputStreamReader, PrintWriter, BufferedWriter, OutputStreamWriter}
import java.net.{InetAddress, ServerSocket, Socket}
import java.util.concurrent.{ExecutorService, Executors}
import java.util.concurrent.atomic.AtomicInteger
import java.time.LocalTime
import java.time.format.DateTimeFormatter


/** A self-describing MCP tool: its wire name, human description, JSON-schema
  * for inputs, and the handler. `handler` returns Right(result-fields) for a
  * success, or Left(message) for a validation error surfaced to the caller as
  * an isError tool result. Exceptions thrown by the handler are NOT caught here
  * — they propagate to McpServer.handleToolCall and become a JSON-RPC
  * INTERNAL_ERROR with the original message (id preserved). */
final case class McpTool(
  name: String,
  description: String,
  inputSchema: Map[String, Any],
  handler: McpToolParams => Either[String, McpToolResult]
)


/** Tool-call parameters: a normalized Map[String, Any] of arguments. */
final case class McpToolParams private (private val fields: Map[String, Any]) {
  def toMap: Map[String, Any] = fields
}
object McpToolParams {
  val empty: McpToolParams = McpToolParams(Map.empty)
  def fromMap(fields: Map[String, Any]): McpToolParams = {
    val normalized = fields.collect { case (key, value) if key.trim.nonEmpty =>
      key.trim -> value
    }
    McpToolParams(normalized)
  }
}

/** Tool-handler result: a Map[String, Any] of result fields. */
final case class McpToolResult private (private val fields: Map[String, Any]) {
  def toMap: Map[String, Any] = fields
}
object McpToolResult {
  def fromMap(fields: Map[String, Any]): McpToolResult = McpToolResult(fields)
}

/** Dispatch failure: a bad-params Left from a handler, or an unknown tool. */
sealed trait McpInvocationError {
  def code: Int
  def message: String
}
object McpInvocationError {
  final case class InvalidParams(message: String) extends McpInvocationError {
    val code: Int = ErrorCodes.INVALID_PARAMS
  }
  final case class UnknownTool(toolName: String) extends McpInvocationError {
    val code: Int = ErrorCodes.METHOD_NOT_FOUND
    val message: String = s"Unknown tool: $toolName"
  }
}


/** Console-diagnostics seam (replaces direct isabelle.Output.writeln). */
trait McpLogger {
  def info(message: String): Unit
  def security(message: String): Unit
}
object McpLogger {
  val noop: McpLogger = new McpLogger {
    def info(message: String): Unit = ()
    def security(message: String): Unit = ()
  }
}

/** UI wire-tap seam: the host can mirror traffic and client status to a UI. */
trait McpCommLogger {
  def isLoggingEnabled: Boolean
  def logCommunication(message: String): Unit
  def updateClientStatus(connected: Boolean, count: Int, address: String): Unit
}
object McpCommLogger {
  val noop: McpCommLogger = new McpCommLogger {
    def isLoggingEnabled: Boolean = false
    def logCommunication(message: String): Unit = ()
    def updateClientStatus(connected: Boolean, count: Int, address: String): Unit = ()
  }
}

/** JSON codec seam. A host typically backs this with isabelle.JSON
  * (parse = JSON.parse, format = JSON.Format). */
trait McpJsonCodec {
  def parse(line: String): JSON.T
  def format(value: Any): String
}


/** Framework-neutral server configuration. The host fills these in; all fields
  * are defaulted so a host need not set any of them.
  *
  *   - serverName: the wire identity returned by `initialize`;
  *   - logName: the prefix on console diagnostics;
  *   - threadPrefix: the prefix on the worker / accept-loop thread names;
  *   - authToolDescription: the `description` of the built-in authenticate tool
  *     shown in tools/list — a client-facing hint a host can specialize (e.g.
  *     naming its own auth-token environment variable);
  *   - redact: applied to logged wire traffic (defaults to identity). */
final case class McpServerConfig(
  port: Int,
  authToken: String,
  maxClientThreads: Int,
  serverName: String = "isabelle-mcp-server",
  logName: String = "MCP Server",
  threadPrefix: String = "mcp",
  authToolDescription: String =
    "Authenticate with the MCP server through an authentication token.",
  redact: String => String = identity
)


/** Runtime-mutable, thread-safe, registration-order-preserving tool registry.
  *
  * tools/list reflects current registration order (a java LinkedHashMap under a
  * lock — NOT sorted), and the server prepends the built-in `authenticate`. The
  * name `authenticate` is reserved and cannot be registered. invoke does not
  * catch handler exceptions; they propagate to the server's INTERNAL_ERROR path. */
final class McpToolRegistry {
  import scala.jdk.CollectionConverters._

  private val tools = new java.util.LinkedHashMap[String, McpTool]()
  private val lock = new Object

  private def guardName(name: String): Either[String, Unit] =
    if (name.trim.isEmpty) Left("Tool name must be non-empty")
    else if (name == "authenticate") Left("'authenticate' is a reserved built-in")
    else Right(())

  /** Register a tool; Left on a duplicate name or a reserved/empty name. */
  def register(tool: McpTool): Either[String, Unit] = lock.synchronized {
    guardName(tool.name).flatMap { _ =>
      if (tools.containsKey(tool.name)) Left(s"Tool already registered: ${tool.name}")
      else { val _ = tools.put(tool.name, tool); Right(()) }
    }
  }

  /** Register many; stops at the first failure. */
  def registerAll(ts: Iterable[McpTool]): Either[String, Unit] =
    ts.foldLeft[Either[String, Unit]](Right(()))((acc, t) => acc.flatMap(_ => register(t)))

  def unregister(name: String): Unit = lock.synchronized { val _ = tools.remove(name) }

  def get(name: String): Option[McpTool] = lock.synchronized { Option(tools.get(name)) }

  /** tools/list projection in registration order. The server prepends the
    * built-in authenticate schema. Each element has key order: name,
    * description, inputSchema. */
  def toolDefinitions: List[Map[String, Any]] = lock.synchronized {
    tools.values().asScala.toList.map { t =>
      Map[String, Any](
        "name" -> t.name,
        "description" -> t.description,
        "inputSchema" -> t.inputSchema
      )
    }
  }

  /** Dispatch a tool call. UnknownTool when the name isn't registered. Does NOT
    * catch handler exceptions (they propagate to McpServer.handleToolCall). */
  def invoke(name: String, params: McpToolParams)
      : Either[McpInvocationError, McpToolResult] =
    get(name) match {
      case Some(t) => t.handler(params).left.map(McpInvocationError.InvalidParams.apply)
      case None => Left(McpInvocationError.UnknownTool(name))
    }
}


/** The generic MCP server, customized through the seams above. Construct it,
  * register tools (before or while running), then start(). */
final class McpServer(
  config: McpServerConfig,
  json: McpJsonCodec,
  val registry: McpToolRegistry = new McpToolRegistry(),
  logger: McpLogger = McpLogger.noop,
  comm: McpCommLogger = McpCommLogger.noop,
  paramTransform: Map[String, Any] => Map[String, Any] = identity
) {

  /* ---- runtime tool registration (thread-safe via the registry) ---- */

  def register(tool: McpTool): Either[String, Unit] = registry.register(tool)
  def registerAll(ts: Iterable[McpTool]): Either[String, Unit] = registry.registerAll(ts)
  def unregister(name: String): Unit = registry.unregister(name)

  /* ---- internals ---- */

  private val logName: String = config.logName

  private def throwableMessage(ex: Throwable): String =
    Option(ex.getMessage).map(_.trim).filter(_.nonEmpty).getOrElse(ex.getClass.getName)

  private var serverSocket: Option[ServerSocket] = None
  private var acceptThread: Option[Thread] = None
  @volatile private var isRunning = false

  private val workerCounter = new AtomicInteger(0)
  private val executor: ExecutorService =
    Executors.newFixedThreadPool(
      config.maxClientThreads,
      (r: Runnable) => {
        val t = new Thread(r, s"${config.threadPrefix}-worker-${workerCounter.incrementAndGet()}")
        t.setDaemon(true)
        t.setPriority(Thread.MIN_PRIORITY)
        t
      }
    )

  private val timeFormatter = DateTimeFormatter.ofPattern("HH:mm:ss.SSS")
  private val clientAddressTL = new ThreadLocal[String]()
  private val activeClientCount = new AtomicInteger(0)
  private val authenticatedClientCount = new AtomicInteger(0)

  def getActiveClientCount: Int = activeClientCount.get()
  def getAuthenticatedClientCount: Int = authenticatedClientCount.get()

  private def getTimestamp(): String = LocalTime.now().format(timeFormatter)

  /** Remote address of the client whose request the current thread is handling,
    * or "unknown" off a worker thread. Tool handlers run on the worker thread
    * that set this, so a handler (or code it calls, e.g. for audit logging) can
    * read it. Returns "unknown" under processRequestForTest, which bypasses
    * handleClient. */
  def currentClientAddress(): String =
    Option(clientAddressTL.get()).getOrElse("unknown")

  private def logSecurityEvent(message: String): Unit =
    logger.security(message)

  /* ---- lifecycle ---- */

  def start(): Unit = {
    try {
      // Bind exclusively to loopback. Hardcoded and never configurable: the
      // listen address must never be sourced from the environment or CLI.
      val bindAddress = InetAddress.getByName("127.0.0.1")

      serverSocket = Some(new ServerSocket(config.port, 50, bindAddress))
      isRunning = true

      logger.info(
        s"$logName starting on 127.0.0.1:${config.port} " +
        s"(max_client_threads=${config.maxClientThreads})"
      )

      val thread = new Thread(
        () =>
          serverSocket.foreach { socket =>
            while (isRunning) {
              try {
                val clientSocket = socket.accept()
                logger.info(s"MCP Client connected: ${clientSocket.getRemoteSocketAddress}")

                val _ = executor.submit(new Runnable {
                  def run(): Unit = handleClient(clientSocket)
                })
              } catch {
                case _: java.net.SocketException if !isRunning =>
                  // Server was stopped, ignore
                case ex: Exception =>
                  logger.info(s"Error accepting client connection: ${ex.getMessage}")
              }
            }
          },
        s"${config.threadPrefix}-mcp-accept-loop"
      )
      thread.setDaemon(true)
      thread.start()
      acceptThread = Some(thread)

    } catch {
      case ex: Exception =>
        logger.info(s"Failed to start MCP server: ${ex.getMessage}")
        throw ex
    }
  }

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
    logger.info(s"$logName stopped")
  }

  private def handleClient(clientSocket: Socket): Unit = {
    var registeredClient = false
    var registeredAuthenticated = false
    try {
      clientAddressTL.set(Option(clientSocket.getRemoteSocketAddress).map(_.toString).getOrElse("unknown"))

      clientSocket.setSendBufferSize(65536)
      clientSocket.setTcpNoDelay(true)

      logger.info(s"MCP Client connected with buffer size: ${clientSocket.getSendBufferSize} (no timeout)")

      val clientCount = activeClientCount.incrementAndGet()
      registeredClient = true
      val clientAddr = Option(clientSocket.getRemoteSocketAddress).map(_.toString).getOrElse("unknown")
      comm.updateClientStatus(clientCount > 0, clientCount, clientAddr)

      val reader = new BufferedReader(new InputStreamReader(clientSocket.getInputStream))
      val writer = new PrintWriter(new BufferedWriter(new OutputStreamWriter(clientSocket.getOutputStream), 65536), true)
      var clientAuthenticated = false

      def sendResponse(response: String): Unit = {
        if (comm.isLoggingEnabled)
          comm.logCommunication(
            s"${getTimestamp()} [SEND] ${config.redact(response)}")
        writer.println(response)
        writer.flush()
      }

      Iterator
        .continually(reader.readLine())
        .takeWhile(_ != null)
        .foreach { line =>
        try {
          if (comm.isLoggingEnabled)
            comm.logCommunication(
              s"${getTimestamp()} [RECV] ${config.redact(line)}")

          val requestOpt = try {
            McpProtocol.decodeJsonRpcRequest(json.parse(line)).toOption
          } catch { case _: Exception => None }

          val method = requestOpt.map(_.method).getOrElse("")
          val id = requestOpt.flatMap(_.id)
          val isNotification = id.isEmpty

          // A) Public methods: always allowed, regardless of auth state.
          if (Set("initialize", "tools/list", "ping").contains(method)
              || method.startsWith("notifications/")) {
            processRequest(line).foreach(sendResponse)

          // B) Not yet authenticated: only accept the authenticate tool call.
          } else if (!clientAuthenticated) {
            val authenticated = for {
              req <- requestOpt
              tc <- McpProtocol.decodeToolCall(req).toOption
              if tc.toolName == "authenticate"
              token <- tc.arguments.collectFirst { case ("token", v: String) => v }
              if java.security.MessageDigest.isEqual(
                   token.getBytes("UTF-8"),
                   config.authToken.getBytes("UTF-8"))
            } yield true

            authenticated match {
              case Some(true) =>
                clientAuthenticated = true
                registeredAuthenticated = true
                val _ = authenticatedClientCount.incrementAndGet()
                logSecurityEvent(s"ALLOW authenticate client=${currentClientAddress()}")
                id.foreach { requestId =>
                  sendResponse(formatSuccessResponse(requestId, Map[String, Any](
                    "content" -> List(Map("type" -> "text",
                      "text" -> "Authenticated successfully")))))
                }
              case _ =>
                logSecurityEvent(
                  s"DENY unauthenticated request method='$method' client=${currentClientAddress()}")
                if (!isNotification)
                  sendResponse(formatErrorResponse(id, ErrorCodes.INVALID_REQUEST,
                    "Not authenticated — call the 'authenticate' tool first"))
            }

          // C) Authenticated: handle normally.
          } else {
            processRequest(line).foreach(sendResponse)
          }
        } catch {
          case ex: Exception =>
            sendResponse(formatErrorResponse(None, ErrorCodes.INTERNAL_ERROR,
              s"Internal error: ${throwableMessage(ex)}"))
          case err: LinkageError =>
            logger.info(s"$logName: Linkage error: ${throwableMessage(err)}")
            err.printStackTrace()
            sendResponse(formatErrorResponse(None, ErrorCodes.INTERNAL_ERROR,
              s"Internal linkage error: ${throwableMessage(err)}"))
        }
      }
    } catch {
      case ex: Exception =>
        logger.info(s"Error handling MCP client: ${ex.getMessage}")
      case err: LinkageError =>
        logger.info(s"$logName: Linkage error handling MCP client: ${throwableMessage(err)}")
        err.printStackTrace()
    } finally {
      try {
        clientSocket.close()
        logger.info("MCP Client disconnected")

        if (registeredAuthenticated) {
          val r = authenticatedClientCount.decrementAndGet()
          if (r < 0) authenticatedClientCount.set(0)
        }
        if (registeredClient) {
          val remaining = activeClientCount.decrementAndGet()
          val clampedRemaining = if (remaining < 0) {
            activeClientCount.set(0)
            0
          } else remaining
          comm.updateClientStatus(clampedRemaining > 0, clampedRemaining, "")
        }
      } catch {
        case _: Exception => // Ignore close errors
      } finally {
        clientAddressTL.remove()
      }
    }
  }

  private def processRequest(requestLine: String): Option[String] = {
    var requestIdForError: Option[Any] = None
    try {
      logger.info(s"$logName: Processing request: ${config.redact(requestLine)}")

      val jsonValue = try {
        json.parse(requestLine)
      } catch {
        case ex: Exception =>
          logger.info(s"$logName: Failed to parse JSON-RPC payload: ${throwableMessage(ex)}")
          return Some(
            formatErrorResponse(
              None,
              ErrorCodes.PARSE_ERROR,
              s"Parse error: ${throwableMessage(ex)}"
            )
          )
        case err: LinkageError =>
          logger.info(s"$logName: Linkage error while parsing JSON-RPC payload: ${throwableMessage(err)}")
          return Some(
            formatErrorResponse(
              None,
              ErrorCodes.INTERNAL_ERROR,
              s"Internal linkage error: ${throwableMessage(err)}"
            )
          )
      }
      val request = McpProtocol.decodeJsonRpcRequest(jsonValue) match {
        case Right(decoded) => decoded
        case Left(errorMessage) =>
          return Some(
            formatErrorResponse(
              None,
              ErrorCodes.INVALID_REQUEST,
              errorMessage
            )
          )
      }
      val method = request.method
      val id = request.id
      requestIdForError = id

      logger.info(s"$logName: Parsed method='$method', id=$id")

      id match {
        case Some(requestId) =>
          val result: Either[(Int, String), Map[String, Any]] = method match {
            case "initialize" =>
              createInitializeResult().left.map(msg => (ErrorCodes.METHOD_NOT_FOUND, msg))
            case "tools/list" =>
              createToolsListResult().left.map(msg => (ErrorCodes.METHOD_NOT_FOUND, msg))
            case "tools/call" =>
              handleToolCall(request)
            case "ping" =>
              Right(Map("status" -> "ok", "timestamp" -> System.currentTimeMillis()))
            case _ =>
              logger.info(s"$logName: Unknown method '$method'")
              Left((ErrorCodes.METHOD_NOT_FOUND, s"Method not found: $method"))
          }

          result match {
            case Right(data) => Some(formatSuccessResponse(requestId, data))
            case Left((code, error)) => Some(formatErrorResponse(Some(requestId), code, error))
          }
        case None =>
          method match {
            case m if m.startsWith("notifications/") =>
              logger.info(s"$logName: Handling notification '$method'")
              handleNotification(method)
              None
            case _ =>
              logger.info(s"$logName: Ignoring unknown notification '$method'")
              None
          }
      }
    } catch {
      case ex: Exception =>
        logger.info(s"$logName: Error processing request: ${ex.getMessage}")
        ex.printStackTrace()
        Some(
          formatErrorResponse(
            requestIdForError,
            ErrorCodes.INTERNAL_ERROR,
            s"Internal error: ${throwableMessage(ex)}"
          )
        )
      case err: LinkageError =>
        logger.info(s"$logName: Linkage error processing request: ${throwableMessage(err)}")
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

  private def handleNotification(method: String): Unit = {
    method match {
      case "notifications/initialized" =>
        logger.info(s"$logName: Client initialization complete")
      case _ =>
        logger.info(s"$logName: Unknown notification method: $method")
    }
  }

  private def wrapToolCallResult(result: Map[String, Any], isError: Boolean = false): Map[String, Any] = {
    val serializedJson = json.format(result)
    val base = Map("content" -> List(Map("type" -> "text", "text" -> serializedJson)))
    if (isError) base + ("isError" -> true) else base
  }

  private def handleToolCall(
      request: McpProtocol.JsonRpcRequest
  ): Either[(Int, String), Map[String, Any]] = {
    try {
      val toolCall = McpProtocol.decodeToolCall(request) match {
        case Right(value) => value
        case Left(error) => return Left((ErrorCodes.INVALID_PARAMS, error))
      }
      // Authenticate is handled at the connection level in handleClient; this
      // branch handles it when reached via processRequestForTest or when an
      // already-authenticated client calls it again.
      if (toolCall.toolName == "authenticate") {
        val token = toolCall.arguments.collectFirst { case ("token", v: String) => v }
        return token match {
          case Some(t) if java.security.MessageDigest.isEqual(
            t.getBytes("UTF-8"), config.authToken.getBytes("UTF-8")) =>
            // Return the content map directly — same shape as the connection-level
            // success in handleClient. Do NOT route through wrapToolCallResult,
            // which would re-serialize this map and nest it inside another wrapper.
            Right(Map[String, Any](
              "content" -> List(Map("type" -> "text", "text" -> "Authenticated successfully"))))
          case _ =>
            Left((ErrorCodes.INVALID_REQUEST, "Invalid authentication token"))
        }
      }

      val params = McpToolParams.fromMap(paramTransform(extractArguments(toolCall.arguments)))
      logger.info(
        s"$logName: Extracted tool='${toolCall.toolName}', params=${params.toMap}"
      )

      registry.invoke(toolCall.toolName, params) match {
        case Right(res) =>
          Right(wrapToolCallResult(res.toMap))
        case Left(McpInvocationError.UnknownTool(name)) =>
          logger.info(s"$logName: Unknown tool name: '$name'")
          Left((ErrorCodes.METHOD_NOT_FOUND, s"Unknown tool: $name"))
        case Left(err) =>
          Right(wrapToolCallResult(Map("text" -> err.message), isError = true))
      }
    } catch {
      case ex: Exception =>
        logger.info(s"$logName: Tool execution error: ${ex.getMessage}")
        ex.printStackTrace()
        Left((ErrorCodes.INTERNAL_ERROR, s"Tool execution error: ${ex.getMessage}"))
      case err: LinkageError =>
        logger.info(s"$logName: Tool linkage error: ${throwableMessage(err)}")
        err.printStackTrace()
        Left(
          (
            ErrorCodes.INTERNAL_ERROR,
            s"Tool execution linkage error: ${throwableMessage(err)}"
          )
        )
    }
  }

  /** JSON.T -> Any conversion of tool-call arguments, preserving value kinds. */
  private def extractArguments(jsonMap: Map[String, JSON.T]): Map[String, Any] =
    McpProtocol.extractArguments(jsonMap)

  private def formatSuccessResponse(id: Any, result: Map[String, Any]): String = {
    val responseData = Map(
      "jsonrpc" -> "2.0",
      "id" -> id,
      "result" -> result
    )
    json.format(responseData)
  }

  private def formatErrorResponse(id: Option[Any], code: Int, message: String): String = {
    val responseData = Map(
      "jsonrpc" -> "2.0",
      "id" -> id.orNull,
      "error" -> Map(
        "code" -> code,
        "message" -> message
      )
    )
    json.format(responseData)
  }

  private def createInitializeResult(): Either[String, Map[String, Any]] = {
    val timestamp = java.time.Instant.now().toString
    val result = Map(
      "protocolVersion" -> "2024-11-05",
      "capabilities" -> Map(
        "tools" -> Map.empty[String, Any],
        "resources" -> Map.empty[String, Any]
      ),
      "serverInfo" -> Map(
        "name" -> config.serverName,
        "version" -> s"1.0.0-$timestamp"
      )
    )
    Right(result)
  }

  /** The built-in authenticate tool's schema, prepended to tools/list. The
    * description is `config.authToolDescription`, a client-facing hint the host
    * can specialize. */
  private val authenticateToolSchema: Map[String, Any] =
    Map(
      "name" -> "authenticate",
      "description" -> config.authToolDescription,
      "inputSchema" -> Map(
        "type" -> "object",
        "properties" -> Map(
          "token" -> Map(
            "type" -> "string",
            "description" -> "The authentication token."
          )
        ),
        "required" -> List("token")
      )
    )

  private def createToolsListResult(): Either[String, Map[String, Any]] = {
    val tools = authenticateToolSchema :: registry.toolDefinitions
    Right(Map("tools" -> tools))
  }
}
