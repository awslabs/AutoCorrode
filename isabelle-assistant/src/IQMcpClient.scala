/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

import java.io.{BufferedReader, InputStreamReader, OutputStreamWriter, PrintWriter}
import java.net.{InetSocketAddress, Socket}
import java.nio.charset.StandardCharsets
import java.util.concurrent.atomic.AtomicLong
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

  private[assistant] def parseToolCallResponse(rawResponse: String): Either[String, Map[String, Any]] = {
    try {
      JSON.parse(rawResponse) match {
        case JSON.Object(root) =>
          root.get("error").flatMap(asObject) match {
            case Some(errorObj) =>
              val msg = errorObj.get("message").map(_.toString).getOrElse("Unknown I/Q MCP error")
              Left(msg)
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
      case NonFatal(ex) => Left(s"Failed to parse I/Q MCP response: ${ex.getMessage}")
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
        parseToolCallResponse(responseLine)
      }
    } catch {
      case NonFatal(ex) => Left(ex.getMessage)
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

  private[assistant] def decodeExploreResult(payload: Map[String, Any]): ExploreResult = {
    ExploreResult(
      success = boolField(payload, "success", default = false),
      results = stringField(payload, "results"),
      message = stringField(payload, "message"),
      timedOut = boolField(payload, "timed_out", default = false),
      error = payload.get("error").map(_.toString).filter(_.nonEmpty)
    )
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
