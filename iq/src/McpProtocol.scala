/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/* JSON-RPC decode for the generic MCP server. Pure: depends only on
   isabelle.JSON.

   Tool identity is an open String (validated non-empty here); the registered
   tool set is the source of truth for which names exist, so "unknown tool" is
   decided at dispatch (McpToolRegistry.invoke), not here. */

// `package isabelle` (as Extended_Query_Operation.scala): shares the generic MCP
// layer with `package isabelle.ic2`. JSON et al. are then in scope unqualified.
package isabelle

object McpProtocol {
  final case class JsonRpcRequest(
    method: String,
    id: Option[Any],
    params: Map[String, JSON.T],
    // The client's progress token from params._meta.progressToken (MCP spec),
    // if any. A request carrying it is opting in to notifications/progress; a
    // string or number per spec. None when absent.
    progressToken: Option[Any] = None
  )

  final case class ToolCall(
    toolName: String,
    arguments: Map[String, JSON.T]
  )

  /** Convert a JSON.T tool-call argument to a plain Any, preserving value kinds
    * (objects -> Map, arrays -> List, scalars unchanged). Pure. */
  private def convertJsonValue(value: JSON.T): Any = value match {
    case JSON.Object(obj) =>
      obj.map { case (k, v) => k -> convertJsonValue(v) }
    case list: List[?] =>
      list.map {
        case nested: JSON.T @unchecked => convertJsonValue(nested)
      }
    case s: String => s
    case b: Boolean => b
    case n: Number => n
    case null => null
    case other => other
  }

  /** Convert a map of JSON.T arguments to plain values, preserving value kinds. */
  def extractArguments(jsonMap: Map[String, JSON.T]): Map[String, Any] =
    jsonMap.map { case (key, value) => key -> convertJsonValue(value) }

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

        // params._meta.progressToken (string|number), if the client opted in.
        val progressToken =
          params.get("_meta") match {
            case Some(JSON.Object(meta)) =>
              meta.get("progressToken").collect {
                case s: String => s
                case n: Number => n
              }
            case _ => None
          }

        Right(JsonRpcRequest(method = method, id = id, params = params,
          progressToken = progressToken))

      case _ =>
        Left("Invalid request: payload must be a JSON object")
    }
  }

  def decodeToolCall(request: JsonRpcRequest): Either[String, ToolCall] = {
    val toolName = request.params.get("name") match {
      case Some(name: String) if name.trim.nonEmpty => name.trim
      case Some(_: String) =>
        return Left("Invalid params: tool 'name' must be non-empty")
      case Some(_) =>
        return Left("Invalid params: tool 'name' must be a string")
      case None =>
        return Left("Invalid params: missing required field 'name'")
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
