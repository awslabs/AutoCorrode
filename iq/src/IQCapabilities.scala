/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/** Shared capability backend for I/Q tool operations.
  *
  * This defines a stable dispatch seam between transport layers (e.g. MCP in
  * IQServer) and Isabelle-side tool implementations.
  */
trait IQCapabilityBackend {
  def toolNames: Set[IQToolName]

  def invoke(
    toolName: IQToolName,
    params: IQToolParams
  ): Either[IQCapabilityInvocationError, IQToolResult]
}

enum IQToolName(val wire: String) {
  case ListFiles extends IQToolName("list_files")
  case GetCommandInfo extends IQToolName("get_command_info")
  case GetDocumentInfo extends IQToolName("get_document_info")
  case OpenFile extends IQToolName("open_file")
  case ReadFile extends IQToolName("read_file")
  case WriteFile extends IQToolName("write_file")
  case ResolveCommandTarget extends IQToolName("resolve_command_target")
  case GetContextInfo extends IQToolName("get_context_info")
  case GetEntities extends IQToolName("get_entities")
  case GetTypeAtSelection extends IQToolName("get_type_at_selection")
  case GetProofBlocks extends IQToolName("get_proof_blocks")
  case GetProofContext extends IQToolName("get_proof_context")
  case GetDefinitions extends IQToolName("get_definitions")
  case GetDiagnostics extends IQToolName("get_diagnostics")
  case Explore extends IQToolName("explore")
  case SaveFile extends IQToolName("save_file")
}

object IQToolName {
  private val byWire: Map[String, IQToolName] =
    IQToolName.values.map(tool => tool.wire -> tool).toMap

  def fromWire(raw: String): Either[String, IQToolName] =
    byWire.get(raw.trim) match {
      case Some(tool) => Right(tool)
      case None => Left(raw)
    }
}

final case class IQToolParams private (private val fields: Map[String, Any]) {
  def toMap: Map[String, Any] = fields
}

object IQToolParams {
  val empty: IQToolParams = IQToolParams(Map.empty)

  def fromMap(fields: Map[String, Any]): IQToolParams = {
    val normalized = fields.collect { case (key, value) if key.trim.nonEmpty =>
      key.trim -> value
    }
    IQToolParams(normalized)
  }
}

final case class IQToolResult private (private val fields: Map[String, Any]) {
  def toMap: Map[String, Any] = fields
}

object IQToolResult {
  def fromMap(fields: Map[String, Any]): IQToolResult = IQToolResult(fields)
}

sealed trait IQCapabilityInvocationError {
  def code: Int
  def message: String
}

object IQCapabilityInvocationError {
  final case class InvalidParams(message: String)
      extends IQCapabilityInvocationError {
    val code: Int = ErrorCodes.INVALID_PARAMS
  }

  final case class UnknownTool(toolName: String)
      extends IQCapabilityInvocationError {
    val code: Int = ErrorCodes.METHOD_NOT_FOUND
    val message: String = s"Unknown tool: $toolName"
  }
}

object IQCapabilityBackend {
  type RawToolHandler = IQToolParams => Either[String, IQToolResult]

  def fromHandlers(
    handlers: Map[IQToolName, RawToolHandler]
  ): IQCapabilityBackend =
    new IQCapabilityBackend {
      private val normalizedHandlers: Map[IQToolName, RawToolHandler] =
        handlers

      val toolNames: Set[IQToolName] = normalizedHandlers.keySet

      def invoke(
        toolName: IQToolName,
        params: IQToolParams
      ): Either[IQCapabilityInvocationError, IQToolResult] = {
        normalizedHandlers.get(toolName) match {
          case Some(handler) =>
            handler(params).left.map(
              IQCapabilityInvocationError.InvalidParams.apply
            )
          case None =>
            Left(IQCapabilityInvocationError.UnknownTool(toolName.wire))
        }
      }
    }
}
