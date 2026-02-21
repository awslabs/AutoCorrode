/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/** Shared capability backend for I/Q tool operations.
  *
  * This defines a stable dispatch seam between transport layers (e.g. MCP in
  * IQServer) and Isabelle-side tool implementations.
  */
trait IQCapabilityBackend {
  def toolNames: Set[String]

  def invoke(
    toolName: String,
    params: Map[String, Any]
  ): Either[IQCapabilityInvocationError, Map[String, Any]]
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
  type RawToolHandler = Map[String, Any] => Either[String, Map[String, Any]]

  def fromHandlers(handlers: Map[String, RawToolHandler]): IQCapabilityBackend =
    new IQCapabilityBackend {
      private val normalizedHandlers: Map[String, RawToolHandler] =
        handlers.map { case (toolName, handler) =>
          (toolName.trim, handler)
        }.filter(_._1.nonEmpty)

      val toolNames: Set[String] = normalizedHandlers.keySet

      def invoke(
        toolName: String,
        params: Map[String, Any]
      ): Either[IQCapabilityInvocationError, Map[String, Any]] = {
        normalizedHandlers.get(toolName.trim) match {
          case Some(handler) =>
            handler(params).left.map(
              IQCapabilityInvocationError.InvalidParams.apply
            )
          case None =>
            Left(IQCapabilityInvocationError.UnknownTool(toolName))
        }
      }
    }
}
