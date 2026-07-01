/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

// `package isabelle` (as Extended_Query_Operation.scala), so the generic MCP
// layer is reachable from `package isabelle.ic2` too, not just the default
// package the rest of I/Q lives in.
package isabelle

/**
 * Standardized error codes for I/Q MCP server responses.
 * Following JSON-RPC 2.0 specification for error codes.
 */
object ErrorCodes {
  // JSON-RPC standard error codes
  val PARSE_ERROR = -32700
  val INVALID_REQUEST = -32600
  val METHOD_NOT_FOUND = -32601
  val INVALID_PARAMS = -32602
  val INTERNAL_ERROR = -32603

  // Application-specific error codes (range: -32000 to -32099)
  val FILE_NOT_FOUND = -32000
  val FILE_ACCESS_ERROR = -32001
  val INVALID_FILE_PATH = -32002
  val BUFFER_NOT_FOUND = -32003
  val COMMAND_NOT_FOUND = -32004
  val DOCUMENT_NOT_READY = -32005
  val OPERATION_TIMEOUT = -32006
  val VERIFICATION_FAILED = -32007
  val ISABELLE_ERROR = -32008
  val INVALID_OFFSET = -32009
  val INVALID_LINE_NUMBER = -32010
  val EXPLORATION_FAILED = -32011
  val WRITE_OPERATION_FAILED = -32012
  val INVALID_CONTENT = -32013
  val THEORY_PROCESSING_ERROR = -32014
  val SNAPSHOT_ERROR = -32015

  /**
   * Get human-readable error message for error code.
   */
  def getMessage(code: Int): String = code match {
    case PARSE_ERROR => "Parse error"
    case INVALID_REQUEST => "Invalid request"
    case METHOD_NOT_FOUND => "Method not found"
    case INVALID_PARAMS => "Invalid parameters"
    case INTERNAL_ERROR => "Internal error"
    case FILE_NOT_FOUND => "File not found"
    case FILE_ACCESS_ERROR => "File access error"
    case INVALID_FILE_PATH => "Invalid file path"
    case BUFFER_NOT_FOUND => "Buffer not found"
    case COMMAND_NOT_FOUND => "Command not found"
    case DOCUMENT_NOT_READY => "Document not ready"
    case OPERATION_TIMEOUT => "Operation timeout"
    case VERIFICATION_FAILED => "Verification failed"
    case ISABELLE_ERROR => "Isabelle error"
    case INVALID_OFFSET => "Invalid offset"
    case INVALID_LINE_NUMBER => "Invalid line number"
    case EXPLORATION_FAILED => "Exploration failed"
    case WRITE_OPERATION_FAILED => "Write operation failed"
    case INVALID_CONTENT => "Invalid content"
    case THEORY_PROCESSING_ERROR => "Theory processing error"
    case SNAPSHOT_ERROR => "Snapshot error"
    case _ => "Unknown error"
  }
}
