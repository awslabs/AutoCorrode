/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.util.Locale

/** Argument parsing and validation utilities for LLM tool calls.
  *
  * Provides safe extraction of string, integer, and boolean parameters from
  * tool argument maps with length limits, sanitization, and validation.
  */
private[assistant] object ToolArgs {

  /** Maximum length for string arguments from LLM tool calls. */
  val MAX_STRING_ARG_LENGTH = 10000

  /** Maximum length for proof text arguments. */
  val MAX_PROOF_ARG_LENGTH = 5000

  /** Maximum length for search pattern arguments. */
  val MAX_PATTERN_ARG_LENGTH = 500

  /** Valid theory reference pattern (for referring to already-open theories). */
  val THEORY_REFERENCE_PATTERN = """^[A-Za-z0-9_.\-/]+$""".r

  /** Valid new theory file name (single file name, no path separators). */
  val CREATE_THEORY_NAME_PATTERN = """^[A-Za-z][A-Za-z0-9_']*$""".r

  /** Sanitize a string argument: trim, limit length, reject control characters.
    *
    * @param args Tool arguments map
    * @param key Parameter name
    * @param maxLen Maximum allowed length (default: MAX_STRING_ARG_LENGTH)
    * @param trim Whether to trim leading/trailing whitespace (default: true)
    * @return Sanitized string value, or empty string if parameter not present
    */
  def safeStringArg(
      args: ResponseParser.ToolArgs,
      key: String,
      maxLen: Int = MAX_STRING_ARG_LENGTH,
      trim: Boolean = true
  ): String = {
    val raw = args.get(key).map(ResponseParser.toolValueToString).getOrElse("")
    val cleaned = raw.filter(c => !c.isControl || c == '\n' || c == '\t')
    val limited = cleaned.take(maxLen)
    if (trim) limited.trim else limited
  }

  /** Strict sibling of [[safeStringArg]]. Distinguishes the three cases
    * callers usually want to handle separately:
    *
    *   - argument missing entirely => Right("")   (semantically "empty")
    *   - argument present and string-typed => Right(cleaned value)
    *   - argument present but a non-string type (number, bool, object, null)
    *     => Left(explanatory error)
    *
    * Use this when the caller needs to produce a specific
    * "argument X must be a string" message rather than silently coercing.
    */
  def safeStringArgEither(
      args: ResponseParser.ToolArgs,
      key: String,
      maxLen: Int = MAX_STRING_ARG_LENGTH,
      trim: Boolean = true
  ): Either[String, String] = {
    args.get(key) match {
      case None | Some(ResponseParser.NullValue) => Right("")
      case Some(ResponseParser.StringValue(raw)) =>
        val cleaned = raw.filter(c => !c.isControl || c == '\n' || c == '\t')
        val limited = cleaned.take(maxLen)
        Right(if (trim) limited.trim else limited)
      case Some(other) =>
        val typeName = other match {
          case _: ResponseParser.IntValue     => "integer"
          case _: ResponseParser.DecimalValue => "number"
          case _: ResponseParser.BooleanValue => "boolean"
          case _: ResponseParser.JsonValue    => "object/array"
          case _                              => "non-string"
        }
        Left(s"Error: argument '$key' must be a string, got $typeName")
    }
  }

  /** Validate a theory name argument.
    *
    * @param args Tool arguments map
    * @return Right(theory name) if valid, Left(error message) otherwise
    */
  def safeTheoryArg(
      args: ResponseParser.ToolArgs
  ): Either[String, String] = {
    safeStringArgEither(args, "theory", 200).flatMap { name =>
      if (name.isEmpty) Left("Error: theory name required")
      else if (THEORY_REFERENCE_PATTERN.findFirstIn(name).isEmpty)
        Left(s"Error: invalid theory name '${describeTheoryName(name)}'")
      else Right(name)
    }
  }

  /** Render a theory-name-like argument for inclusion in user-visible error
    * messages that are later fed back to the LLM. The rejected name may
    * itself have originated from the LLM, so we strip control characters
    * (newlines in particular would let the name steer the ongoing tool-use
    * conversation) and bound the length to a small constant.
    */
  def describeTheoryName(name: String): String = {
    val sanitized = name.map {
      case c if c == '\n' || c == '\r' || c == '\t' => ' '
      case c if c.isControl => '?'
      case c => c
    }
    val limit = 80
    if (sanitized.length <= limit) sanitized
    else sanitized.take(limit) + "…"
  }

  /** Check if a theory name is valid for new file creation (no path separators).
    *
    * @param name Proposed theory name
    * @return true if valid for creation, false otherwise
    */
  def isValidCreateTheoryName(name: String): Boolean =
    CREATE_THEORY_NAME_PATTERN.findFirstIn(name).isDefined

  /** Extract optional integer parameter with type coercion and validation.
    *
    * @param args Tool arguments map
    * @param key Parameter name
    * @return Some(integer value) if parameter present and valid, None otherwise
    * @throws IllegalArgumentException if parameter is present but not convertible to integer
    */
  def optionalIntArg(args: ResponseParser.ToolArgs, key: String): Option[Int] =
    args.get(key).flatMap {
      case ResponseParser.NullValue => None
      case ResponseParser.DecimalValue(d) if !d.isWhole =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer, got decimal value: $d"
        )
      case ResponseParser.DecimalValue(d) => Some(d.toInt)
      case ResponseParser.IntValue(i)     => Some(i)
      case ResponseParser.StringValue(s) =>
        Some(
          scala.util.Try(s.toInt).getOrElse(
            throw new IllegalArgumentException(
              s"Parameter '$key' must be an integer, got: '$s'"
            )
          )
        )
      case ResponseParser.BooleanValue(_) | ResponseParser.JsonValue(_) =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer"
        )
    }

  /** Extract integer parameter with default value.
    *
    * @param args Tool arguments map
    * @param key Parameter name
    * @param default Default value if parameter not present
    * @return Integer value or default
    */
  def intArg(
      args: ResponseParser.ToolArgs,
      key: String,
      default: Int
  ): Int = optionalIntArg(args, key).getOrElse(default)

  /** Extract boolean parameter with default value.
    *
    * @param args Tool arguments map
    * @param key Parameter name
    * @param default Default value if parameter not present
    * @return Boolean value or default
    */
  def boolArg(args: ResponseParser.ToolArgs, key: String, default: Boolean): Boolean =
    args.get(key) match {
      case Some(ResponseParser.BooleanValue(b)) => b
      case Some(ResponseParser.StringValue(s)) =>
        s.trim.toLowerCase match {
          case "true" => true
          case "false" => false
          case _ => default
        }
      case _ => default
    }

  /** Normalize line range to valid [1, totalLines] bounds.
    *
    * @param totalLines Total line count in file
    * @param requestedStart Requested start line (may be out of bounds)
    * @param requestedEnd Requested end line (may be out of bounds, <= 0 means EOF)
    * @return (clampedStart, clampedEnd) within valid bounds
    */
  def normalizeReadRange(
      totalLines: Int,
      requestedStart: Int,
      requestedEnd: Int
  ): (Int, Int) = {
    if (totalLines <= 0) (1, 0)
    else {
      val start = math.max(1, math.min(totalLines, requestedStart))
      val rawEnd = if (requestedEnd <= 0) totalLines else requestedEnd
      val end = math.max(start, math.min(totalLines, rawEnd))
      (start, end)
    }
  }

  /** Clamp buffer offset to valid [0, bufferLength] range.
    *
    * @param offset Requested offset (may be negative or beyond EOF)
    * @param bufferLength Buffer length in characters
    * @return Clamped offset within [0, bufferLength]
    */
  def clampOffset(offset: Int, bufferLength: Int): Int =
    math.max(0, math.min(offset, bufferLength))

  /** Check if an argument name is sensitive and should be redacted in logs.
    *
    * @param argName Argument name to check
    * @return true if sensitive (contains token, secret, password, etc.)
    */
  def isSensitiveArgName(argName: String): Boolean = {
    val lowered = argName.toLowerCase(Locale.ROOT)
    AssistantConstants.SENSITIVE_ARG_TOKENS.exists(token => lowered.contains(token))
  }
}