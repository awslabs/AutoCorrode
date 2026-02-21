/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import software.amazon.awssdk.thirdparty.jackson.core.{JsonFactory, JsonToken}
import java.io.StringWriter

/** Parses JSON responses from different Bedrock model providers. Extracted from
  * BedrockClient for testability and separation of concerns.
  *
  * Handles response formats for: Anthropic (Claude), Meta (Llama), Amazon
  * (Titan), Mistral, and generic models.
  */
/** Schema for structured output via Anthropic tool_choice forcing. */
case class StructuredResponseSchema(
    name: String,
    description: String,
    jsonSchema: String
)

object ResponseParser {
  private val jsonFactory = new JsonFactory()

  enum ParseError {
    case EmptyResponse
    case MissingTextField
    case InvalidJson(details: String)

    def message: String = this match {
      case EmptyResponse        => "Empty response from model"
      case MissingTextField     => "Could not parse model response (no text field found)"
      case InvalidJson(details) => s"Failed to parse model response: $details"
    }
  }

  /** Parse response from Bedrock model using Jackson JSON parser. Throws on
    * empty/unparseable responses so callers don't treat errors as valid text.
    *
    * @param modelId
    *   The model identifier (determines which fields to extract)
    * @param json
    *   The raw JSON response string
    * @return
    *   Extracted text content
    * @throws RuntimeException
    *   on empty/unparseable responses
    */
  def parseResponse(modelId: String, json: String): String = {
    parseResponseEither(modelId, json) match {
      case Right(value) => value
      case Left(ParseError.InvalidJson(details)) =>
        throw new RuntimeException(
          ParseError.InvalidJson(details).message,
          new RuntimeException(details)
        )
      case Left(err) =>
        throw new RuntimeException(err.message)
    }
  }

  def parseResponseEither(
      modelId: String,
      json: String
  ): Either[ParseError, String] = {
    if (json == null || json.trim.isEmpty) Left(ParseError.EmptyResponse)
    else {
      val parser = jsonFactory.createParser(json)
      try {
        extractTextField(parser, modelId).toRight(ParseError.MissingTextField)
      } catch {
        case ex: Exception => Left(ParseError.InvalidJson(ex.getMessage))
      } finally {
        parser.close()
      }
    }
  }

  /** Extract text content fields from a Bedrock JSON response, collecting all
    * matching blocks.
    */
  private[assistant] def extractTextField(
      parser: software.amazon.awssdk.thirdparty.jackson.core.JsonParser,
      modelId: String
  ): Option[String] = {
    val targetFields =
      if (PayloadBuilder.isProvider(modelId, "anthropic")) Set("text")
      else if (PayloadBuilder.isProvider(modelId, "meta")) Set("generation")
      else if (PayloadBuilder.isProvider(modelId, "amazon")) Set("outputText")
      else Set("text", "content", "output", "response", "generation")

    val results = scala.collection.mutable.ListBuffer[String]()
    while (parser.nextToken() != null) {
      if (
        parser.currentToken() == JsonToken.FIELD_NAME && targetFields.contains(
          parser.currentName()
        )
      ) {
        parser.nextToken()
        if (parser.currentToken() == JsonToken.VALUE_STRING) {
          val value = parser.getValueAsString
          if (value != null && value.nonEmpty) results += value
        }
      }
    }
    if (results.nonEmpty) Some(results.mkString("\n")) else None
  }

  /** Typed tool argument values (avoid Map[String, Any] dynamic dispatch). */
  enum ToolValue {
    case StringValue(value: String)
    case IntValue(value: Int)
    case DecimalValue(value: Double)
    case BooleanValue(value: Boolean)
    case JsonValue(value: String)
    case NullValue
  }
  export ToolValue._
  type ToolArgs = Map[String, ToolValue]

  def toolValueToDisplay(value: ToolValue): String = value match {
    case StringValue(v)  => v
    case IntValue(v)     => v.toString
    case DecimalValue(v) => v.toString
    case BooleanValue(v) => v.toString
    case JsonValue(v)    => v
    case NullValue       => "null"
  }

  /** Convert a ToolValue to a raw string. NullValue maps to empty string. */
  def toolValueToString(value: ToolValue): String = value match {
    case NullValue => ""
    case other     => toolValueToDisplay(other)
  }

  def parseToolArgsJsonObject(json: String): ToolArgs = {
    parseToolArgsJsonObjectEither(json) match {
      case Right(args) => args
      case Left(ParseError.InvalidJson(details)) =>
        ErrorHandler.logSilentError(
          "parseToolArgsJsonObject",
          new RuntimeException(details)
        )
        Map.empty
      case Left(_) => Map.empty
    }
  }

  def parseToolArgsJsonObjectEither(json: String): Either[ParseError, ToolArgs] = {
    val parser = jsonFactory.createParser(json)
    try {
      if (parser.nextToken() != JsonToken.START_OBJECT) Right(Map.empty)
      else Right(parseToolArgsObject(parser))
    } catch {
      case ex: Exception => Left(ParseError.InvalidJson(ex.getMessage))
    } finally {
      parser.close()
    }
  }

  def toolArgsToJson(args: ToolArgs): String = {
    val sw = new StringWriter()
    val gen = jsonFactory.createGenerator(sw)
    gen.writeStartObject()
    args.foreach { case (key, value) =>
      value match {
        case StringValue(v)  => gen.writeStringField(key, v)
        case IntValue(v)     => gen.writeNumberField(key, v)
        case DecimalValue(v) => gen.writeNumberField(key, v)
        case BooleanValue(v) => gen.writeBooleanField(key, v)
        case JsonValue(v)    =>
          gen.writeFieldName(key)
          gen.writeRawValue(v)
        case NullValue => gen.writeNullField(key)
      }
    }
    gen.writeEndObject()
    gen.close()
    sw.toString
  }

  /** Represents a content block in an Anthropic response. */
  enum ContentBlock {
    case TextBlock(text: String)
    case ToolUseBlock(id: String, name: String, input: ToolArgs)
  }
  export ContentBlock._

  /** Parse Anthropic response content blocks and stop_reason. */
  def parseAnthropicContentBlocks(
      json: String
  ): (List[ContentBlock], String) = {
    val parser = jsonFactory.createParser(json)
    val blocks = scala.collection.mutable.ListBuffer[ContentBlock]()
    var stopReason = ""

    try {
      while (parser.nextToken() != null) {
        if (parser.currentToken() == JsonToken.FIELD_NAME) {
          parser.currentName() match {
            case "stop_reason" =>
              parser.nextToken()
              stopReason = parser.getValueAsString("")
            case "content" =>
              if (parser.nextToken() == JsonToken.START_ARRAY) {
                while (parser.nextToken() != JsonToken.END_ARRAY) {
                  if (parser.currentToken() == JsonToken.START_OBJECT) {
                    parseContentBlock(parser).foreach(blocks += _)
                  } else {
                    val _ = parser.skipChildren()
                  }
                }
              } else {
                val _ = parser.skipChildren()
              }
            case _ =>
              parser.nextToken()
              val _ = parser.skipChildren()
          }
        }
      }
    } finally {
      parser.close()
    }

    (blocks.toList, stopReason)
  }

  /** Extract the first ToolUseBlock's input from a forced tool_choice response.
    * Returns None if the response contains no tool_use block.
    */
  def extractForcedToolArgs(json: String): Option[ToolArgs] = {
    val (blocks, _) = parseAnthropicContentBlocks(json)
    blocks.collectFirst { case ToolUseBlock(_, _, input) => input }
  }

  private def parseContentBlock(
      parser: software.amazon.awssdk.thirdparty.jackson.core.JsonParser
  ): Option[ContentBlock] = {
    var blockType = ""
    var textVal = ""
    var toolId = ""
    var toolName = ""
    var input = Map.empty[String, ToolValue]

    while (parser.nextToken() != JsonToken.END_OBJECT) {
      if (parser.currentToken() == JsonToken.FIELD_NAME) {
        val key = parser.currentName()
        parser.nextToken()
        key match {
          case "type" => blockType = parser.getValueAsString("")
          case "text" => textVal = parser.getValueAsString("")
          case "id"   => toolId = parser.getValueAsString("")
          case "name" => toolName = parser.getValueAsString("")
          case "input" if parser.currentToken() == JsonToken.START_OBJECT =>
            input = parseToolArgsObject(parser)
          case _ =>
            val _ = parser.skipChildren()
        }
      }
    }

    blockType match {
      case "text" if textVal.nonEmpty    => Some(TextBlock(textVal))
      case "tool_use" if toolId.nonEmpty =>
        Some(ToolUseBlock(toolId, toolName, input))
      case _ => None
    }
  }

  private def parseToolArgsObject(
      parser: software.amazon.awssdk.thirdparty.jackson.core.JsonParser
  ): ToolArgs = {
    val args = scala.collection.mutable.Map[String, ToolValue]()
    while (parser.nextToken() != JsonToken.END_OBJECT) {
      if (parser.currentToken() == JsonToken.FIELD_NAME) {
        val key = parser.currentName()
        parser.nextToken()
        args += (key -> readToolValue(parser))
      }
    }
    args.toMap
  }

  private def readToolValue(
      parser: software.amazon.awssdk.thirdparty.jackson.core.JsonParser
  ): ToolValue = {
    parser.currentToken() match {
      case JsonToken.VALUE_STRING => StringValue(parser.getValueAsString(""))
      case JsonToken.VALUE_NUMBER_INT =>
        val longVal = parser.getLongValue
        if (longVal >= Int.MinValue && longVal <= Int.MaxValue)
          IntValue(longVal.toInt)
        else DecimalValue(longVal.toDouble)
      case JsonToken.VALUE_NUMBER_FLOAT =>
        val doubleVal = parser.getDoubleValue
        if (
          doubleVal.isWhole && doubleVal >= Int.MinValue && doubleVal <= Int.MaxValue
        )
          IntValue(doubleVal.toInt)
        else
          DecimalValue(doubleVal)
      case JsonToken.VALUE_TRUE                           => BooleanValue(true)
      case JsonToken.VALUE_FALSE                          => BooleanValue(false)
      case JsonToken.VALUE_NULL                           => NullValue
      case JsonToken.START_OBJECT | JsonToken.START_ARRAY =>
        JsonValue(serializeCurrentStructure(parser))
      case _ =>
        StringValue(parser.getValueAsString(""))
    }
  }

  private def serializeCurrentStructure(
      parser: software.amazon.awssdk.thirdparty.jackson.core.JsonParser
  ): String = {
    val sw = new StringWriter()
    val gen = jsonFactory.createGenerator(sw)
    gen.copyCurrentStructure(parser)
    gen.close()
    sw.toString
  }

  /** Parses a JSON string representing an array of strings into a List[String].
    */
  def parseStringList(json: String): List[String] = {
    val parser = jsonFactory.createParser(json)
    val list = scala.collection.mutable.ListBuffer[String]()
    try {
      if (parser.nextToken() == JsonToken.START_ARRAY) {
        while (
          parser.nextToken() != JsonToken.END_ARRAY && parser
            .currentToken() != null
        ) {
          if (parser.currentToken() == JsonToken.VALUE_STRING) {
            list += parser.getValueAsString("")
          } else {
            val _ = parser.skipChildren()
          }
        }
      }
    } catch {
      case ex: Exception => ErrorHandler.logSilentError("parseStringList", ex)
    } finally {
      parser.close()
    }
    list.toList
  }
}
