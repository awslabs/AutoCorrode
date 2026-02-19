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
object ResponseParser {
  private val jsonFactory = new JsonFactory()

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
    if (json == null || json.trim.isEmpty)
      throw new RuntimeException("Empty response from model")

    val parser = jsonFactory.createParser(json)
    try {
      val result = extractTextField(parser, modelId)
      result.getOrElse(
        throw new RuntimeException(
          s"Could not parse model response (no text field found)"
        )
      )
    } catch {
      case e: RuntimeException => throw e
      case ex: Exception       =>
        throw new RuntimeException(
          s"Failed to parse model response: ${ex.getMessage}",
          ex
        )
    } finally {
      parser.close()
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

  def toolValueToString(value: ToolValue): String = value match {
    case StringValue(v)  => v
    case IntValue(v)     => v.toString
    case DecimalValue(v) => v.toString
    case BooleanValue(v) => v.toString
    case JsonValue(v)    => v
    case NullValue       => ""
  }

  def parseToolArgsJsonObject(json: String): ToolArgs = {
    val parser = jsonFactory.createParser(json)
    try {
      if (parser.nextToken() != JsonToken.START_OBJECT) Map.empty
      else parseToolArgsObject(parser)
    } catch {
      case _: Exception => Map.empty
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
                    parser.skipChildren()
                  }
                }
              } else {
                parser.skipChildren()
              }
            case _ =>
              parser.nextToken()
              parser.skipChildren()
          }
        }
      }
    } finally {
      parser.close()
    }

    (blocks.toList, stopReason)
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
            parser.skipChildren()
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

  /** Safely extract JSON object string from a response that might contain
    * markdown or conversational filler. Finds the first '{' and the last '}'.
    */
  def extractJsonObjectString(response: String): Option[String] = {
    val start = response.indexOf('{')
    val end = response.lastIndexOf('}')
    if (start != -1 && end != -1 && end > start) {
      Some(response.substring(start, end + 1))
    } else None
  }

  /** Parses a single string field from a JSON object string. */
  def parseStringField(json: String, fieldName: String): Option[String] = {
    val parser = jsonFactory.createParser(json)
    try {
      var result: Option[String] = None
      while (parser.nextToken() != null && result.isEmpty) {
        if (
          parser.currentToken() == JsonToken.FIELD_NAME && parser
            .currentName() == fieldName
        ) {
          parser.nextToken()
          if (parser.currentToken() == JsonToken.VALUE_STRING) {
            result = Some(parser.getValueAsString)
          }
        }
      }
      result
    } catch {
      case _: Exception => None
    } finally {
      parser.close()
    }
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
            parser.skipChildren()
          }
        }
      }
    } catch {
      case _: Exception => // ignore
    } finally {
      parser.close()
    }
    list.toList
  }
}
