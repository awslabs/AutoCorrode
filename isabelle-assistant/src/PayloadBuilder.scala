/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import software.amazon.awssdk.thirdparty.jackson.core.{JsonFactory, JsonGenerator, JsonToken}
import java.io.StringWriter

/**
 * Builds JSON request payloads for Anthropic models on AWS Bedrock.
 * Extracted from BedrockClient for testability and separation of concerns.
 *
 * Supports only Anthropic Claude models. The Assistant enforces this requirement
 * via BedrockClient.requireAnthropicModel() which rejects non-Anthropic models
 * before payload construction.
 *
 * Payloads deliberately omit `temperature`: newer Claude models (Opus 4.7+)
 * reject the deprecated field, and earlier models default sensibly in its
 * absence.
 */
object PayloadBuilder {
  private val jsonFactory = new JsonFactory()

  // --- Chat payloads ---

  /**
   * Build request payload for chat-style interactions (Anthropic only).
   *
   * @param systemPrompt The system prompt
   * @param messages The conversation history as (role, content) pairs
   * @param maxTokens Maximum tokens to generate
   * @return JSON payload string
   */
  def buildChatPayload(systemPrompt: String, messages: List[(String, String)], maxTokens: Int): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      g.writeStringField("system", systemPrompt)
      g.writeArrayFieldStart("messages")
      for ((role, content) <- messages) {
        g.writeStartObject()
        g.writeStringField("role", role)
        g.writeStringField("content", content)
        g.writeEndObject()
      }
      g.writeEndArray()
    }
  }

  // --- Anthropic tool-use payloads ---

  /** Build Anthropic payload with tools. Messages may contain structured content (JSON arrays). */
  def buildAnthropicToolPayload(
    systemPrompt: String, messages: List[(String, String)],
    maxTokens: Int
  ): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      g.writeStringField("system", systemPrompt)
      AssistantTools.writeFilteredToolsJson(g)
      g.writeArrayFieldStart("messages")
      for ((role, content) <- messages) {
        g.writeStartObject()
        g.writeStringField("role", role)
        if (isAnthropicStructuredContent(content)) {
          g.writeFieldName("content")
          g.writeRawValue(content)
        } else {
          g.writeStringField("content", content)
        }
        g.writeEndObject()
      }
      g.writeEndArray()
    }
  }

  /** Build Anthropic payload with planning tools only (read-only exploration).
    * Used by planning sub-agents to prevent write operations and recursion. */
  def buildPlanningAgentToolPayload(
    systemPrompt: String, messages: List[(String, String)],
    maxTokens: Int
  ): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      g.writeStringField("system", systemPrompt)
      AssistantTools.writePlanningToolsJson(g)
      g.writeArrayFieldStart("messages")
      for ((role, content) <- messages) {
        g.writeStartObject()
        g.writeStringField("role", role)
        if (isAnthropicStructuredContent(content)) {
          g.writeFieldName("content")
          g.writeRawValue(content)
        } else {
          g.writeStringField("content", content)
        }
        g.writeEndObject()
      }
      g.writeEndArray()
    }
  }

  /** Only treat content as raw JSON when it is a valid Anthropic content-block array. */
  private[assistant] def isAnthropicStructuredContent(content: String): Boolean = {
    val trimmed = content.trim
    if (!trimmed.startsWith("[")) return false
    val parser = jsonFactory.createParser(trimmed)
    try {
      if (parser.nextToken() != JsonToken.START_ARRAY) return false
      var token = parser.nextToken()
      while (token != null && token != JsonToken.END_ARRAY) {
        if (token != JsonToken.START_OBJECT) return false
        var hasValidType = false
        while (parser.nextToken() != JsonToken.END_OBJECT) {
          if (parser.currentToken() == JsonToken.FIELD_NAME) {
            val fieldName = parser.currentName()
            val valueToken = parser.nextToken()
            if (
              fieldName == "type" &&
              valueToken == JsonToken.VALUE_STRING &&
              parser.getValueAsString("").trim.nonEmpty
            ) {
              hasValidType = true
            } else {
              val _ = parser.skipChildren()
            }
          }
        }
        if (!hasValidType) return false
        token = parser.nextToken()
      }
      token == JsonToken.END_ARRAY
    } catch {
      case _: Exception => false
    } finally {
      parser.close()
    }
  }

  /** Build Anthropic payload with a single forced tool for structured output.
    * Uses tool_choice to guarantee the response is a tool_use block matching the schema.
    * Does NOT include agentic tools — only the synthetic schema tool. */
  def buildAnthropicStructuredPayload(
    systemPrompt: String, messages: List[(String, String)],
    schema: StructuredResponseSchema,
    maxTokens: Int
  ): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      if (systemPrompt.nonEmpty) g.writeStringField("system", systemPrompt)
      // Single synthetic tool from schema
      g.writeArrayFieldStart("tools")
      g.writeStartObject()
      g.writeStringField("name", schema.name)
      g.writeStringField("description", schema.description)
      g.writeFieldName("input_schema")
      g.writeRawValue(schema.jsonSchema)
      g.writeEndObject()
      g.writeEndArray()
      // Force the model to call this tool
      g.writeObjectFieldStart("tool_choice")
      g.writeStringField("type", "tool")
      g.writeStringField("name", schema.name)
      g.writeEndObject()
      // Messages
      g.writeArrayFieldStart("messages")
      for ((role, content) <- messages) {
        g.writeStartObject()
        g.writeStringField("role", role)
        if (isAnthropicStructuredContent(content)) {
          g.writeFieldName("content")
          g.writeRawValue(content)
        } else {
          g.writeStringField("content", content)
        }
        g.writeEndObject()
      }
      g.writeEndArray()
    }
  }

  /** Write a JSON object using Jackson's JsonGenerator, which handles all escaping. */
  def writeJson(body: JsonGenerator => Unit): String = {
    val sw = new StringWriter()
    val gen = jsonFactory.createGenerator(sw)
    gen.writeStartObject()
    body(gen)
    gen.writeEndObject()
    gen.close()
    sw.toString
  }
}
