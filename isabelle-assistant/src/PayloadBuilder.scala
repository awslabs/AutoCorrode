/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import software.amazon.awssdk.thirdparty.jackson.core.{JsonFactory, JsonGenerator, JsonToken}
import java.io.StringWriter

/**
 * Builds JSON request payloads for different Bedrock model providers.
 * Extracted from BedrockClient for testability and separation of concerns.
 *
 * Supports: Anthropic (Claude), Meta (Llama 2/3+), Mistral, Amazon (Titan),
 * and a generic fallback format.
 */
object PayloadBuilder {
  private val jsonFactory = new JsonFactory()

  // --- Provider detection ---

  /** Check if a model ID belongs to a given provider (e.g., "anthropic", "meta").
   *  Handles CRIS-prefixed IDs like "us.anthropic.claude-..." and global inference profiles. */
  def isProvider(modelId: String, provider: String): Boolean = {
    val stripped = if (modelId.matches("^(us|eu|ap|global)\\..*")) modelId.dropWhile(_ != '.').drop(1) else modelId
    stripped.startsWith(provider + ".")
  }

  /** Detect Llama 3 or later models (llama3, llama-3, llama4, etc.) vs Llama 2.
   *  Only returns true for models that explicitly contain a Llama 3+ version marker.
   *  Models with no recognisable version marker default to Llama 2 format to be safe. */
  def isLlama3OrLater(modelId: String): Boolean = {
    val lower = modelId.toLowerCase
    lower.contains("llama3") || lower.contains("llama-3") ||
    lower.contains("llama4") || lower.contains("llama-4")
  }

  // --- Chat payloads ---

  /**
   * Build request payload for chat-style interactions.
   *
   * @param modelId The Bedrock model identifier
   * @param systemPrompt The system prompt
   * @param messages The conversation history as (role, content) pairs
   * @param temperature The sampling temperature (0.0-1.0)
   * @param maxTokens Maximum tokens to generate
   * @return JSON payload string
   */
  def buildChatPayload(modelId: String, systemPrompt: String, messages: List[(String, String)], temperature: Double, maxTokens: Int): String = {
    if (isProvider(modelId, "anthropic")) {
      writeJson { g =>
        g.writeStringField("anthropic_version", "bedrock-2023-05-31")
        g.writeNumberField("max_tokens", maxTokens)
        g.writeNumberField("temperature", temperature)
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
    } else if (isProvider(modelId, "meta")) {
      if (isLlama3OrLater(modelId)) {
        val historyText = messages.map { case (role, content) =>
          s"<|start_header_id|>$role<|end_header_id|>\n\n$content<|eot_id|>"
        }.mkString("")
        writeJson { g =>
          g.writeStringField("prompt", s"<|begin_of_text|><|start_header_id|>system<|end_header_id|>\n\n$systemPrompt<|eot_id|>$historyText<|start_header_id|>assistant<|end_header_id|>\n\n")
          g.writeNumberField("max_gen_len", maxTokens)
          g.writeNumberField("temperature", temperature)
        }
      } else {
        val historyText = messages.map { case (role, content) =>
          if (role == "user") s"[INST] $content [/INST]"
          else content
        }.mkString("\n")
        writeJson { g =>
          g.writeStringField("prompt", s"<<SYS>>\n$systemPrompt\n<</SYS>>\n\n$historyText")
          g.writeNumberField("max_gen_len", maxTokens)
          g.writeNumberField("temperature", temperature)
        }
      }
    } else if (isProvider(modelId, "mistral")) {
      val historyText = messages.map { case (role, content) =>
        if (role == "user") s"[INST] $content [/INST]"
        else content
      }.mkString("\n")
      writeJson { g =>
        g.writeStringField("prompt", s"<s>[INST] $systemPrompt [/INST]\n$historyText")
        g.writeNumberField("max_tokens", maxTokens)
        g.writeNumberField("temperature", temperature)
      }
    } else {
      writeJson { g =>
        g.writeArrayFieldStart("messages")
        g.writeStartObject()
        g.writeStringField("role", "system")
        g.writeStringField("content", systemPrompt)
        g.writeEndObject()
        for ((role, content) <- messages) {
          g.writeStartObject()
          g.writeStringField("role", role)
          g.writeStringField("content", content)
          g.writeEndObject()
        }
        g.writeEndArray()
        g.writeNumberField("max_tokens", maxTokens)
        g.writeNumberField("temperature", temperature)
      }
    }
  }

  // --- Single prompt payloads ---

  /**
   * Build request payload for single prompt interactions.
   *
   * @param modelId The Bedrock model identifier
   * @param prompt The complete prompt text
   * @param temperature The sampling temperature (0.0-1.0)
   * @param maxTokens Maximum tokens to generate
   * @param systemPrompt Optional system prompt (only used for Anthropic models)
   * @return JSON payload string
   */
  def buildPayload(modelId: String, prompt: String, temperature: Double, maxTokens: Int, systemPrompt: Option[String] = None): String = {
    if (isProvider(modelId, "anthropic")) {
      writeJson { g =>
        g.writeStringField("anthropic_version", "bedrock-2023-05-31")
        g.writeNumberField("max_tokens", maxTokens)
        g.writeNumberField("temperature", temperature)
        systemPrompt.filter(_.nonEmpty).foreach(s => g.writeStringField("system", s))
        g.writeArrayFieldStart("messages")
        g.writeStartObject()
        g.writeStringField("role", "user")
        g.writeStringField("content", prompt)
        g.writeEndObject()
        g.writeEndArray()
      }
    } else if (isProvider(modelId, "meta")) {
      if (isLlama3OrLater(modelId)) {
        writeJson { g =>
          g.writeStringField("prompt", s"<|begin_of_text|><|start_header_id|>user<|end_header_id|>\n\n$prompt<|eot_id|><|start_header_id|>assistant<|end_header_id|>\n\n")
          g.writeNumberField("max_gen_len", maxTokens)
          g.writeNumberField("temperature", temperature)
        }
      } else {
        writeJson { g =>
          g.writeStringField("prompt", prompt)
          g.writeNumberField("max_gen_len", maxTokens)
          g.writeNumberField("temperature", temperature)
        }
      }
    } else if (isProvider(modelId, "mistral")) {
      writeJson { g =>
        g.writeStringField("prompt", s"<s>[INST] $prompt [/INST]")
        g.writeNumberField("max_tokens", maxTokens)
        g.writeNumberField("temperature", temperature)
      }
    } else if (isProvider(modelId, "amazon")) {
      writeJson { g =>
        g.writeStringField("inputText", prompt)
        g.writeObjectFieldStart("textGenerationConfig")
        g.writeNumberField("maxTokenCount", maxTokens)
        g.writeNumberField("temperature", temperature)
        g.writeEndObject()
      }
    } else {
      writeJson { g =>
        g.writeArrayFieldStart("messages")
        g.writeStartObject()
        g.writeStringField("role", "user")
        g.writeStringField("content", prompt)
        g.writeEndObject()
        g.writeEndArray()
        g.writeNumberField("max_tokens", maxTokens)
        g.writeNumberField("temperature", temperature)
      }
    }
  }

  // --- Anthropic tool-use payloads ---

  /** Build Anthropic payload with tools. Messages may contain structured content (JSON arrays). */
  def buildAnthropicToolPayload(
    systemPrompt: String, messages: List[(String, String)],
    temperature: Double, maxTokens: Int
  ): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      g.writeNumberField("temperature", temperature)
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
              parser.skipChildren()
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
    temperature: Double, maxTokens: Int
  ): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      g.writeNumberField("temperature", temperature)
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
