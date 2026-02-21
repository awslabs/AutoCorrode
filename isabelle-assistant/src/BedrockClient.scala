/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import software.amazon.awssdk.services.bedrockruntime.BedrockRuntimeClient
import software.amazon.awssdk.services.bedrockruntime.model.InvokeModelRequest
import software.amazon.awssdk.core.SdkBytes
import software.amazon.awssdk.regions.Region
import software.amazon.awssdk.thirdparty.jackson.core.JsonFactory
import java.io.StringWriter
import scala.util.control.NonFatal

/**
 * AWS Bedrock client for LLM interactions.
 *
 * Provides robust, retry-enabled communication with AWS Bedrock models
 * using Anthropic Claude via Bedrock.
 * Handles connection pooling, error recovery, and response parsing.
 *
 * JSON payload construction is delegated to [[PayloadBuilder]] and response
 * parsing to [[ResponseParser]] — this object handles only transport,
 * retry, rate-limiting, circuit-breaking, caching, and the Anthropic
 * tool-use agentic loop.
 */
object BedrockClient {
  @volatile private var cachedClient: Option[(String, BedrockRuntimeClient)] = None
  private val clientLock = new Object()
  private val maxRetries = AssistantConstants.MAX_RETRY_ATTEMPTS
  private val baseRetryDelayMs = AssistantConstants.RETRY_BASE_DELAY_MS
  private val jsonFactory = new JsonFactory()

  /** Simple rate limiter: tracks the last API call timestamp and enforces a minimum
   *  interval between calls to avoid overwhelming the Bedrock API. */
  private val rateLimitLock = new Object()
  @volatile private var lastApiCallMs = 0L
  private val minIntervalMs = 200L // minimum 200ms between API calls

  enum ModelValidationError {
    case MissingModel
    case InvalidFormat(modelId: String)
    case UnsupportedProvider(modelId: String)

    def message: String = this match {
      case MissingModel =>
        "No model configured. Use :set model <model-id> or configure in Plugin Options."
      case InvalidFormat(modelId) =>
        s"Invalid model ID format: $modelId"
      case UnsupportedProvider(modelId) =>
        s"Unsupported model '$modelId'. Only Anthropic models are supported because tool-use requires the Anthropic API."
    }
  }

  private[assistant] def validateAnthropicModel(
      modelId: String
  ): Either[ModelValidationError, Unit] = {
    if (modelId.isEmpty) Left(ModelValidationError.MissingModel)
    else if (!modelId.matches("^[a-zA-Z0-9._:/-]+$"))
      Left(ModelValidationError.InvalidFormat(modelId))
    else if (!BedrockModels.isAnthropicModelId(modelId))
      Left(ModelValidationError.UnsupportedProvider(modelId))
    else Right(())
  }

  private[assistant] def requireAnthropicModel(modelId: String): Unit = {
    validateAnthropicModel(modelId) match {
      case Right(_) => ()
      case Left(ModelValidationError.MissingModel) =>
        throw new IllegalStateException(ModelValidationError.MissingModel.message)
      case Left(err) =>
        throw new IllegalArgumentException(err.message)
    }
  }

  /** Circuit breaker: after consecutive failures, fail fast without calling the API.
   *  Resets after a cooldown period or on a successful call. */
  private val circuitBreakerLock = new Object()
  @volatile private var consecutiveFailures = 0
  @volatile private var circuitOpenUntilMs = 0L
  private val circuitBreakerThreshold = 5      // open after 5 consecutive failures
  private val circuitBreakerCooldownMs = 30000L // 30 seconds cooldown

  private def checkCircuitBreaker(): Unit = {
    if (consecutiveFailures >= circuitBreakerThreshold) {
      val now = System.currentTimeMillis()
      if (now < circuitOpenUntilMs) {
        val remaining = (circuitOpenUntilMs - now) / 1000
        throw new RuntimeException(
          s"Service temporarily unavailable (${remaining}s cooldown after $consecutiveFailures consecutive failures). " +
          "Check your network connection and AWS credentials.")
      } else {
        // Cooldown elapsed — allow a probe request and reduce failure count to threshold-1
        // so that another failure will re-open the circuit, but a success will reset fully
        circuitBreakerLock.synchronized {
          if (now >= circuitOpenUntilMs && consecutiveFailures >= circuitBreakerThreshold) {
            Output.writeln("[Assistant] Circuit breaker: cooldown elapsed, allowing probe request")
            consecutiveFailures = circuitBreakerThreshold - 1
            circuitOpenUntilMs = 0L
          }
        }
      }
    }
  }

  private def recordSuccess(): Unit = circuitBreakerLock.synchronized {
    if (consecutiveFailures > 0) {
      Output.writeln(s"[Assistant] Circuit breaker: reset after success (was $consecutiveFailures failures)")
      consecutiveFailures = 0
      circuitOpenUntilMs = 0L
    }
  }

  private def recordFailure(): Unit = circuitBreakerLock.synchronized {
    consecutiveFailures += 1
    if (consecutiveFailures >= circuitBreakerThreshold) {
      circuitOpenUntilMs = System.currentTimeMillis() + circuitBreakerCooldownMs
      Output.writeln(s"[Assistant] Circuit breaker OPEN: $consecutiveFailures consecutive failures, cooldown ${circuitBreakerCooldownMs / 1000}s")
    }
  }

  private def enforceRateLimit(): Unit = {
    rateLimitLock.synchronized {
      val now = System.currentTimeMillis()
      val elapsed = now - lastApiCallMs
      if (elapsed < minIntervalMs) {
        Thread.sleep(minIntervalMs - elapsed)
      }
      lastApiCallMs = System.currentTimeMillis()
    }
  }

  /**
   * Get or create a Bedrock client for the configured region.
   * Uses @volatile + double-checked locking to reduce contention.
   */
  private def getClient: BedrockRuntimeClient = {
    val region = AssistantOptions.getRegion
    cachedClient match {
      case Some((r, c)) if r == region => c
      case _ => clientLock.synchronized {
        // Double-check after acquiring lock
        cachedClient match {
          case Some((r, c)) if r == region => c
          case _ =>
            cachedClient.foreach { case (_, client) =>
              try { client.close() }
              catch { case NonFatal(_) => () }
            }
            val client = ErrorHandler.withErrorHandling("create Bedrock client") {
              val newClient = BedrockRuntimeClient.builder()
                .region(Region.of(region))
                .build()
              ErrorHandler.registerResource(newClient)
              newClient
            }.getOrElse(throw new RuntimeException(s"Failed to create Bedrock client for region $region"))
            cachedClient = Some((region, client))
            client
        }
      }
    }
  }

  private val currentViewTL = new ThreadLocal[org.gjt.sp.jedit.View]()

  private enum BedrockRole(val wireValue: String) {
    case User extends BedrockRole("user")
    case Assistant extends BedrockRole("assistant")
  }

  private object BedrockRole {
    def fromWire(value: String): Option[BedrockRole] = value match {
      case "user"      => Some(User)
      case "assistant" => Some(Assistant)
      case _           => None
    }
  }

  private case class ChatTurn(role: BedrockRole, content: String)

  private def toTurns(messages: List[(String, String)]): List[ChatTurn] = {
    val (valid, dropped) = messages.foldLeft((List.empty[ChatTurn], 0)) {
      case ((acc, dropCount), (role, content)) =>
        BedrockRole.fromWire(role) match {
          case Some(r) => (acc :+ ChatTurn(r, content), dropCount)
          case None    => (acc, dropCount + 1)
        }
    }
    if (dropped > 0)
      Output.warning(
        s"[Assistant] Dropped $dropped message(s) with unsupported Bedrock role(s)"
      )
    valid
  }

  private def fromTurns(messages: List[ChatTurn]): List[(String, String)] =
    messages.map(m => (m.role.wireValue, m.content))

  /** Set the current view for tool execution context. Called before agentic invocations. */
  def setCurrentView(view: org.gjt.sp.jedit.View): Unit = { currentViewTL.set(view) }

  /**
   * Invoke chat with retry logic and proper error handling.
   *
   * @param systemPrompt The system prompt for the conversation
   * @param messages The conversation history as (role, content) pairs
   * @return The LLM response text
   */
  def invokeChat(systemPrompt: String, messages: List[(String, String)]): String = {
    ErrorHandler.logOperation("invokeChat") {
      try {
        retryWithBackoff(maxRetries) {
          invokeChatInternal(systemPrompt, toTurns(messages))
        }
      } finally {
        currentViewTL.remove()
      }
    }
  }

  /**
   * Invoke with conversational context: appends the prompt as the latest user
   * message to the current chat history and sends the full conversation to the LLM.
   * For Anthropic models, enables tool use with an agentic loop.
   * 
   * Thread-safe: takes an atomic snapshot of history to avoid race conditions.
   */
  def invokeInContext(prompt: String): String = {
    ErrorHandler.logOperation("invokeInContext") {
      // Set view for tool execution — use the active jEdit view
      Option(org.gjt.sp.jedit.jEdit.getActiveView).foreach(setCurrentView)
      // System prompt is empty here — invokeChatInternal prepends getSystemPrompt automatically
      // Take atomic snapshot of history before constructing messages to avoid races
      val history =
        ChatAction.getHistorySnapshot
          .filterNot(_.transient)
          .flatMap(m => BedrockRole.fromWire(m.role.wireValue).map(ChatTurn(_, m.content)))
      val messages = history :+ ChatTurn(BedrockRole.User, prompt)
      try {
        retryWithBackoff(maxRetries) {
          invokeChatInternal("", messages)
        }
      } finally {
        currentViewTL.remove()
      }
    }
  }

  /**
   * Invoke single prompt with retry logic, caching, and proper error handling.
   * Stateless — no conversation history. Use for self-contained prompts.
   * Results are cached by exact prompt text to avoid redundant API calls.
   *
   * @param prompt The prompt text
   * @return The LLM response
   * @throws RuntimeException if all retries fail
   */
  def invoke(prompt: String): String = {
    ErrorHandler.logOperation("invoke") {
      // Check cache first
      LLMResponseCache.get(prompt) match {
        case Some(cachedResponse) =>
          Output.writeln(s"[Assistant] Using cached response (${cachedResponse.length} chars)")
          cachedResponse
        case None =>
          val response = retryWithBackoff(maxRetries) {
            invokeInternal(prompt)
          }
          // Cache the response
          LLMResponseCache.put(prompt, response)
          response
      }
    }
  }

  /**
   * Invoke single prompt bypassing the response cache.
   * Use for retry operations where the prompt may be identical to a previous
   * attempt but a fresh response is required (e.g., verification retries).
   *
   * @param prompt The prompt text
   * @return The LLM response
   * @throws RuntimeException if all retries fail
   */
  def invokeNoCache(prompt: String): String = {
    ErrorHandler.logOperation("invokeNoCache") {
      retryWithBackoff(maxRetries) {
        invokeInternal(prompt)
      }
    }
  }

  // --- Structured output methods (forced tool_choice) ---

  import ResponseParser.ToolArgs

  /**
   * Invoke a single prompt with structured output via forced tool_choice.
   * Stateless with cache. Returns parsed tool arguments.
   */
  def invokeStructured(prompt: String, schema: StructuredResponseSchema, systemPrompt: String = ""): ToolArgs = {
    ErrorHandler.logOperation("invokeStructured") {
      val cacheKey = s"structured:${schema.name}:$prompt"
      LLMResponseCache.get(cacheKey) match {
        case Some(cached) =>
          Output.writeln(s"[Assistant] Using cached structured response")
          ResponseParser.parseToolArgsJsonObject(cached)
        case None =>
          val args = retryWithBackoff(maxRetries) {
            invokeStructuredInternal(prompt, schema, systemPrompt)
          }
          LLMResponseCache.put(cacheKey, ResponseParser.toolArgsToJson(args))
          args
      }
    }
  }

  /**
   * Invoke with conversational context and structured output via forced tool_choice.
   * Appends the prompt to the current chat history. Returns parsed tool arguments.
   */
  def invokeInContextStructured(prompt: String, schema: StructuredResponseSchema): ToolArgs = {
    ErrorHandler.logOperation("invokeInContextStructured") {
      Option(org.gjt.sp.jedit.jEdit.getActiveView).foreach(setCurrentView)
      val history =
        ChatAction.getHistorySnapshot
          .filterNot(_.transient)
          .flatMap(m => BedrockRole.fromWire(m.role.wireValue).map(ChatTurn(_, m.content)))
      val messages = history :+ ChatTurn(BedrockRole.User, prompt)
      try {
        retryWithBackoff(maxRetries) {
          invokeStructuredChatInternal(messages, schema)
        }
      } finally {
        currentViewTL.remove()
      }
    }
  }

  /**
   * Invoke a single prompt with structured output, bypassing cache.
   * Use for retry operations where a fresh response is required.
   */
  def invokeNoCacheStructured(prompt: String, schema: StructuredResponseSchema): ToolArgs = {
    ErrorHandler.logOperation("invokeNoCacheStructured") {
      retryWithBackoff(maxRetries) {
        invokeStructuredInternal(prompt, schema, "")
      }
    }
  }

  /** Single-prompt structured invocation. */
  private def invokeStructuredInternal(
    prompt: String, schema: StructuredResponseSchema, systemPrompt: String
  ): ToolArgs = {
    val modelId = AssistantOptions.getModelId
    requireAnthropicModel(modelId)
    val temperature = AssistantOptions.getTemperature
    val maxTokens = AssistantOptions.getMaxTokens

    val fullSystemPrompt = List(PromptLoader.getSystemPrompt, systemPrompt).filter(_.nonEmpty).mkString("\n\n")

    Output.writeln(s"[Assistant] invokeStructured - Model: $modelId, Schema: ${schema.name}")

    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      fullSystemPrompt, List(("user", prompt)), schema, temperature, maxTokens
    )

    val request = InvokeModelRequest.builder()
      .modelId(modelId)
      .body(SdkBytes.fromUtf8String(payload))
      .build()

    enforceRateLimit()
    val response = getClient.invokeModel(request)
    val responseJson = response.body().asUtf8String()

    ResponseParser.extractForcedToolArgs(responseJson).getOrElse(
      throw new RuntimeException("Structured response contained no tool_use block")
    )
  }

  /** Chat-history structured invocation with truncation and merging. */
  private def invokeStructuredChatInternal(
    messages: List[ChatTurn],
    schema: StructuredResponseSchema
  ): ToolArgs = {
    val modelId = AssistantOptions.getModelId
    requireAnthropicModel(modelId)
    val temperature = AssistantOptions.getTemperature
    val maxTokens = AssistantOptions.getMaxTokens

    val fullSystemPrompt = PromptLoader.getSystemPrompt

    Output.writeln(s"[Assistant] invokeStructuredChat - Model: $modelId, Schema: ${schema.name}, Messages: ${messages.length}")

    val maxChars = AssistantConstants.MAX_CHAT_CONTEXT_CHARS
    val truncated = truncateTurns(messages, maxChars)
    if (truncated.length < messages.length)
      Output.writeln(s"[Assistant] invokeStructuredChat - Truncated ${messages.length - truncated.length} old messages")
    val merged = mergeConsecutiveTurns(truncated)

    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      fullSystemPrompt,
      fromTurns(merged),
      schema,
      temperature,
      maxTokens
    )

    val request = InvokeModelRequest.builder()
      .modelId(modelId)
      .body(SdkBytes.fromUtf8String(payload))
      .build()

    enforceRateLimit()
    val response = getClient.invokeModel(request)
    val responseJson = response.body().asUtf8String()

    ResponseParser.extractForcedToolArgs(responseJson).getOrElse(
      throw new RuntimeException("Structured response contained no tool_use block")
    )
  }

  /**
   * Retry an operation with exponential backoff, cancellation checks, and
   * circuit-breaker integration with capped delay.
   */
  private def retryWithBackoff[T](maxAttempts: Int)(operation: => T): T = {
    def retry(attempt: Int, lastException: Option[Exception]): T = {
      if (AssistantDockable.isCancelled)
        throw new RuntimeException("Operation cancelled")
      if (attempt > maxAttempts) {
        recordFailure()
        val msg = lastException.map(_.getMessage).getOrElse("Unknown error")
        throw new RuntimeException(ErrorHandler.makeUserFriendly(msg, "API call"))
      }

      try {
        checkCircuitBreaker()
        val result = operation
        recordSuccess()
        result
      } catch {
        case ex: Exception =>
          if (AssistantDockable.isCancelled)
            throw new RuntimeException("Operation cancelled")
          if (attempt < maxAttempts) {
            // Cap exponential backoff at 30 seconds
            val delay = math.min(30000L, baseRetryDelayMs * math.pow(2, attempt - 1).toLong)
            Output.writeln(s"[Assistant] Attempt $attempt failed, retrying in ${delay}ms: ${ErrorHandler.makeUserFriendly(ex.getMessage, "request")}")
            Thread.sleep(delay)
            retry(attempt + 1, Some(ex))
          } else {
            // Final attempt failed - record failure before throwing
            recordFailure()
            throw new RuntimeException(ErrorHandler.makeUserFriendly(ex.getMessage, "API call"), ex)
          }
      }
    }

    retry(1, None)
  }

  /** Truncate old typed messages to fit within context budget, keeping the most recent. */
  private def truncateTurns(
      messages: List[ChatTurn],
      maxChars: Int,
      systemCost: Int = 0
  ): List[ChatTurn] = {
    val available = math.max(0, maxChars - systemCost)
    if (available <= 0) {
      Output.warning(s"[Assistant] System prompt ($systemCost chars) exceeds context budget ($maxChars chars)")
      List.empty
    } else {
      val reversed = messages.reverse
      var accumulated = 0
      var kept = 0
      for (msg <- reversed if accumulated + msg.content.length <= available) {
        accumulated += msg.content.length
        kept += 1
      }
      if (kept > 0) {
        messages.takeRight(kept)
      } else if (messages.nonEmpty) {
        val lastMsg = messages.last
        if (lastMsg.content.length > available && available > 0)
          List(lastMsg.copy(content = lastMsg.content.take(available) + "\n[... truncated]"))
        else List(lastMsg)
      } else List.empty
    }
  }

  /** Public tuple-based wrapper used by tests. */
  private[assistant] def truncateMessages(
      messages: List[(String, String)],
      maxChars: Int,
      systemCost: Int = 0
  ): List[(String, String)] =
    fromTurns(truncateTurns(toTurns(messages), maxChars, systemCost))

  /** Merge consecutive same-role messages (Anthropic requires strict alternation). */
  private def mergeConsecutiveTurns(messages: List[ChatTurn]): List[ChatTurn] =
    messages.foldLeft(List.empty[ChatTurn]) {
      case (acc, msg) if acc.nonEmpty && acc.last.role == msg.role =>
        acc.init :+ acc.last.copy(content = acc.last.content + "\n\n" + msg.content)
      case (acc, msg) => acc :+ msg
    }

  /** Public tuple-based wrapper used by tests. */
  private[assistant] def mergeConsecutiveRoles(
      messages: List[(String, String)]
  ): List[(String, String)] =
    fromTurns(mergeConsecutiveTurns(toTurns(messages)))

  /**
   * Internal implementation of chat invocation.
   * Delegates payload construction to [[PayloadBuilder]] and response parsing
   * to [[ResponseParser]].
   */
  private def invokeChatInternal(
      systemPrompt: String,
      messages: List[ChatTurn]
  ): String = {
    val modelId = AssistantOptions.getModelId
    requireAnthropicModel(modelId)

    val temperature = AssistantOptions.getTemperature
    val maxTokens = AssistantOptions.getMaxTokens

    val fullSystemPrompt = List(PromptLoader.getSystemPrompt, systemPrompt).filter(_.nonEmpty).mkString("\n\n")

    Output.writeln(s"[Assistant] invokeChat - Model: $modelId, Messages: ${messages.length}")

    val maxChars = AssistantConstants.MAX_CHAT_CONTEXT_CHARS
    val systemCost = if (PayloadBuilder.isProvider(modelId, "anthropic")) 0 else fullSystemPrompt.length
    val truncated = truncateTurns(messages, maxChars, systemCost)
    if (truncated.length < messages.length)
      Output.writeln(s"[Assistant] invokeChat - Truncated ${messages.length - truncated.length} old messages")

    val merged = mergeConsecutiveTurns(truncated)

    invokeChatWithTools(modelId, fullSystemPrompt, merged, temperature, maxTokens)
  }

  /**
   * Anthropic tool-use agentic loop. Sends messages with tool definitions,
   * executes any tool_use requests, feeds results back, and repeats until
   * the model responds with text only or the iteration limit is reached.
   */
  private def invokeChatWithTools(
    modelId: String,
    systemPrompt: String,
    initialMessages: List[ChatTurn],
    temperature: Double, maxTokens: Int
  ): String = {
    val maxIter = AssistantOptions.getMaxToolIterations
    // Build structured message list: each entry is (role, json_content_string)
    // For simple text messages, content is just the string.
    // For tool results, content is a JSON array of tool_result blocks.
    val msgBuf = scala.collection.mutable.ListBuffer[ChatTurn]()
    msgBuf ++= initialMessages

    var iteration = 0
    val textParts = scala.collection.mutable.ListBuffer[String]()
    var continue = true
    // Improved stuck-loop detection: track last 6 tool calls (window of 6)
    val recentCalls = scala.collection.mutable.Queue[String]()
    val LOOP_DETECTION_WINDOW = 6

    while (continue) {
      iteration += 1
      if (AssistantDockable.isCancelled) throw new RuntimeException("Operation cancelled")
      pruneToolLoopMessagesInPlace(msgBuf, AssistantConstants.MAX_CHAT_CONTEXT_CHARS)

      // Check if we've hit the iteration limit
      val hitLimit = maxIter match {
        case Some(limit) => iteration > limit
        case None => false
      }
      if (hitLimit) {
        // Send a message to the model informing it we've hit the limit
        Output.warning(s"[Assistant] Hit max tool iteration limit ($iteration iterations)")
        msgBuf += ChatTurn(
          BedrockRole.User,
          "You have reached the maximum tool iteration limit. Please provide a summary of what you've learned and any conclusions you can make without additional tool calls."
        )
        
        // Make one final call to get the model's summary
        val payload = PayloadBuilder.buildAnthropicToolPayload(
          systemPrompt,
          fromTurns(msgBuf.toList),
          temperature,
          maxTokens
        )
        val request = InvokeModelRequest.builder()
          .modelId(modelId)
          .body(SdkBytes.fromUtf8String(payload))
          .build()
        
        enforceRateLimit()
        try {
          val response = getClient.invokeModel(request)
          val responseJson = response.body().asUtf8String()
          val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(responseJson)
          val summaryText = blocks.collect { case ResponseParser.TextBlock(t) => t }
          if (summaryText.nonEmpty) textParts ++= summaryText
        } catch {
          case ex: Exception => 
            Output.warning(s"[Assistant] Final summary call failed: ${ex.getMessage}")
        }
        continue = false
      } else {
        val payload = PayloadBuilder.buildAnthropicToolPayload(
          systemPrompt,
          fromTurns(msgBuf.toList),
          temperature,
          maxTokens
        )
        val request = InvokeModelRequest.builder()
          .modelId(modelId)
          .body(SdkBytes.fromUtf8String(payload))
          .build()

        enforceRateLimit()
        val response = getClient.invokeModel(request)
        val responseJson = response.body().asUtf8String()
        val (blocks, stopReason) = ResponseParser.parseAnthropicContentBlocks(responseJson)

        // Collect text from this response
        val currentTextParts = blocks.collect { case ResponseParser.TextBlock(t) => t }
        val toolUses = blocks.collect { case t: ResponseParser.ToolUseBlock => t }

        // Append (not replace) text parts from this iteration
        if (currentTextParts.nonEmpty) textParts ++= currentTextParts

        if (toolUses.isEmpty) {
          // No tool calls — we're done
          continue = false
        } else {
          // Append assistant message with the raw response content
          msgBuf += ChatTurn(BedrockRole.Assistant, rawContentJson(blocks))

          // Execute each tool and build tool_result message
          val view = Option(currentViewTL.get())
            .orElse(Option(org.gjt.sp.jedit.jEdit.getActiveView))
            .getOrElse(throw new RuntimeException("No view available for tool execution"))
          val iterStr = maxIter.map(_.toString).getOrElse("∞")
          val resultBlocks = toolUses.map { tu =>
            // Enhanced stuck-loop detection: track tool name + ALL input params
            // This ensures different arguments produce different signatures
            val paramStr = tu.input.toSeq.sortBy(_._1).map { case (k, v) => 
              s"$k=${ResponseParser.toolValueToString(v).take(50)}" 
            }.mkString(",")
            val signature = s"${tu.name}($paramStr)"
            recentCalls.enqueue(signature)
            if (recentCalls.length > LOOP_DETECTION_WINDOW) {
              val _ = recentCalls.dequeue()
            }
            
            // Check for exact repetition (3+ identical calls in window)
            if (recentCalls.length >= 3 && recentCalls.takeRight(3).distinct.size == 1) {
              Output.warning(s"[Assistant] Detected stuck loop: same tool call '${recentCalls.last}' repeated 3+ times")
              throw new RuntimeException(s"Stuck in loop: tool '${tu.name}' called repeatedly with identical arguments and no progress. Try a different approach.")
            }
            
            // Check for alternating pattern (A-B-A-B)
            if (recentCalls.length >= 4) {
              val last4 = recentCalls.takeRight(4).toList
              if (last4(0) == last4(2) && last4(1) == last4(3)) {
                Output.warning(s"[Assistant] Detected alternating loop: ${last4(0)} <-> ${last4(1)}")
                throw new RuntimeException(s"Stuck in alternating loop between two tool calls with no progress. Try a different approach.")
              }
            }
            
            Output.writeln(s"[Assistant] Tool use ($iteration/$iterStr): ${tu.name}")
            AssistantDockable.setStatus(s"[tool] ${tu.name} ($iteration/$iterStr)...")
            // Add tool message to chat UI (skip for task list tools since they inject their own widgets)
            if (!tu.name.startsWith("task_list_")) {
              GUI_Thread.later {
                ChatAction.addToolMessage(tu.name, tu.input)
              }
            }
            val result = AssistantTools.executeToolWithPermission(tu.name, tu.input, view)

            // Display tool result in chat UI
            GUI_Thread.later {
              ChatAction.addTransient(s"→ Tool result: ${result.take(200)}${if (result.length > 200) "..." else ""}")
            }
            (tu.id, result)
          }

          // Append user message with tool results
          msgBuf += ChatTurn(BedrockRole.User, toolResultsJson(resultBlocks))
        }
      }
    }

    val finalText = textParts.mkString("\n\n")
    if (finalText.isEmpty) {
      Output.warning("[Assistant] Tool-use loop completed without text response")
      "I processed the request using tools but could not generate a text summary. Please try again or rephrase your question."
    } else {
      Output.writeln(s"[Assistant] Tool loop completed in $iteration iterations, response: ${finalText.length} chars")
      finalText
    }
  }

  private def pruneToolLoopMessagesInPlace(
      msgBuf: scala.collection.mutable.ListBuffer[ChatTurn],
      maxChars: Int
  ): Unit = {
    val pruned = prunedToolLoopTurns(msgBuf.toList, maxChars)
    if (pruned.length != msgBuf.length || pruned != msgBuf.toList) {
      val removed = msgBuf.length - pruned.length
      if (removed > 0)
        Output.writeln(
          s"[Assistant] Tool loop context pruned $removed message(s) to stay within budget"
        )
      msgBuf.clear()
      msgBuf ++= pruned
    }
  }

  private def prunedToolLoopTurns(
      messages: List[ChatTurn],
      maxChars: Int
  ): List[ChatTurn] = {
    if (messages.isEmpty) return Nil
    val budget = math.max(1, maxChars)
    val lengths = messages.map(_.content.length)
    var total = lengths.sum
    var dropCount = 0
    while (total > budget && dropCount < messages.length - 1) {
      total -= lengths(dropCount)
      dropCount += 1
    }
    val kept = messages.drop(dropCount)
    if (kept.isEmpty) Nil
    else if (total <= budget) kept
    else {
      // Single oversized tail message: keep it but trim content.
      val last = kept.last
      val keepChars = math.max(64, budget - 32)
      val trimmed =
        if (last.content.length <= keepChars) last.content
        else "[... truncated due to context budget ...]\n" + last.content
          .takeRight(keepChars)
      List(last.copy(content = trimmed))
    }
  }

  private[assistant] def prunedToolLoopMessages(
      messages: List[(String, String)],
      maxChars: Int
  ): List[(String, String)] =
    fromTurns(prunedToolLoopTurns(toTurns(messages), maxChars))

  /** Serialize content blocks as a JSON array string for the assistant message. */
  private def rawContentJson(blocks: List[ResponseParser.ContentBlock]): String = {
    val sw = new StringWriter()
    val g = jsonFactory.createGenerator(sw)
    g.writeStartArray()
    for (b <- blocks) b match {
      case ResponseParser.TextBlock(text) =>
        g.writeStartObject()
        g.writeStringField("type", "text")
        g.writeStringField("text", text)
        g.writeEndObject()
      case ResponseParser.ToolUseBlock(id, name, input) =>
        g.writeStartObject()
        g.writeStringField("type", "tool_use")
        g.writeStringField("id", id)
        g.writeStringField("name", name)
        g.writeObjectFieldStart("input")
        for ((k, v) <- input) v match {
          case ResponseParser.StringValue(s) => g.writeStringField(k, s)
          case ResponseParser.IntValue(n) => g.writeNumberField(k, n)
          case ResponseParser.DecimalValue(n) => g.writeNumberField(k, n)
          case ResponseParser.BooleanValue(b) => g.writeBooleanField(k, b)
          case ResponseParser.JsonValue(json) =>
            g.writeFieldName(k)
            g.writeRawValue(json)
          case ResponseParser.NullValue => g.writeNullField(k)
        }
        g.writeEndObject()
        g.writeEndObject()
    }
    g.writeEndArray()
    g.close()
    sw.toString
  }

  /** Serialize tool results as a JSON array string for the user message. */
  private def toolResultsJson(results: List[(String, String)]): String = {
    val sw = new StringWriter()
    val g = jsonFactory.createGenerator(sw)
    g.writeStartArray()
    for ((id, content) <- results) {
      g.writeStartObject()
      g.writeStringField("type", "tool_result")
      g.writeStringField("tool_use_id", id)
      g.writeStringField("content", content)
      g.writeEndObject()
    }
    g.writeEndArray()
    g.close()
    sw.toString
  }

  /**
   * Internal implementation of single prompt invocation.
   * Delegates payload construction to [[PayloadBuilder]] and response parsing
   * to [[ResponseParser]].
   */
  private def invokeInternal(prompt: String): String = {
    val modelId = AssistantOptions.getModelId
    requireAnthropicModel(modelId)
    
    val temperature = AssistantOptions.getTemperature
    val maxTokens = AssistantOptions.getMaxTokens
    val region = AssistantOptions.getRegion

    // Validate prompt is non-empty
    ErrorHandler.validateInput(prompt) match {
      case scala.util.Failure(ex) => throw new IllegalArgumentException(s"Invalid prompt: ${ex.getMessage}")
      case _ =>
    }

    // Get auto-discovered system prompts
    val systemPrompt = PromptLoader.getSystemPrompt

    // Validate prompt length (conservative limit: 200k chars ≈ 50k tokens for most models)
    val maxPromptChars = 200000
    val totalLength = systemPrompt.length + prompt.length
    if (totalLength > maxPromptChars) {
      throw new IllegalArgumentException(
        s"Prompt too long: $totalLength chars (limit: $maxPromptChars). " +
        "Try reducing context or simplifying the request.")
    }

    Output.writeln(s"[Assistant] Region: $region")
    Output.writeln(s"[Assistant] Model: $modelId")
    Output.writeln(s"[Assistant] Temperature: $temperature, Max tokens: $maxTokens")
    Output.writeln(s"[Assistant] Prompt length: ${totalLength} chars (system: ${systemPrompt.length}, user: ${prompt.length})")

    // Use buildChatPayload when system prompt exists to ensure it's sent as a proper system field
    val payload = if (systemPrompt.nonEmpty)
      PayloadBuilder.buildChatPayload(modelId, systemPrompt, List(("user", prompt)), temperature, maxTokens)
    else
      PayloadBuilder.buildPayload(modelId, prompt, temperature, maxTokens)

    val request = InvokeModelRequest.builder()
      .modelId(modelId)
      .body(SdkBytes.fromUtf8String(payload))
      .build()

    enforceRateLimit()
    val response = getClient.invokeModel(request)
    val responseBody = response.body().asUtf8String()

    val parsed = ResponseParser.parseResponseEither(modelId, responseBody) match {
      case Right(text) => text
      case Left(err)   => throw new RuntimeException(err.message)
    }
    Output.writeln(s"[Assistant] Parsed response length: ${parsed.length} chars")
    parsed
  }

  /**
   * Cleanup cached client resources.
   */
  def cleanup(): Unit = clientLock.synchronized {
    cachedClient.foreach { case (_, client) =>
      try { client.close() }
      catch { case NonFatal(_) => () }
    }
    cachedClient = None
  }
}
