/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import software.amazon.awssdk.services.bedrockruntime.BedrockRuntimeClient
import software.amazon.awssdk.services.bedrockruntime.model.InvokeModelRequest
import software.amazon.awssdk.core.SdkBytes
import software.amazon.awssdk.regions.Region
import software.amazon.awssdk.thirdparty.jackson.core.{JsonFactory, JsonParser, JsonToken}
import java.io.StringWriter
import java.util.concurrent.{CountDownLatch, TimeUnit}
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
  private val lastApiCallMs = new java.util.concurrent.atomic.AtomicLong(0L)
  private val minIntervalMs = AssistantConstants.MIN_API_INTERVAL_MS

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
   *  Resets after a cooldown period or on a successful call.
   *
   *  All state transitions are guarded by `circuitLock` so that
   *  `consecutiveFailures` and `circuitOpenUntilMs` stay consistent — they
   *  must be updated as a pair. Reads outside the lock see whatever the most
   *  recent lock-holder published (volatile via the lock's release).
   */
  private val circuitLock = new Object()
  private var consecutiveFailures: Int = 0
  private var circuitOpenUntilMs: Long = 0L
  private val circuitBreakerThreshold = 5      // open after 5 consecutive failures
  private val circuitBreakerCooldownMs = 30000L // 30 seconds cooldown

  private def checkCircuitBreaker(): Unit = circuitLock.synchronized {
    if (consecutiveFailures >= circuitBreakerThreshold) {
      val now = System.currentTimeMillis()
      if (now < circuitOpenUntilMs) {
        val remaining = (circuitOpenUntilMs - now) / 1000
        throw new RuntimeException(
          s"Service temporarily unavailable (${remaining}s cooldown after $consecutiveFailures consecutive failures). " +
          "Check your network connection and AWS credentials.")
      } else {
        // Cooldown elapsed — allow a probe request. Reduce failure count to
        // threshold-1 so that another failure will re-open the circuit, but
        // a success (which resets to 0) clears it fully.
        circuitOpenUntilMs = 0L
        consecutiveFailures = circuitBreakerThreshold - 1
        Output.writeln("[Assistant] Circuit breaker: cooldown elapsed, allowing probe request")
      }
    }
  }

  private def recordSuccess(): Unit = circuitLock.synchronized {
    if (consecutiveFailures > 0) {
      Output.writeln(s"[Assistant] Circuit breaker: reset after success (was $consecutiveFailures failures)")
      consecutiveFailures = 0
      circuitOpenUntilMs = 0L
    }
  }

  private def recordFailure(): Unit = circuitLock.synchronized {
    consecutiveFailures += 1
    if (consecutiveFailures >= circuitBreakerThreshold) {
      circuitOpenUntilMs = System.currentTimeMillis() + circuitBreakerCooldownMs
      Output.writeln(s"[Assistant] Circuit breaker OPEN: $consecutiveFailures consecutive failures, cooldown ${circuitBreakerCooldownMs / 1000}s")
    }
  }

  /**
   * Token-bucket-ish rate limiter: serialize API calls by reserving the next
   * allowed slot atomically, then sleeping only if the slot is still in the
   * future. Concurrent callers each claim distinct slots instead of all
   * sleeping for `now-lastCall` and stampeding when they wake up.
   */
  private def enforceRateLimit(): Unit = {
    var reserved = 0L
    var done = false
    while (!done) {
      val now = System.currentTimeMillis()
      val prev = lastApiCallMs.get()
      val target = math.max(now, prev + minIntervalMs)
      if (lastApiCallMs.compareAndSet(prev, target)) {
        reserved = target
        done = true
      }
    }
    val wait = reserved - System.currentTimeMillis()
    if (wait > 0) {
      try Thread.sleep(wait)
      catch {
        case _: InterruptedException =>
          // Restore the interrupt flag so downstream cancellation checks
          // (e.g. CancellationToken polling) still see the signal. Without
          // this, sleep would silently swallow the interrupt and the
          // caller would keep running past the cancel request.
          Thread.currentThread().interrupt()
      }
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

  /** Truncate on a code-point boundary so the stuck-loop signature can
    * never bisect a multi-byte UTF-8 character. `String.take(n)` works
    * on UTF-16 code units, which is fine for BMP characters but can
    * split a surrogate pair in half; matching against such a
    * half-formed signature with `distinct.size == 1` is still correct,
    * but the log messages are nicer when every truncated value is
    * valid Unicode. */
  private def truncateSafely(s: String, maxCodeUnits: Int): String = {
    if (s == null || s.length <= maxCodeUnits) s
    else {
      val lastChar = s.charAt(maxCodeUnits - 1)
      val cutoff =
        if (Character.isHighSurrogate(lastChar)) maxCodeUnits - 1
        else maxCodeUnits
      s.substring(0, cutoff)
    }
  }

  private val currentViewTL = new ThreadLocal[org.gjt.sp.jedit.View]()

  /** Track active tool loop context size for accurate context bar display.
    * Atomic because parallel planning sub-agents can update the high-water
    * mark concurrently — a plain @volatile would lose updates on concurrent
    * writes (read-modify-write is not atomic on volatile ints). */
  private val activeToolLoopContextChars = new java.util.concurrent.atomic.AtomicInteger(0)

  /** Dedicated executor for planning sub-agents.
    *
    * Previously sub-agents ran on `Isabelle_Thread.fork`, which shares a
    * pool with PIDE command processing and the I/Q backplane. Three
    * long-running HTTP tool-use loops on that pool can starve PIDE. A
    * small fixed pool (sized to the number of approaches we brainstorm
    * plus a little headroom for re-runs) keeps planning work on its own
    * thread budget while still letting the JVM reclaim threads if planning
    * isn't in use. */
  private val planningExecutor: java.util.concurrent.ExecutorService = {
    val poolSize = math.max(2, AssistantConstants.PLANNING_NUM_APPROACHES + 1)
    val threadCounter = new java.util.concurrent.atomic.AtomicInteger(0)
    java.util.concurrent.Executors.newFixedThreadPool(
      poolSize,
      (r: Runnable) => {
        val t = new Thread(r, s"assistant-planning-${threadCounter.incrementAndGet()}")
        t.setDaemon(true)
        t
      }
    )
  }

  /** Get current tool loop context size (0 if no active loop). */
  def getActiveToolLoopContextChars: Int = activeToolLoopContextChars.get()

  private[assistant] enum BedrockRole(val wireValue: String) {
    case User extends BedrockRole("user")
    case Assistant extends BedrockRole("assistant")
  }

  private[assistant] object BedrockRole {
    def fromWire(value: String): Option[BedrockRole] = value match {
      case "user"      => Some(User)
      case "assistant" => Some(Assistant)
      case _           => None
    }
  }

  private[assistant] case class ChatTurn(role: BedrockRole, content: String)

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
        ChatAction.getHistory
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
   *
   * @param modelIdOverride Optional model ID override (defaults to main model)
   */
  def invokeStructured(
      prompt: String,
      schema: StructuredResponseSchema,
      systemPrompt: String = "",
      modelIdOverride: Option[String] = None
  ): ToolArgs = {
    ErrorHandler.logOperation("invokeStructured") {
      val cacheKey = structuredCacheKey(schema, systemPrompt, prompt)
      LLMResponseCache.get(cacheKey) match {
        case Some(cached) =>
          Output.writeln(s"[Assistant] Using cached structured response")
          ResponseParser.parseToolArgsJsonObject(cached)
        case None =>
          val args = retryWithBackoff(maxRetries) {
            invokeStructuredInternal(prompt, schema, systemPrompt, modelIdOverride)
          }
          LLMResponseCache.put(cacheKey, ResponseParser.toolArgsToJson(args))
          args
      }
    }
  }

  /** Build a cache key that binds the cached response to the full schema
    * definition and system prompt, not just the schema's display name. Two
    * schemas that happened to share a name but differed in field set, or the
    * same schema with a different system prompt, would otherwise collide.
    */
  private def structuredCacheKey(
      schema: StructuredResponseSchema,
      systemPrompt: String,
      prompt: String
  ): String = {
    val md = java.security.MessageDigest.getInstance("SHA-256")
    md.update(schema.name.getBytes(java.nio.charset.StandardCharsets.UTF_8))
    md.update(0.toByte)
    md.update(schema.description.getBytes(java.nio.charset.StandardCharsets.UTF_8))
    md.update(0.toByte)
    md.update(schema.jsonSchema.getBytes(java.nio.charset.StandardCharsets.UTF_8))
    md.update(0.toByte)
    md.update(systemPrompt.getBytes(java.nio.charset.StandardCharsets.UTF_8))
    val hex = md.digest().take(8).map(b => f"${b & 0xff}%02x").mkString
    s"structured:${schema.name}:$hex:$prompt"
  }

  /**
   * Invoke with conversational context and structured output via forced tool_choice.
   * Appends the prompt to the current chat history. Returns parsed tool arguments.
   */
  def invokeInContextStructured(prompt: String, schema: StructuredResponseSchema): ToolArgs = {
    ErrorHandler.logOperation("invokeInContextStructured") {
      Option(org.gjt.sp.jedit.jEdit.getActiveView).foreach(setCurrentView)
      val history =
        ChatAction.getHistory
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

  /**
   * Invoke a single prompt with structured output, bypassing cache.
   * Extended version with model override.
   * Use for operations like summarization where caching is undesirable.
   */
  def invokeNoCacheStructured(
      prompt: String,
      schema: StructuredResponseSchema,
      systemPrompt: String,
      modelIdOverride: Option[String]
  ): ToolArgs = {
    ErrorHandler.logOperation("invokeNoCacheStructured") {
      retryWithBackoff(maxRetries) {
        invokeStructuredInternal(prompt, schema, systemPrompt, modelIdOverride)
      }
    }
  }

  /** Single-prompt structured invocation. */
  private def invokeStructuredInternal(
    prompt: String,
    schema: StructuredResponseSchema,
    systemPrompt: String,
    modelIdOverride: Option[String] = None
  ): ToolArgs = {
    val modelId = modelIdOverride.getOrElse(AssistantOptions.getModelId)
    requireAnthropicModel(modelId)
    val maxTokens = AssistantOptions.getMaxTokens

    val fullSystemPrompt = List(PromptLoader.getSystemPrompt, systemPrompt).filter(_.nonEmpty).mkString("\n\n")

    Output.writeln(s"[Assistant] invokeStructured - Model: $modelId, Schema: ${schema.name}")

    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      fullSystemPrompt, List(("user", prompt)), schema, maxTokens
    )

    val request = InvokeModelRequest.builder()
      .modelId(modelId)
      .body(SdkBytes.fromUtf8String(payload))
      .build()

    enforceRateLimit()
    val response = getClient.invokeModel(request)
    val responseJson = response.body().asUtf8String()

    ResponseParser.extractForcedToolArgs(responseJson).getOrElse(
      throw new RuntimeException("The model did not return a structured response. Try rephrasing your request or use a different model.")
    )
  }

  /** Chat-history structured invocation with truncation and merging. */
  private def invokeStructuredChatInternal(
    messages: List[ChatTurn],
    schema: StructuredResponseSchema
  ): ToolArgs = {
    val modelId = AssistantOptions.getModelId
    requireAnthropicModel(modelId)
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
      throw new RuntimeException("The model did not return a structured response. Try rephrasing your request or use a different model.")
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
        // Don't call recordFailure() here - already recorded in catch block of final attempt
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
            try Thread.sleep(delay)
            catch {
              case _: InterruptedException =>
                // Preserve the interrupt so cancellation polling downstream
                // still sees it — without this, a cancel during retry sleep
                // would be silently swallowed and the next attempt would
                // proceed regardless.
                Thread.currentThread().interrupt()
                throw new RuntimeException("Operation cancelled")
            }
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

  /** Merge consecutive same-role messages (Anthropic requires strict alternation).
    *
    * Implementation note: accumulates into a `ListBuffer`, collecting content
    * chunks per run and emitting one `ChatTurn` per role-change. The previous
    * `foldLeft` implementation rebuilt the accumulator on every matching
    * message (`acc.init :+ acc.last.copy(...)`), producing O(n^2) work on
    * long histories with many same-role runs.
    */
  private def mergeConsecutiveTurns(messages: List[ChatTurn]): List[ChatTurn] = {
    val out = scala.collection.mutable.ListBuffer.empty[ChatTurn]
    var currentRole: Option[BedrockRole] = None
    val currentContent = new StringBuilder
    for (msg <- messages) {
      if (currentRole.contains(msg.role)) {
        currentContent.append("\n\n").append(msg.content)
      } else {
        currentRole.foreach(r => out += ChatTurn(r, currentContent.toString))
        currentRole = Some(msg.role)
        currentContent.setLength(0)
        currentContent.append(msg.content)
      }
    }
    currentRole.foreach(r => out += ChatTurn(r, currentContent.toString))
    out.toList
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
      messages: List[ChatTurn],
      summarizationAttempted: Boolean = false
  ): String = {
    val modelId = AssistantOptions.getModelId
    requireAnthropicModel(modelId)

    val maxTokens = AssistantOptions.getMaxTokens

    val fullSystemPrompt = List(PromptLoader.getSystemPrompt, systemPrompt).filter(_.nonEmpty).mkString("\n\n")

    Output.writeln(s"[Assistant] invokeChat - Model: $modelId, Messages: ${messages.length}")

    // Pre-flight summarization check (only on first call, not after summarization retry)
    if (!summarizationAttempted && ContextSummarizer.shouldSummarize(ChatAction.getHistory, modelId)) {
      Output.writeln("[Assistant] Context budget threshold reached - triggering summarization")
      ContextSummarizer.performSummarization(modelId)
      // Re-snapshot messages after summarization replaced history
      val updatedHistory = ChatAction.getHistory
        .filterNot(_.transient)
        .flatMap(m => BedrockRole.fromWire(m.role.wireValue).map(ChatTurn(_, m.content)))
      return invokeChatInternal(systemPrompt, updatedHistory, summarizationAttempted = true)
    }

    val maxChars = AssistantConstants.MAX_CHAT_CONTEXT_CHARS
    // Anthropic doesn't count system prompt against message context budget
    val systemCost = 0
    val truncated = truncateTurns(messages, maxChars, systemCost)
    if (truncated.length < messages.length)
      Output.writeln(s"[Assistant] invokeChat - Truncated ${messages.length - truncated.length} old messages")

    val merged = mergeConsecutiveTurns(truncated)
    if (merged.isEmpty) {
      throw new RuntimeException(
        "Context budget exhausted — the conversation is too large. Clear chat history and try again."
      )
    }

    invokeChatWithTools(modelId, fullSystemPrompt, merged, maxTokens)
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
    maxTokens: Int
  ): String = {
    invokeChatWithToolsTestable(
      modelId, systemPrompt, initialMessages, maxTokens,
      request => getClient.invokeModel(request).body().asUtf8String(),
      (toolName, args) => {
        val view = Option(currentViewTL.get())
          .orElse(Option(org.gjt.sp.jedit.jEdit.getActiveView))
          .getOrElse(throw new RuntimeException("No view available for tool execution"))
        AssistantTools.executeToolWithPermission(toolName, args, view)
      }
    )
  }

  /**
   * Testable version of the agentic tool-use loop.
   * Accepts function parameters for API calls and tool execution, enabling mock-based testing.
   *
   * @param modelId The Bedrock model ID
   * @param systemPrompt System prompt for the conversation
   * @param initialMessages Initial message history
   * @param maxTokens Maximum tokens to generate
   * @param invoker Function that takes an InvokeModelRequest and returns the response JSON
   * @param toolExecutor Function that takes (toolName, args) and returns the result string
   * @return The final text response from the model
   */
  private[assistant] def invokeChatWithToolsTestable(
    modelId: String,
    systemPrompt: String,
    initialMessages: List[ChatTurn],
    maxTokens: Int,
    invoker: InvokeModelRequest => String,
    toolExecutor: (String, ResponseParser.ToolArgs) => String
  ): String = {
    val maxIter = AssistantOptions.getMaxToolIterations
    val msgBuf = scala.collection.mutable.ListBuffer[ChatTurn]()
    msgBuf ++= initialMessages

    var iteration = 0
    val textParts = scala.collection.mutable.ListBuffer[String]()
    var continue = true
    val recentCalls = scala.collection.mutable.Queue[String]()

    // Track running total of all message content sizes so we only invoke
    // pruning when it actually exceeds the budget, instead of rebuilding the
    // sum from scratch every iteration.
    var runningChars = msgBuf.foldLeft(0)(_ + _.content.length)

    while (continue) {
      iteration += 1
      if (AssistantDockable.isCancelled) throw new RuntimeException("Operation cancelled")
      if (runningChars > AssistantConstants.MAX_CHAT_CONTEXT_CHARS) {
        pruneToolLoopMessagesInPlace(msgBuf, AssistantConstants.MAX_CHAT_CONTEXT_CHARS)
        runningChars = msgBuf.foldLeft(0)(_ + _.content.length)
      }

      // Update active tool loop context size for context bar
      activeToolLoopContextChars.set(runningChars)

      val hitLimit = maxIter match {
        case Some(limit) => iteration > limit
        case None => false
      }
      if (hitLimit) {
        ErrorHandler.safeWarn(s"[Assistant] Hit max tool iteration limit ($iteration iterations)")
        msgBuf += ChatTurn(
          BedrockRole.User,
          "You have reached the maximum tool iteration limit. Please provide a summary of what you've learned and any conclusions you can make without additional tool calls."
        )
        
        val payload = PayloadBuilder.buildAnthropicToolPayload(
          systemPrompt,
          fromTurns(msgBuf.toList),
          maxTokens
        )
        val request = InvokeModelRequest.builder()
          .modelId(modelId)
          .body(SdkBytes.fromUtf8String(payload))
          .build()

        enforceRateLimit()
        try {
          val responseJson = invoker(request)
          val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(responseJson)
          val summaryText = blocks.collect { case ResponseParser.TextBlock(t) => t }
          if (summaryText.nonEmpty) textParts ++= summaryText
        } catch {
          case ex: Exception =>
            ErrorHandler.safeWarn(s"[Assistant] Final summary call failed: ${ex.getMessage}")
        }
        continue = false
      } else {
        val payload = PayloadBuilder.buildAnthropicToolPayload(
          systemPrompt,
          fromTurns(msgBuf.toList),
          maxTokens
        )
        val request = InvokeModelRequest.builder()
          .modelId(modelId)
          .body(SdkBytes.fromUtf8String(payload))
          .build()

        enforceRateLimit()
        val responseJson = invoker(request)
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
          val assistantTurn = ChatTurn(BedrockRole.Assistant, rawContentJson(blocks))
          msgBuf += assistantTurn
          runningChars += assistantTurn.content.length

          // Execute each tool and build tool_result message
          val iterStr = maxIter.map(_.toString).getOrElse("∞")
          val resultBlocks = toolUses.map { tu =>
            // Enhanced stuck-loop detection: track tool name + ALL input params
            // This ensures different arguments produce different signatures
            val paramStr = tu.input.toSeq.sortBy(_._1).map { case (k, v) =>
              s"$k=${truncateSafely(ResponseParser.toolValueToString(v), 50)}"
            }.mkString(",")
            val signature = s"${tu.name}($paramStr)"
            recentCalls.enqueue(signature)
            if (recentCalls.length > AssistantConstants.LOOP_DETECTION_WINDOW) {
              val _ = recentCalls.dequeue()
            }

            // Check for exact repetition (N+ identical consecutive calls)
            val repeatThreshold = AssistantConstants.LOOP_DETECTION_REPEAT_THRESHOLD
            if (recentCalls.length >= repeatThreshold
                && recentCalls.takeRight(repeatThreshold).distinct.size == 1) {
              ErrorHandler.safeWarn(s"[Assistant] Detected stuck loop: same tool call '${recentCalls.last}' repeated $repeatThreshold+ times")
              throw new RuntimeException(s"Stuck in loop: tool '${tu.name}' called repeatedly with identical arguments and no progress. Try a different approach.")
            }

            // Check for alternating pattern (A-B-A-B)
            if (recentCalls.length >= 4) {
              val last4 = recentCalls.takeRight(4).toList
              if (last4(0) == last4(2) && last4(1) == last4(3)) {
                ErrorHandler.safeWarn(s"[Assistant] Detected alternating loop: ${last4(0)} <-> ${last4(1)}")
                throw new RuntimeException(s"Stuck in alternating loop between two tool calls with no progress. Try a different approach.")
              }
            }
            
            ErrorHandler.safeLog(s"[Assistant] Tool use ($iteration/$iterStr): ${tu.name}")
            ErrorHandler.safeUi("BedrockClient.toolLoop.setStatus") {
              AssistantDockable.setStatus(s"[tool] ${tu.name} ($iteration/$iterStr)…")
            }

            // Skip tool call bubble for tools that inject their own widgets
            val skipToolCallBubble =
              tu.name.startsWith("task_list_") ||
                tu.name == ToolId.AskUser.wireName ||
                tu.name == ToolId.PlanApproach.wireName
            if (!skipToolCallBubble) {
              ErrorHandler.safeUi("BedrockClient.toolLoop.addToolMessage") {
                GUI_Thread.later {
                  ChatAction.addToolMessage(tu.name, tu.input)
                }
              }
            }

            // A throwing tool handler must not abort the whole agentic
            // session. Surface the error as a tool_result string so the
            // LLM can course-correct, while stuck-loop detection above
            // still throws to abort pathological runs.
            val result =
              try toolExecutor(tu.name, tu.input)
              catch {
                case NonFatal(ex) =>
                  ErrorHandler.safeWarn(
                    s"[Assistant] Tool '${tu.name}' threw: ${ex.getMessage}"
                  )
                  s"Error (tool=${tu.name}): ${Option(ex.getMessage).getOrElse(ex.getClass.getSimpleName)}"
              }

            // Skip tool result bubble for tools that inject their own widgets
            // (task_list_*, ask_user, and plan_approach already show rich UI widgets)
            val skipToolResultBubble =
              tu.name.startsWith("task_list_") ||
                tu.name == ToolId.AskUser.wireName ||
                tu.name == ToolId.PlanApproach.wireName
            if (!skipToolResultBubble) {
              ErrorHandler.safeUi("BedrockClient.toolLoop.toolResultBubble") {
                GUI_Thread.later {
                  val html = WidgetRenderer.toolResult(
                    tu.name,
                    result,
                    action => AssistantDockable.registerAction(action)
                  )
                  ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
                    java.time.LocalDateTime.now(), rawHtml = true, transient = true))
                  AssistantDockable.showConversation(ChatAction.getHistory)
                }
              }
            }
            (tu.id, result)
          }

          // Append user message with tool results
          val resultTurn = ChatTurn(BedrockRole.User, toolResultsJson(resultBlocks))
          msgBuf += resultTurn
          runningChars += resultTurn.content.length
        }
      }
    }

    try {
      val finalText = textParts.mkString("\n\n")
      if (finalText.isEmpty) {
        ErrorHandler.safeWarn("[Assistant] Tool-use loop completed without text response")
        "I processed the request using tools but could not generate a text summary. Please try again or rephrase your question."
      } else {
        ErrorHandler.safeLog(s"[Assistant] Tool loop completed in $iteration iterations, response: ${finalText.length} chars")
        finalText
      }
    } finally {
      // Clear tool loop context tracking when loop exits
      activeToolLoopContextChars.set(0)
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
    try {
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
    } finally g.close()
    sw.toString
  }

  /** Serialize tool results as a JSON array string for the user message. */
  private def toolResultsJson(results: List[(String, String)]): String = {
    val sw = new StringWriter()
    val g = jsonFactory.createGenerator(sw)
    try {
      g.writeStartArray()
      for ((id, content) <- results) {
        g.writeStartObject()
        g.writeStringField("type", "tool_result")
        g.writeStringField("tool_use_id", id)
        g.writeStringField("content", content)
        g.writeEndObject()
      }
      g.writeEndArray()
    } finally g.close()
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
    Output.writeln(s"[Assistant] Max tokens: $maxTokens")
    Output.writeln(s"[Assistant] Prompt length: ${totalLength} chars (system: ${systemPrompt.length}, user: ${prompt.length})")

    // Build payload with system prompt
    val payload = PayloadBuilder.buildChatPayload(systemPrompt, List(("user", prompt)), maxTokens)

    val request = InvokeModelRequest.builder()
      .modelId(modelId)
      .body(SdkBytes.fromUtf8String(payload))
      .build()

    enforceRateLimit()
    val response = getClient.invokeModel(request)
    val responseBody = response.body().asUtf8String()

    val parsed = ResponseParser.parseResponseEither(responseBody) match {
      case Right(text) => text
      case Left(err)   => throw new RuntimeException(err.message)
    }
    Output.writeln(s"[Assistant] Parsed response length: ${parsed.length} chars")
    parsed
  }

  /**
   * Orchestrate the adaptive tree-of-thought planning process.
   * Phase 1: Brainstorm a configurable number of distinct approaches
   * Phase 2: Elaborate each approach in parallel using exploration tools
   * Phase 3: Select the best approach and return a refined plan
   *
   * @param problem Detailed problem description
   * @param scope Scope hint (e.g., "proof", "refactor", "multi-file")
   * @param context Optional extra context provided by the caller
   * @param view Current jEdit view for context
   * @return The final detailed plan text, or an error / cancellation message
   */
  def invokePlanningAgent(
      problem: String,
      scope: String,
      context: String,
      view: View
  ): String = {
    ErrorHandler.logOperation("invokePlanningAgent") {
      val planningModelId = AssistantOptions.getPlanningModelId
      val usingCustomModel = AssistantOptions.getPlanningBaseModelId.nonEmpty
      val modelInfo =
        if (usingCustomModel) s" using planning model: $planningModelId"
        else s" using main model: $planningModelId"
      Output.writeln(s"[Assistant] Planning agent: starting adaptive tree-of-thought$modelInfo")
      Output.writeln(s"[Assistant] Problem: ${problem.take(80)}")

      // Show initial planning widget
      GUI_Thread.later {
        val html = WidgetRenderer.planningInProgress(problem, "brainstorm")
        ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
          java.time.LocalDateTime.now(), rawHtml = true, transient = true))
        AssistantDockable.showConversation(ChatAction.getHistory)
      }

      // Capture context snapshot from current state, then merge in the
      // caller's optional context. We keep them separate because the
      // buffer-derived snapshot is structured (current file, goal) while
      // the LLM-supplied context is free-form.
      val viewContext = captureContextSnapshot(view)
      val contextSnapshot =
        if (context.trim.isEmpty) viewContext
        else s"$viewContext\n\nCaller-provided context:\n${context.trim}"

      // Phase 1: Brainstorm approaches (single API call)
      Output.writeln("[Assistant] Planning Phase 1: Brainstorming approaches...")
      val approaches = brainstormApproaches(problem, contextSnapshot, scope)

      if (AssistantDockable.isCancelled) {
        "Error: planning cancelled by user."
      } else {
        // Update widget for elaborate phase
        val approachTitles = approaches.map(_.title)
        GUI_Thread.later {
          val html = WidgetRenderer.planningInProgress(problem, "elaborate", approachTitles)
          ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
            java.time.LocalDateTime.now(), rawHtml = true, transient = true))
          AssistantDockable.showConversation(ChatAction.getHistory)
        }

        // Phase 2: Elaborate each approach in parallel (agentic loops)
        Output.writeln(s"[Assistant] Planning Phase 2: Elaborating ${approaches.length} approaches in parallel...")
        val elaboratedPlans = elaborateApproachesInParallel(problem, approaches, context, view)

        if (AssistantDockable.isCancelled) {
          "Error: planning cancelled by user."
        } else {
          // Update widget for select phase
          GUI_Thread.later {
            val html = WidgetRenderer.planningInProgress(problem, "select", approachTitles)
            ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
              java.time.LocalDateTime.now(), rawHtml = true, transient = true))
            AssistantDockable.showConversation(ChatAction.getHistory)
          }

          // Phase 3: Select best plan (single API call)
          Output.writeln("[Assistant] Planning Phase 3: Selecting best approach...")
          val finalPlan = selectBestPlan(problem, approaches, elaboratedPlans)

          Output.writeln(s"[Assistant] Planning complete: selected approach ${finalPlan.selectedApproach}")

          // Show final planning result widget
          GUI_Thread.later {
            val html = WidgetRenderer.planningResult(
              problem,
              approaches.map(a => (a.id, a.title)),
              finalPlan.selectedApproach,
              finalPlan.reasoning,
              finalPlan.plan,
              action => AssistantDockable.registerAction(action)
            )
            ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
              java.time.LocalDateTime.now(), rawHtml = true, transient = true))
            AssistantDockable.showConversation(ChatAction.getHistory)
          }

          finalPlan.plan
        }
      }
    }
  }

  /** Capture a lightweight context snapshot from the current view state. */
  private def captureContextSnapshot(view: View): String = {
    try {
      val pathOpt = GUI_Thread.now {
        Option(view.getBuffer).flatMap(b => Option(b.getPath))
      }
      
      val contextParts = scala.collection.mutable.ListBuffer[String]()
      
      // Add current file path
      pathOpt.foreach(path => contextParts += s"Current file: $path")
      
      // Add goal state if available
      if (IQAvailable.isAvailable) {
        val selectionArgs = pathOpt.map(path => {
          val offset = GUI_Thread.now {
            Option(view.getTextArea).map(_.getCaretPosition).getOrElse(0)
          }
          Map(
            "command_selection" -> "file_offset",
            "path" -> path,
            "offset" -> offset
          )
        }).getOrElse(Map("command_selection" -> "current"))
        
        // Short timeout: this is speculative context gathered before the
        // first planning API call. A slow I/Q backplane shouldn't delay the
        // brainstorm visible to the user — the planning sub-agents will do
        // their own focused context fetches when they actually need them.
        IQMcpClient.callGetContextInfo(selectionArgs, 1000L).toOption.foreach { ctx =>
          if (ctx.goal.hasGoal && ctx.goal.goalText.trim.nonEmpty) {
            contextParts += s"\nCurrent goal state:\n${ctx.goal.goalText.trim}"
          }
        }
      }
      
      if (contextParts.nonEmpty) contextParts.mkString("\n\n")
      else "No additional context available."
    } catch {
      // Use NonFatal so OutOfMemoryError / VirtualMachineError / thread
      // interrupts propagate to the caller instead of being suppressed.
      case NonFatal(ex) =>
        Output.warning(s"[Assistant] Context capture failed: ${ex.getMessage}")
        "Context capture failed."
    }
  }

  /** Phase 1: Brainstorm distinct approaches using structured output.
    *
    * Returns [[AssistantConstants.PLANNING_NUM_APPROACHES]] approaches on
    * success. On malformed or short output, throws a RuntimeException —
    * the pipeline must not silently degrade to a single-approach run,
    * because the downstream widgets, prompts, and select phase all assume
    * diversity.
    */
  private def brainstormApproaches(
    problem: String,
    contextSnapshot: String,
    scope: String
  ): List[Approach] = {
    val numApproaches = AssistantConstants.PLANNING_NUM_APPROACHES
    val scopeHint = if (scope.nonEmpty) s"\n\nScope: $scope" else ""
    val prompt = s"""$problem$scopeHint

$contextSnapshot

Generate exactly $numApproaches distinct approaches to solve this problem. Each approach should use a different strategy or technique. Focus on diversity - the approaches should explore different angles rather than minor variations of the same idea. Each approach must have a unique positive integer `id`."""

    val planningModelId = AssistantOptions.getPlanningModelId

    // Bypass the structured-output cache: brainstorm is creative work and
    // cache hits would re-serve the same approaches for identical prompts
    // (very likely when users retry the same question), defeating the
    // point of the phase.
    val args = BedrockClient.invokeNoCacheStructured(
      prompt,
      StructuredResponseSchema.PlanningBrainstorm,
      systemPrompt = PromptLoader.load("planning_brainstorm_system.md", Map.empty),
      modelIdOverride = Some(planningModelId)
    )

    val approaches = parseApproaches(args)
    if (approaches.length < numApproaches) {
      throw new RuntimeException(
        s"Planning brainstorm returned ${approaches.length} valid approaches (needed $numApproaches). " +
          "The model may have produced malformed output; try rephrasing the request or using a different planning model."
      )
    }
    approaches
  }

  /** Parse approaches from structured response arguments. */
  private case class Approach(
    id: Int,
    title: String,
    summary: String,
    keyIdea: String,
    explorationHints: List[String]
  )

  /** Parse approaches from the brainstorm phase's structured response.
    *
    * Drops entries with missing / blank required fields (`id`, `title`,
    * `summary`, `keyIdea`) rather than emitting sentinel `Approach(0, ...)`
    * rows that would flow through elaboration and pollute the UI. The
    * caller (brainstormApproaches) is responsible for deciding what to do
    * when too few valid entries come back. */
  private def parseApproaches(args: ResponseParser.ToolArgs): List[Approach] = {
    args.get("approaches") match {
      case Some(ResponseParser.JsonValue(json)) =>
        val parser = jsonFactory.createParser(json)
        val approaches = scala.collection.mutable.ListBuffer[Approach]()
        val seenIds = scala.collection.mutable.Set.empty[Int]

        try {
          if (parser.nextToken() == JsonToken.START_ARRAY) {
            while (parser.nextToken() != JsonToken.END_ARRAY) {
              if (parser.currentToken() == JsonToken.START_OBJECT) {
                var id = 0
                var title = ""
                var summary = ""
                var keyIdea = ""
                val hints = scala.collection.mutable.ListBuffer[String]()

                while (parser.nextToken() != JsonToken.END_OBJECT) {
                  val fieldName = parser.currentName()
                  parser.nextToken()
                  fieldName match {
                    case "id" => id = parser.getIntValue
                    case "title" => title = parser.getText
                    case "summary" => summary = parser.getText
                    case "key_idea" => keyIdea = parser.getText
                    case "exploration_hints" =>
                      if (parser.currentToken() == JsonToken.START_ARRAY) {
                        while (parser.nextToken() != JsonToken.END_ARRAY) {
                          hints += parser.getText
                        }
                      }
                    case _ => val _ = parser.skipChildren()
                  }
                }

                val isValid =
                  id > 0 && !seenIds.contains(id) &&
                  title.trim.nonEmpty && summary.trim.nonEmpty && keyIdea.trim.nonEmpty
                if (isValid) {
                  seenIds += id
                  approaches += Approach(id, title.trim, summary.trim, keyIdea.trim, hints.toList)
                } else {
                  Output.warning(
                    s"[Assistant] Planning: dropping malformed brainstorm entry (id=$id, title=${title.take(40)})"
                  )
                }
              }
            }
          }
        } finally {
          parser.close()
        }

        approaches.toList
      case _ => List.empty
    }
  }

  /** Phase 2: Elaborate each approach in parallel using sub-agent exploration. */
  private case class ElaboratedPlan(approachId: Int, title: String, planText: String)

  private def elaborateApproachesInParallel(
    problem: String,
    approaches: List[Approach],
    context: String,
    view: View
  ): List[ElaboratedPlan] = {
    if (approaches.isEmpty) return Nil

    val latch = new CountDownLatch(approaches.length)
    val results = new java.util.concurrent.ConcurrentHashMap[Int, ElaboratedPlan]()

    // Stagger sub-agent starts so we don't trip Bedrock's concurrency
    // throttle by firing all three initial requests at the same instant.
    // We schedule each fork via TimeoutGuard.scheduleAction so the calling
    // thread isn't blocked on Thread.sleep; fires after (idx * stagger) ms.
    val staggerMs = 200L
    val cancels = scala.collection.mutable.ListBuffer.empty[() => Unit]

    approaches.zipWithIndex.foreach { case (approach, idx) =>
      val cancel = TimeoutGuard.scheduleAction(idx * staggerMs) {
        if (AssistantDockable.isCancelled) {
          val _ = results.put(approach.id, ElaboratedPlan(
            approach.id, approach.title, "Error: planning cancelled by user."
          ))
          latch.countDown()
        } else {
          val _ = planningExecutor.submit(new Runnable {
            def run(): Unit = {
              try {
                if (!AssistantDockable.isCancelled) {
                  val prompt = buildElaborationPrompt(problem, approach, context)
                  val plan = runPlanningSubAgent(prompt, view)
                  val _ = results.put(approach.id, ElaboratedPlan(approach.id, approach.title, plan))
                } else {
                  val _ = results.put(approach.id, ElaboratedPlan(
                    approach.id, approach.title, "Error: planning cancelled by user."
                  ))
                }
              } catch {
                case NonFatal(ex) =>
                  Output.warning(s"[Assistant] Planning sub-agent ${approach.id} failed: ${ex.getMessage}")
                  val _ = results.put(approach.id, ElaboratedPlan(
                    approach.id,
                    approach.title,
                    s"Error: elaboration failed: ${ex.getMessage}"
                  ))
              } finally {
                latch.countDown()
              }
            }
          })
        }
      }
      cancels += cancel
    }

    // Wait for all sub-agents to complete (with capped timeout). Capping
    // before the arithmetic prevents overflow when a pathological
    // getMaxToolIterations is configured. We also bound below by the
    // global PLANNING_TOTAL_TIMEOUT_MS so a single stuck call can't
    // monopolise the tool loop indefinitely.
    val iters = math.max(1, math.min(AssistantOptions.getMaxToolIterations.getOrElse(15), 10_000))
    val derivedTimeout = (iters.toLong * 30L + 60L) * 1000L
    val totalTimeout = math.min(derivedTimeout, AssistantConstants.PLANNING_TOTAL_TIMEOUT_MS)

    val allCompleted =
      try latch.await(totalTimeout, TimeUnit.MILLISECONDS)
      catch {
        case _: InterruptedException =>
          Thread.currentThread().interrupt()
          false
      }

    if (!allCompleted) {
      Output.warning(
        s"[Assistant] Planning elaboration timed out after ${totalTimeout}ms; returning partial results"
      )
      // Cancel any scheduled forks that haven't started yet — forks that
      // have already begun are left to complete on their own because the
      // Bedrock SDK call is the expensive part and is not itself cancellable.
      cancels.foreach(_.apply())
    }

    // Return results in original order (by approach position, not ID).
    approaches.map(a =>
      results.getOrDefault(a.id, ElaboratedPlan(
        a.id,
        a.title,
        "Error: elaboration did not complete in time."
      ))
    )
  }

  /** Build the prompt for a sub-agent to elaborate an approach. */
  private def buildElaborationPrompt(
      problem: String,
      approach: Approach,
      context: String
  ): String = {
    val hintsSection =
      if (approach.explorationHints.nonEmpty)
        s"\n\nExploration hints:\n${approach.explorationHints.map(h => s"- $h").mkString("\n")}"
      else ""

    val contextSection =
      if (context.trim.isEmpty) ""
      else s"\n\nAdditional context from the caller:\n${context.trim}"

    s"""Problem: $problem

Assigned Approach: ${approach.title}

Summary: ${approach.summary}

Key Idea: ${approach.keyIdea}$hintsSection$contextSection

Your task is to elaborate this approach into a detailed, actionable plan. Use the available exploration tools to:
1. Verify that referenced entities (theorems, definitions, etc.) actually exist
2. Check the current goal state and proof context
3. Search for relevant lemmas and theorems
4. Identify potential challenges or edge cases

Produce a structured plan with:
- Step-by-step implementation instructions
- Specific theorem/lemma names to use (verified via tools)
- Anticipated challenges and how to address them
- Acceptance criteria for completion"""
  }

  /** Run a planning sub-agent with read-only tools. */
  private def runPlanningSubAgent(prompt: String, view: View): String = {
    val modelId = AssistantOptions.getPlanningModelId
    requireAnthropicModel(modelId)
    val maxTokens = AssistantOptions.getMaxTokens
    val planningSystemPrompt = PromptLoader.load("planning_agent_system.md", Map.empty)
    val messages = List(ChatTurn(BedrockRole.User, prompt))

    // Custom agentic loop with planning-specific payload builder
    runPlanningSubAgentLoop(
      modelId,
      planningSystemPrompt,
      messages,
      maxTokens,
      view
    )
  }

  /** Planning sub-agent agentic loop with restricted tool set. */
  private def runPlanningSubAgentLoop(
    modelId: String,
    systemPrompt: String,
    initialMessages: List[ChatTurn],
    maxTokens: Int,
    view: View
  ): String = {
    // Planning sub-agents get a reduced iteration limit. If the user has
    // configured a tighter main-loop limit than the planning default, honour
    // that as well — the user's ceiling should always be the tighter one.
    val defaultSubLimit = AssistantConstants.PLANNING_SUB_AGENT_MAX_ITERATIONS
    val mainIter = AssistantOptions.getMaxToolIterations
    val maxIter = mainIter match {
      case Some(n) => math.max(1, math.min(n, defaultSubLimit))
      case None => defaultSubLimit
    }
    val msgBuf = scala.collection.mutable.ListBuffer[ChatTurn]()
    msgBuf ++= initialMessages

    var iteration = 0
    val textParts = scala.collection.mutable.ListBuffer[String]()
    var continue = true
    val recentCalls = scala.collection.mutable.Queue[String]()
    var runningChars = msgBuf.foldLeft(0)(_ + _.content.length)

    try {
    while (continue) {
      iteration += 1
      if (AssistantDockable.isCancelled) throw new RuntimeException("Operation cancelled")

      // Prune messages only when we actually exceed the budget.
      if (runningChars > AssistantConstants.MAX_CHAT_CONTEXT_CHARS) {
        pruneToolLoopMessagesInPlace(msgBuf, AssistantConstants.MAX_CHAT_CONTEXT_CHARS)
        runningChars = msgBuf.foldLeft(0)(_ + _.content.length)
      }

      // Expose the sub-agent's current context size so the UI's context
      // bar stays accurate during the parallel elaboration phase. We take
      // the max across concurrent sub-agents so the bar never under-reports
      // while any sub-agent is still working — do it atomically so two
      // sub-agents racing to publish their runningChars can't lose the
      // higher value.
      val _ = activeToolLoopContextChars.updateAndGet(prev => math.max(prev, runningChars))

      if (iteration > maxIter) {
        msgBuf += ChatTurn(
          BedrockRole.User,
          "You have reached the iteration limit for planning. Please provide a summary of your findings and a structured plan based on what you've explored."
        )
        
        val payload = PayloadBuilder.buildPlanningAgentToolPayload(
          systemPrompt,
          fromTurns(msgBuf.toList),
          maxTokens
        )
        val request = InvokeModelRequest.builder()
          .modelId(modelId)
          .body(SdkBytes.fromUtf8String(payload))
          .build()

        enforceRateLimit()
        try {
          val responseJson = getClient.invokeModel(request).body().asUtf8String()
          val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(responseJson)
          val summaryText = blocks.collect { case ResponseParser.TextBlock(t) => t }
          if (summaryText.nonEmpty) textParts ++= summaryText
        } catch {
          // Preserve the no-throw contract (we still want to return whatever
          // the sub-agent accumulated), but don't lose the diagnostic: a
          // silent catch made it impossible to tell whether the summary
          // actually returned content or was suppressed by an exception.
          case NonFatal(e) =>
            ErrorHandler.safeWarn(
              s"[Assistant] Planning sub-agent final summary failed: ${e.getMessage}"
            )
        }
        continue = false
      } else {
        val payload = PayloadBuilder.buildPlanningAgentToolPayload(
          systemPrompt,
          fromTurns(msgBuf.toList),
          maxTokens
        )
        val request = InvokeModelRequest.builder()
          .modelId(modelId)
          .body(SdkBytes.fromUtf8String(payload))
          .build()

        enforceRateLimit()
        val responseJson = getClient.invokeModel(request).body().asUtf8String()
        val (blocks, _) = ResponseParser.parseAnthropicContentBlocks(responseJson)

        val currentTextParts = blocks.collect { case ResponseParser.TextBlock(t) => t }
        val toolUses = blocks.collect { case t: ResponseParser.ToolUseBlock => t }

        if (currentTextParts.nonEmpty) textParts ++= currentTextParts

        if (toolUses.isEmpty) {
          continue = false
        } else {
          val assistantTurn = ChatTurn(BedrockRole.Assistant, rawContentJson(blocks))
          msgBuf += assistantTurn
          runningChars += assistantTurn.content.length

          val resultBlocks = toolUses.map { tu =>
            // Stuck-loop detection for planning sub-agent
            val paramStr = tu.input.toSeq.sortBy(_._1).map { case (k, v) =>
              s"$k=${ResponseParser.toolValueToString(v).take(50)}"
            }.mkString(",")
            val signature = s"${tu.name}($paramStr)"
            recentCalls.enqueue(signature)
            if (recentCalls.length > AssistantConstants.LOOP_DETECTION_WINDOW) {
              val _ = recentCalls.dequeue()
            }

            // Check for exact repetition (N+ identical consecutive calls)
            val repeatThreshold = AssistantConstants.LOOP_DETECTION_REPEAT_THRESHOLD
            if (recentCalls.length >= repeatThreshold
                && recentCalls.takeRight(repeatThreshold).distinct.size == 1) {
              Output.warning(s"[Assistant] Planning sub-agent stuck loop detected: '${recentCalls.last}'")
              throw new RuntimeException(s"Planning sub-agent stuck: tool '${tu.name}' called repeatedly with no progress.")
            }

            // Check for alternating pattern (A-B-A-B)
            if (recentCalls.length >= 4) {
              val last4 = recentCalls.takeRight(4).toList
              if (last4(0) == last4(2) && last4(1) == last4(3)) {
                Output.warning(s"[Assistant] Planning sub-agent alternating loop detected")
                throw new RuntimeException(s"Planning sub-agent stuck in alternating loop between '${last4(0)}' and '${last4(1)}'.")
              }
            }
            
            // Execute tool with planning-only filter AND ToolPermissions
            // enforcement. Even "read-only" tools in planningToolIds can be
            // configured as AskAtFirstUse (e.g. FindTheorems, GetDefinitions
            // — see ToolPermissions.defaultPermissions): the sub-agent must
            // respect the user's policy the same way the main agent does.
            val result = ToolId.fromWire(tu.name) match {
              case Some(id) if ToolId.planningToolIds.contains(id) =>
                AssistantTools.executeToolWithPermission(tu.name, tu.input, view)
              case _ =>
                s"Tool '${tu.name}' is not available to the planning agent. Use only read-only exploration tools."
            }
            (tu.id, result)
          }

          val resultTurn = ChatTurn(BedrockRole.User, toolResultsJson(resultBlocks))
          msgBuf += resultTurn
          runningChars += resultTurn.content.length
        }
      }
    }

    val finalText = textParts.mkString("\n\n")
    if (finalText.isEmpty) {
      "Planning exploration completed but no plan was generated."
    } else {
      finalText
    }
    } finally {
      // Don't zero the high-water mark here: three sub-agents run in
      // parallel under one planning call, so one finishing must not make
      // the UI under-report the remaining sub-agents. The outer chat
      // tool-loop re-publishes on its next iteration and will correct any
      // lingering value once planning as a whole returns.
      ()
    }
  }

  /** Phase 3: Select the best plan using structured output. */
  private case class SelectedPlan(selectedApproach: Int, reasoning: String, plan: String)

  private def selectBestPlan(
      problem: String,
      approaches: List[Approach],
      plans: List[ElaboratedPlan]
  ): SelectedPlan = {
    val plansSection = plans.map { p =>
      s"""Approach ${p.approachId}: ${p.title}
${p.planText}

---"""
    }.mkString("\n\n")

    val prompt = s"""Problem: $problem

The following approaches have been elaborated:

$plansSection

Review all approaches and select the best one. Consider:
- Completeness and detail of the plan
- Feasibility of the proposed steps
- Use of verified theorems/lemmas (not guesses)
- Clarity of acceptance criteria

Select the best approach and produce a final refined plan."""

    val planningModelId = AssistantOptions.getPlanningModelId

    // Planning responses should not be cached: Phase 1 and Phase 3 both run
    // non-deterministic creative work, and cache hits would re-serve the
    // same three approaches (or the same "best" selection) on identical
    // inputs, defeating diversity.
    val args = BedrockClient.invokeNoCacheStructured(
      prompt,
      StructuredResponseSchema.PlanningSelect,
      systemPrompt = PromptLoader.load("planning_select_system.md", Map.empty),
      modelIdOverride = Some(planningModelId)
    )

    val rawSelection = args.get("selected_approach").collect {
      case ResponseParser.IntValue(n) => n
    }
    val validIds = approaches.map(_.id).toSet
    val fallbackId = approaches.headOption.map(_.id).getOrElse(1)
    val selected = rawSelection match {
      case Some(n) if validIds.contains(n) => n
      case Some(n) =>
        Output.warning(
          s"[Assistant] Planning: model selected approach $n which is not in ${validIds.mkString("{", ", ", "}")}; falling back to $fallbackId"
        )
        fallbackId
      case None =>
        Output.warning("[Assistant] Planning: model did not return selected_approach; falling back")
        fallbackId
    }

    SelectedPlan(
      selectedApproach = selected,
      reasoning = args.get("reasoning").collect {
        case ResponseParser.StringValue(s) => s
      }.getOrElse("No reasoning provided."),
      plan = args.get("plan").collect {
        case ResponseParser.StringValue(s) => s
      }.getOrElse("No plan provided.")
    )
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
    currentViewTL.remove()
    try planningExecutor.shutdown()
    catch { case NonFatal(_) => () }
  }
}
