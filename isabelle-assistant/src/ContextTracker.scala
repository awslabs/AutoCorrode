/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/**
 * Tracks context window usage for LLM conversations.
 * 
 * Provides token estimation and usage metrics to help users understand how much
 * of the model's context window is consumed. Uses a heuristic approach since
 * exact tokenization requires model-specific tokenizers.
 */
object ContextTracker {

  /**
   * Context usage metrics calculated from conversation history.
   * 
   * @param usedTokens Estimated tokens used by messages in current context
   * @param maxTokens Model's maximum context window size in tokens
   * @param budgetTokens Our internal budget converted to estimated tokens
   * @param messageCount Total messages in history (including transient)
   * @param truncatedCount Messages that were/would be dropped due to budget limit
   * @param systemPromptTokens Estimated tokens in the system prompt
   */
  case class ContextUsage(
    usedTokens: Int,
    maxTokens: Int,
    budgetTokens: Int,
    messageCount: Int,
    truncatedCount: Int,
    systemPromptTokens: Int
  ) {
    /** Usage as a percentage of the budget (0.0 to 1.0+) */
    def budgetPercentage: Double = 
      if (budgetTokens <= 0) 0.0 
      else math.min(1.0, usedTokens.toDouble / budgetTokens.toDouble)
    
    /** Usage as a percentage of the model's total context window (0.0 to 1.0+) */
    def modelPercentage: Double = 
      if (maxTokens <= 0) 0.0
      else math.min(1.0, usedTokens.toDouble / maxTokens.toDouble)
    
    /** The limiting factor percentage (uses budget percentage since that's what causes truncation) */
    def percentage: Double = budgetPercentage
    
    /** Format as "~14K/200K tokens (7%)" */
    def formatSummary: String = {
      val pct = (percentage * 100).toInt
      s"~${ContextTracker.formatThousands(usedTokens)}/${ContextTracker.formatThousands(maxTokens)} tokens ($pct%)"
    }
    
    /** Format as "68%" */
    def formatPercentage: String = s"${(percentage * 100).toInt}%"
    
    /** Format detailed tooltip with breakdown */
    def formatTooltip: String = {
      val pct = (percentage * 100).toInt
      val lines = scala.collection.mutable.ListBuffer[String]()
      lines += s"Context: ~${ContextTracker.formatThousands(usedTokens)} / ${ContextTracker.formatThousands(maxTokens)} tokens ($pct%)"
      lines += s"Budget: ~${ContextTracker.formatThousands(budgetTokens)} tokens (internal limit)"
      lines += s"Messages: $messageCount total"
      if (truncatedCount > 0) {
        lines += s"Truncated: $truncatedCount older messages dropped"
      }
      if (systemPromptTokens > 0) {
        lines += s"System prompt: ~${ContextTracker.formatThousands(systemPromptTokens)} tokens"
      }
      lines.mkString("\n")
    }
  }

  /**
   * Anthropic Claude model context windows (input tokens).
   * Most recent Claude models support 200K tokens; older models may vary.
   * Default to 200K for unknown models (conservative estimate).
   */
  private val modelContextWindows: Map[String, Int] = Map(
    // Claude 3.5 family
    "anthropic.claude-3-5-sonnet-20241022-v2:0" -> 200000,
    "anthropic.claude-3-5-sonnet-20240620-v1:0" -> 200000,
    "anthropic.claude-3-5-haiku-20241022-v1:0" -> 200000,
    
    // Claude 3 family
    "anthropic.claude-3-opus-20240229-v1:0" -> 200000,
    "anthropic.claude-3-sonnet-20240229-v1:0" -> 200000,
    "anthropic.claude-3-haiku-20240307-v1:0" -> 200000,
    
    // Claude 3.7 family (hypothetical future models)
    "anthropic.claude-3-7-sonnet-20250219-v1:0" -> 200000,
    
    // Claude 4 family (future)
    "anthropic.claude-4-opus" -> 200000,
    "anthropic.claude-4-sonnet" -> 200000,
    
    // CRIS-prefixed variants (us./eu./ap./global.)
    "us.anthropic.claude-3-5-sonnet-20241022-v2:0" -> 200000,
    "us.anthropic.claude-3-5-sonnet-20240620-v1:0" -> 200000,
    "us.anthropic.claude-3-5-haiku-20241022-v1:0" -> 200000,
    "eu.anthropic.claude-3-5-sonnet-20241022-v2:0" -> 200000,
    "eu.anthropic.claude-3-5-sonnet-20240620-v1:0" -> 200000,
    "ap.anthropic.claude-3-5-sonnet-20241022-v2:0" -> 200000
  )

  /** Default context window for unknown models (conservative 200K) */
  private val defaultContextWindow = 200000

  /**
   * Get the context window size for a given model ID.
   * Handles CRIS prefixes and pattern matching for model families.
   * 
   * @param modelId Full model ID (may include CRIS prefix like us./eu./ap.)
   * @return Context window size in tokens
   */
  def modelContextWindow(modelId: String): Int = {
    if (modelId.isEmpty) return defaultContextWindow
    
    // Direct lookup first
    modelContextWindows.get(modelId) match {
      case Some(window) => window
      case None =>
        // Strip CRIS prefix and try again
        val stripped = if (modelId.matches("^(us|eu|ap|global)\\..*"))
          modelId.dropWhile(_ != '.').drop(1)
        else modelId
        
        modelContextWindows.get(stripped).getOrElse {
          // Pattern match on model family
          if (stripped.contains("claude-3-5") || stripped.contains("claude-3-7") || 
              stripped.contains("claude-3") || stripped.contains("claude-4")) {
            200000 // All Claude 3+ models support 200K
          } else {
            defaultContextWindow
          }
        }
    }
  }

  /**
   * Estimate token count from text using character-based heuristic.
   *
   * Uses ~3.5 chars/token ratio based on empirical data for Anthropic Claude.
   * This is a rough estimate but sufficient for UI progress indication.
   *
   * @param text Text to estimate tokens for
   * @return Estimated token count
   */
  def estimateTokens(text: String): Int = estimateTokensFromChars(text.length)

  /** Int-keyed overload: use this when only a character count is known, so
    * callers don't have to allocate a scratch string (the tool-loop
    * context-bar refresh used to materialise a 200 KB string just to
    * divide its length by 3.5). */
  def estimateTokensFromChars(chars: Int): Int = {
    // 3.5 chars per token is a reasonable estimate for Claude
    math.ceil(chars / 3.5).toInt
  }

  /**
   * Format number as thousands (e.g., 14200 → "14K", 500 → "500")
   * 
   * @param n Number to format
   * @return Formatted string
   */
  def formatThousands(n: Int): String = {
    if (n >= 1000) s"${n / 1000}K"
    else n.toString
  }

  /**
   * Check if conversation should trigger automatic summarization.
   * Convenience wrapper around calculate() for pre-flight checks.
   * 
   * @param history Current conversation history
   * @param modelId Model ID to use for context window calculation
   * @return True if summarization should be triggered
   */
  def shouldSummarize(history: List[ChatAction.Message], modelId: String): Boolean = {
    if (!AssistantOptions.getAutoSummarize) return false
    
    val nonTransient = history.filterNot(_.transient)
    if (nonTransient.length < AssistantConstants.MIN_MESSAGES_FOR_SUMMARIZATION) return false
    
    val usage = calculate(history, modelId)
    usage.budgetPercentage >= AssistantOptions.getSummarizationThreshold
  }

  /**
   * Calculate context usage from conversation history.
   * 
   * Analyzes the current conversation state and compares against both the
   * internal character budget and the model's actual context window.
   * 
   * @param history Current conversation history (all messages)
   * @param modelId Current model ID
   * @return ContextUsage metrics for display
   */
  def calculate(history: List[ChatAction.Message], modelId: String): ContextUsage = {
    // Filter to non-transient messages (same as what goes to API)
    val apiMessages = history.filterNot(_.transient)
    
    // Estimate tokens for each message and sum
    val messageTokens = apiMessages.map(m => estimateTokens(m.content)).sum
    
    // System prompt tokens
    val systemPrompt = try {
      PromptLoader.getSystemPrompt
    } catch {
      case _: Exception => ""
    }
    val systemTokens = estimateTokens(systemPrompt)
    
    // Add active tool loop context (ephemeral msgBuf during agentic tool execution)
    val toolLoopChars = BedrockClient.getActiveToolLoopContextChars
    val toolLoopTokens = if (toolLoopChars > 0) estimateTokensFromChars(toolLoopChars) else 0
    
    // Total tokens used (includes both persisted history and active tool loop)
    val usedTokens = messageTokens + systemTokens + toolLoopTokens
    
    // Model's max context window
    val maxTokens = modelContextWindow(modelId)
    
    // User-configurable context budget from max_context_tokens setting
    val budgetTokens = AssistantOptions.getMaxContextTokens
    val budgetChars = (budgetTokens * 3.5).toInt // Convert tokens back to chars for comparison
    
    // Truncation calculation: simulate what truncateTurns does
    val totalChars = apiMessages.map(_.content.length).sum
    val truncated = if (totalChars <= budgetChars) {
      0
    } else {
      // Count how many messages would be dropped from the front
      var accumulated = 0
      var kept = 0
      apiMessages.reverse.foreach { msg =>
        if (accumulated + msg.content.length <= budgetChars) {
          accumulated += msg.content.length
          kept += 1
        }
      }
      apiMessages.length - kept
    }
    
    ContextUsage(
      usedTokens = usedTokens,
      maxTokens = maxTokens,
      budgetTokens = budgetTokens,
      messageCount = history.length,
      truncatedCount = truncated,
      systemPromptTokens = systemTokens
    )
  }
}