/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import java.time.Duration

/**
 * Context summarization orchestrator.
 * 
 * When conversation history approaches context budget limits, this module:
 * 1. Checks if summarization should trigger
 * 2. Calls a dedicated LLM to compress history into structured summary
 * 3. Replaces the conversation with the summary as the seed message
 * 
 * The summarization uses a separate model (configurable) and has no tool access.
 * It produces a structured output that preserves: original task, accomplishments,
 * pending work, key context (names/files), approach history, decisions, and current state.
 */
object ContextSummarizer {

  /**
   * Summarization result with structured fields.
   */
  case class SummarizationResult(
    userGoal: String,
    accomplishments: String,
    pendingWork: String,
    keyContext: String,
    approachHistory: String,
    decisionsAndConstraints: String,
    currentState: String
  )

  /**
   * Check if summarization should trigger based on current context usage.
   * Delegates to [[ContextTracker.shouldSummarize]] so the policy lives in
   * a single place.
   *
   * @param history Current conversation history
   * @param modelId Model ID to calculate context for
   * @return True if summarization should happen
   */
  def shouldSummarize(history: List[ChatAction.Message], modelId: String): Boolean =
    ContextTracker.shouldSummarize(history, modelId)

  /**
   * Perform complete summarization flow: call LLM, format result, replace history.
   * This is the main entry point called by BedrockClient.
   * 
   * @param modelId Model ID for the main conversation (used for context calculation)
   */
  def performSummarization(modelId: String): Unit = {
    ErrorHandler.logOperation("performSummarization") {
      val history = ChatAction.getHistory
      Output.writeln(s"[Assistant] Context summarization triggered - ${history.length} messages")

      try {
        // Call summarization agent
        val summary = summarizeConversation(history)

        // Format as restoration message
        val restorationMsg = buildRestorationMessage(summary)

        // Atomically replace history
        ChatAction.replaceHistoryWithSummary(restorationMsg)

        // Show notification to user
        ChatAction.addSummarizationNotice()

        val newHistory = ChatAction.getHistory
        Output.writeln(s"[Assistant] Context summarized - reduced from ${history.length} to ${newHistory.length} messages")

      } catch {
        case ex: Exception =>
          // Deliberate swallow: the caller (BedrockClient.invokeChatInternal)
          // recurses with summarizationAttempted=true regardless, and that
          // path then applies truncateTurns as a fallback. Rethrowing would
          // abort the user's chat turn on a failure in a recovery path.
          // Log loudly enough that the failure is visible in the Isabelle
          // messages panel.
          Output.warning(s"[Assistant] Context summarization failed: ${ex.getMessage}")
          Output.warning("[Assistant] Falling back to truncation in invokeChatInternal")
      }
    }
  }

  /**
   * Call the summarization LLM with structured schema.
   * Formats conversation into three sections with recency gradient.
   * 
   * @param history Full conversation history
   * @return Structured summary
   */
  private def summarizeConversation(history: List[ChatAction.Message]): SummarizationResult = {
    val nonTransient = history.filterNot(_.transient)
    val total = nonTransient.length
    
    // Calculate section boundaries (40% / 40% / 20% split)
    val section1End = (total * 0.4).toInt
    val section2Start = section1End + 1
    val section2End = (total * 0.8).toInt
    val section3Start = section2End + 1
    
    val section1 = nonTransient.take(section1End)
    val section2 = nonTransient.slice(section1End, section2End)
    val section3 = nonTransient.drop(section2End)
    
    // Calculate conversation duration (rough estimate)
    val duration = if (nonTransient.nonEmpty && nonTransient.length >= 2) {
      val start = nonTransient.head.timestamp
      val end = nonTransient.last.timestamp
      Duration.between(start, end)
    } else Duration.ZERO
    
    val durationStr = if (duration.toMinutes > 60) {
      s"${duration.toHours} hours"
    } else if (duration.toMinutes > 0) {
      s"${duration.toMinutes} minutes"
    } else {
      "less than a minute"
    }
    
    // Get current task list state
    val tasks = TaskList.getTasks
    val taskListFormatted = if (tasks.isEmpty) {
      "No active task list."
    } else {
      val taskLines = tasks.map { task =>
        val status = task.status match {
          case TaskList.Done => "✓"
          case TaskList.Todo => "○"
          case TaskList.Irrelevant => "✗"
        }
        s"$status #${task.id}. ${task.title} (${task.status.displayName})"
      }
      taskLines.mkString("\n")
    }
    
    // Format sections
    def formatMessages(msgs: List[ChatAction.Message]): String = {
      msgs.map { m =>
        val role = m.role.wireValue
        val content = m.content.trim
        s"[$role] $content"
      }.mkString("\n\n---\n\n")
    }
    
    val section1Text = formatMessages(section1)
    val section2Text = formatMessages(section2)
    val section3Text = formatMessages(section3)
    
    // Build user prompt
    val userPrompt = s"""# Conversation to Summarize

This conversation has $total messages and has been running for approximately $durationStr.
The context budget is being approached, triggering this summarization.

## Task List State
$taskListFormatted

## Conversation History

The conversation is divided into three sections by recency. Provide MORE detail for Section 3 (most recent) and LESS for Section 1 (oldest).

### Section 1: Early conversation (messages 1-$section1End) — summarize at LOW detail
$section1Text

### Section 2: Middle conversation (messages $section2Start-$section2End) — summarize at MEDIUM detail
$section2Text

### Section 3: Recent conversation (messages $section3Start-$total) — summarize at HIGH detail
$section3Text

Produce the structured summary now. Remember: the continuing agent will have NO access to the original conversation — your summary is all it gets."""
    
    // Load system prompt
    val systemPrompt = PromptLoader.load("summarize_context_system.md", Map.empty)
    
    // Call LLM with structured response
    val modelId = AssistantOptions.getSummarizationModelId

    Output.writeln(s"[Assistant] Calling summarization agent - Model: $modelId")

    // Summarization is invoked precisely when history has changed enough to
    // approach the context limit, so a cache hit can only come from a prior
    // near-identical run — which is unlikely and not worth the risk of
    // reviving stale summaries. Always bypass the LLM response cache.
    val args = BedrockClient.invokeNoCacheStructured(
      userPrompt,
      StructuredResponseSchema.ContextSummary,
      systemPrompt,
      Some(modelId)
    )
    
    // Parse structured response
    SummarizationResult(
      userGoal = args.get("user_goal").collect {
        case ResponseParser.StringValue(s) => s
      }.getOrElse("(original task not captured)"),
      accomplishments = args.get("accomplishments").collect {
        case ResponseParser.StringValue(s) => s
      }.getOrElse("(no accomplishments recorded)"),
      pendingWork = args.get("pending_work").collect {
        case ResponseParser.StringValue(s) => s
      }.getOrElse("(pending work not captured)"),
      keyContext = args.get("key_context").collect {
        case ResponseParser.StringValue(s) => s
      }.getOrElse("(no key context)"),
      approachHistory = args.get("approach_history").collect {
        case ResponseParser.StringValue(s) => s
      }.getOrElse("(no approach history)"),
      decisionsAndConstraints = args.get("decisions_and_constraints").collect {
        case ResponseParser.StringValue(s) => s
      }.getOrElse("(no constraints)"),
      currentState = args.get("current_state").collect {
        case ResponseParser.StringValue(s) => s
      }.getOrElse("(current state not captured)")
    )
  }

  /**
   * Format the summarization result into a message that seeds the new context.
   * This message becomes the first (and only) message in the replaced history.
   * Accessible to tests via private[assistant].
   * 
   * @param summary The structured summary from the LLM
   * @return Formatted restoration message
   */
  private[assistant] def buildRestorationMessage(summary: SummarizationResult): String = {
    s"""📋 CONTEXT SUMMARY (auto-generated — original conversation was summarized to stay within context limits)

## ORIGINAL TASK
${summary.userGoal}

## CURRENT STATE
${summary.currentState}

## KEY CONTEXT
${summary.keyContext}

## ACCOMPLISHMENTS
${summary.accomplishments}

## PENDING WORK
${summary.pendingWork}

## APPROACH HISTORY
${summary.approachHistory}

## DECISIONS & CONSTRAINTS
${summary.decisionsAndConstraints}

---
**Note:** This summary was automatically generated to preserve conversation context. Task progress and all critical information has been retained. Continue working normally."""
  }
}