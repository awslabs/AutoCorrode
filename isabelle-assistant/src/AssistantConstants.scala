/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Configuration constants for Isabelle Assistant operations.
 *
 * Timeout values are in milliseconds unless noted otherwise.
 * These provide sensible defaults; most can be overridden via AssistantOptions.
 */
object AssistantConstants {
  // Timeout constants (in milliseconds)
  /** Timeout for I/Q proof verification. */
  val DEFAULT_VERIFICATION_TIMEOUT = 30000L
  /** Timeout for sledgehammer proof search. */
  val DEFAULT_SLEDGEHAMMER_TIMEOUT = 15000L
  /** Timeout for quickcheck counterexample search. */
  val DEFAULT_QUICKCHECK_TIMEOUT = 5000L
  /** Timeout for nitpick model finding. */
  val DEFAULT_NITPICK_TIMEOUT = 5000L
  /** Timeout for find_theorems queries. */
  val DEFAULT_FIND_THEOREMS_TIMEOUT = 10000L
  /** Timeout for simplifier tracing (in seconds, not ms). */
  val DEFAULT_TRACE_TIMEOUT = 10
  /** Timeout for waiting for theory to finish loading. */
  val DEFAULT_THEORY_COMPLETION_TIMEOUT = 60000L

  // Retry and limit constants
  val DEFAULT_MAX_VERIFICATION_RETRIES = 3
  val DEFAULT_MAX_VERIFY_CANDIDATES = 5
  val DEFAULT_FIND_THEOREMS_LIMIT = 20
  val DEFAULT_TRACE_DEPTH = 3
  val MAX_ACCUMULATED_MESSAGES = 1000
  val VERIFICATION_CACHE_SIZE = 100

  /** Verification-cache entry TTL. After this many milliseconds an entry is
    * treated as a cache miss and evicted. Guards against stale positives
    * from long-running sessions where the document model reuses command IDs
    * and source text after edits that briefly reverted and then re-applied.
    * Ten minutes is long enough to benefit chatty tool loops against the
    * same commands, and short enough to keep long-lived windows honest. */
  val VERIFICATION_CACHE_TTL_MS: Long = 10L * 60L * 1000L

  /** Per-message hard cap. A single runaway response (or a very large
    * pasted file) can otherwise exceed any context budget on its own,
    * even after the count-based `MAX_ACCUMULATED_MESSAGES` cap trims the
    * history. 500_000 chars is roughly 100_000-125_000 tokens — well
    * beyond any reasonable conversational message but generous enough
    * for occasional large tool outputs before truncation kicks in.
    */
  val MAX_MESSAGE_SIZE_CHARS = 500_000

  // Model parameters
  val DEFAULT_MAX_TOKENS = 4000
  /** Default context budget in tokens. Leaves ~140K-340K headroom depending
    * on the active Claude model (Opus 4.6 / 4.7 support up to 1M, Sonnet
    * 4.6 up to 200K) for tool outputs and the response itself. Raise via
    * Plugin Options if a session is hitting the soft truncation cap. */
  val DEFAULT_MAX_CONTEXT_TOKENS = 60000
  val DEFAULT_MAX_TOOL_ITERATIONS = 10
  /** Size of the sliding window of recent tool-call signatures kept for stuck-loop detection. */
  val LOOP_DETECTION_WINDOW = 6
  /** Minimum number of identical consecutive tool calls that trigger stuck-loop detection. */
  val LOOP_DETECTION_REPEAT_THRESHOLD = 3

  // --- Adaptive tree-of-thought planning ---

  /** Number of distinct approaches the planning brainstorm phase must
    * produce and that the elaboration phase then explores in parallel.
    * Raising this multiplies the LLM-call cost of a single `plan_approach`
    * invocation linearly. Lowering it reduces diversity. Three is a good
    * default: enough variety to compare, few enough calls to stay cheap. */
  val PLANNING_NUM_APPROACHES = 3

  /** Default max iterations for each planning sub-agent's tool-use loop.
    * Kept smaller than the main agent's default because a sub-agent that
    * needs more than this many exploration rounds is usually not converging. */
  val PLANNING_SUB_AGENT_MAX_ITERATIONS = 12

  /** Approach-display threshold: plans longer than this render with an
    * "expand" link instead of inline. Arbitrary visual cut-off — picked so
    * the widget stays a reasonable bubble height on typical displays. */
  val PLANNING_RESULT_INLINE_LINE_LIMIT = 15

  /** Per-invocation wall-clock cap for the whole `invokePlanningAgent`
    * pipeline (ms). Guards against a runaway planning call monopolising
    * the main tool loop; hits after this duration return whatever the
    * pipeline has accumulated so far. */
  val PLANNING_TOTAL_TIMEOUT_MS = 180_000L
  val MIN_MAX_TOKENS = 100
  val MIN_MAX_CONTEXT_TOKENS = 1000
  // No MAX_MAX_TOKENS/MAX_MAX_CONTEXT_TOKENS - models like Opus 4.6 support up to 1M tokens

  // File and content limits
  val MAX_CONTENT_PREVIEW_LENGTH = 200
  val MAX_ERROR_MESSAGE_LENGTH = 500
  val MAX_RESPONSE_LENGTH = 10000
  val MAX_CHAT_CONTEXT_CHARS = 210000  // ~60K tokens at 3.5 chars/token

  // Network constants
  val DEFAULT_MCP_PORT = 8765

  /** Minimum spacing between Bedrock API calls, in milliseconds. Acts as a
    * client-side rate-limit floor so back-to-back tool iterations don't
    * trip the service-side throttle. 200ms matches Anthropic's recommended
    * floor for well-behaved streaming clients; raise via `BedrockClient`
    * if the circuit breaker keeps tripping on throttling. */
  val MIN_API_INTERVAL_MS = 200L

  /** Per-entry cap (in chars) on the chat input history buffer. A large
    * pasted document would otherwise persist in memory for the session up
    * to the 500-entry cap. 64K chars (~16K tokens) covers any reasonable
    * typed or copy-pasted prompt without letting a 1MB paste live on
    * indefinitely. */
  val MAX_HISTORY_ENTRY_CHARS = 64 * 1024
  
  // Operation timeouts and buffers
  val TIMEOUT_BUFFER_MS = 2000L
  val SLEDGEHAMMER_GUARD_TIMEOUT = 2000L
  val CONTEXT_FETCH_TIMEOUT = 3000L

  /** Chat-path context resolution timeout. Tighter than the general
    * [[CONTEXT_FETCH_TIMEOUT]] because a free-form chat call must not
    * block the user for three seconds on an I/Q lookup that may not
    * even produce useful context. After this, the chat proceeds with
    * no resolved target; the model still answers. */
  val CHAT_CONTEXT_FETCH_TIMEOUT = 1000L
  val SUGGESTION_COLLECTION_TIMEOUT = 90000L
  val RETRY_BASE_DELAY_MS = 1000L
  val MAX_RETRY_ATTEMPTS = 3
  
  // Thread coordination timeouts
  val GUI_DISPATCH_TIMEOUT = 3000L
  val GUI_DISPATCH_TIMEOUT_SEC = 3L
  val BUFFER_OPERATION_TIMEOUT = 5000L
  val BUFFER_OPERATION_TIMEOUT_SEC = 5L
  val ASK_USER_TIMEOUT_SEC = 60L
  
  // Query and search limits
  val MAX_CONSTANTS_FOR_FIND_THEOREMS = 5
  val MAX_FIND_THEOREMS_RESULTS = 100
  val MAX_SEARCH_RESULTS = 100
  val DEFAULT_READ_THEORY_MAX_LINES = 300
  val DEFAULT_TRACE_MAX_LINES = 100
  val DEFAULT_GET_ENTITIES_MAX_RESULTS = 50
  val DEFAULT_SEARCH_ALL_THEORIES_MAX_RESULTS = 20
  
  // Cache configuration
  val LLM_CACHE_SIZE = 100
  val LLM_CACHE_EXPIRY_HOURS = 1

  // Context summarization
  val DEFAULT_SUMMARIZATION_THRESHOLD = 0.75  // Trigger at 75% of budget
  val MIN_SUMMARIZATION_THRESHOLD = 0.5
  val MAX_SUMMARIZATION_THRESHOLD = 0.95
  val SUMMARIZATION_TARGET_RATIO = 0.25  // After summarization, aim for 25% usage
  val MIN_MESSAGES_FOR_SUMMARIZATION = 5  // Don't summarize if fewer messages

  /** Heuristic delay for PIDE to process buffer edits (ms). */
  val PIDE_PROCESSING_DELAY = 3000L
  
  // UI constants
  val SUGGESTION_DISPLAY_LIMIT = 10
  val ERROR_TRUNCATION_LENGTH = 100
  val MAX_INSERT_ACTIONS = 200
  val CHAT_INPUT_ROWS = 4
  val CHAT_INPUT_COLUMNS = 40
  val CHAT_INPUT_PLACEHOLDER = "Ask a question, or type :help for commands"

  // I/Q operation names
  val IQ_OPERATION_ISAR_EXPLORE = "isar_explore"
  val IQ_OPERATION_FIND_THEOREMS = "find_theorems"

  // Status message constants
  val STATUS_READY = "Ready"
  val STATUS_CANCELLED = "Cancelled"
  val STATUS_THINKING = "Thinking…"
  val STATUS_VERIFYING = "Verifying…"
  
  /** Canonical "I/Q not running" message surfaced to the LLM by tool
    * handlers that depend on the I/Q proof-verification backplane.
    * Duplicated literals previously drifted (trailing period vs none,
    * capitalisation, wording) — one constant keeps the string that the
    * LLM sees identical across all handlers so it can recognise this
    * class of failure reliably. */
  val TOOL_IQ_UNAVAILABLE = "I/Q plugin not available."

  // Security: Sensitive argument name patterns for redaction
  val SENSITIVE_ARG_TOKENS: Set[String] = Set(
    // Substring match against the lowercased argument name — keep the tokens
    // narrow enough to dodge false positives on innocent names, but cover the
    // common LLM-emitted spellings ("apiKey", "apikey", "api_key").
    "token", "secret", "password", "auth", "credential", "api_key", "apikey"
  )

  /** Canonical text for "cursor resolution came up empty" messages. One
    * phrasing per kind, all terminated with a period, all using "at
    * cursor." (rather than "at cursor position." or "at target
    * location") — the user sees the same words whether the cursor failed
    * to resolve from the chat, the right-click menu, or a tool call.
    *
    * These are deliberately terse: the user already knows their cursor
    * was the input; repeating "position" adds no information.
    */
  object UIText {
    val NO_COMMAND_AT_CURSOR      = "No command at cursor."
    val NO_GOAL_AT_CURSOR         = "No goal at cursor."
    val NO_ERROR_AT_CURSOR        = "No error at cursor."
    val NO_DEFINITION_AT_CURSOR   = "No definition at cursor."
    val NO_PROOF_BLOCK_AT_CURSOR  = "No proof block at cursor."
    val NO_TYPE_AT_CURSOR         = "No type information at cursor."
    val NO_SUGGESTIONS            = "No suggestions found."
    val NO_PROOF_PATTERN          = "No proof pattern at cursor."
  }
}
