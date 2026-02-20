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

  // Model parameters
  val DEFAULT_TEMPERATURE = 0.3
  val DEFAULT_MAX_TOKENS = 4000
  val DEFAULT_MAX_TOOL_ITERATIONS = 10
  val DEFAULT_LOOP_DETECTION_WINDOW = 3
  val MIN_TEMPERATURE = 0.0
  val MAX_TEMPERATURE = 1.0
  val MIN_MAX_TOKENS = 100
  val MAX_MAX_TOKENS = 8000

  // File and content limits
  val MAX_CONTENT_PREVIEW_LENGTH = 200
  val MAX_ERROR_MESSAGE_LENGTH = 500
  val MAX_RESPONSE_LENGTH = 10000
  val MAX_CHAT_CONTEXT_CHARS = 100000

  // Network constants
  val DEFAULT_MCP_PORT = 8765
  
  // Operation timeouts and buffers
  val TIMEOUT_BUFFER_MS = 2000L
  val SLEDGEHAMMER_GUARD_TIMEOUT = 2000L
  val CONTEXT_FETCH_TIMEOUT = 3000L
  val SUGGESTION_COLLECTION_TIMEOUT = 90000L
  val RETRY_BASE_DELAY_MS = 1000L
  val MAX_RETRY_ATTEMPTS = 3
  
  // Thread coordination timeouts
  val GUI_DISPATCH_TIMEOUT = 3000L
  val GUI_DISPATCH_TIMEOUT_SEC = 3L
  val BUFFER_OPERATION_TIMEOUT = 5000L
  val BUFFER_OPERATION_TIMEOUT_SEC = 5L
  
  // Query and search limits
  val MAX_CONSTANTS_FOR_FIND_THEOREMS = 5
  val MAX_FIND_THEOREMS_RESULTS = 100
  val MAX_SEARCH_RESULTS = 100
  
  // Cache configuration
  val LLM_CACHE_SIZE = 100
  val LLM_CACHE_EXPIRY_HOURS = 1

  // Auto-prover defaults
  val DEFAULT_PROVE_MAX_STEPS = 20
  val DEFAULT_PROVE_RETRIES_PER_STEP = 3
  val DEFAULT_PROVE_STEP_TIMEOUT = 30000L
  val DEFAULT_PROVE_BRANCHES = 3
  /** Overall wall-clock timeout for :prove auto-prover (ms). */
  val DEFAULT_PROVE_TIMEOUT = 300000L
  /** Timeout for individual LLM calls in auto-prover (ms). */
  val PROVE_LLM_CALL_TIMEOUT = 90000L
  /** Sub-deadline for proving speculated auxiliary lemmas (ms). */
  val PROVE_LEMMA_SUB_DEADLINE = 60000L
  /** Maximum steps when proving speculated lemmas (limit to prevent runaway). */
  val PROVE_LEMMA_MAX_STEPS = 10
  /** Heuristic delay for PIDE to process buffer edits (ms). */
  val PIDE_PROCESSING_DELAY = 3000L
  
  // UI constants
  val SUGGESTION_DISPLAY_LIMIT = 10
  val ERROR_TRUNCATION_LENGTH = 100
  val MAX_INSERT_ACTIONS = 200
  val CHAT_INPUT_ROWS = 4
  val CHAT_INPUT_COLUMNS = 40
  val CHAT_INPUT_PLACEHOLDER = "Ask a question, or type : for commands..."

  // I/Q operation names
  val IQ_OPERATION_ISAR_EXPLORE = "isar_explore"
  val IQ_OPERATION_FIND_THEOREMS = "find_theorems"

  // Status message constants
  val STATUS_READY = "Ready"
  val STATUS_CANCELLED = "Cancelled"
  val STATUS_THINKING = "Thinking..."
  val STATUS_VERIFYING = "Verifying..."
}
