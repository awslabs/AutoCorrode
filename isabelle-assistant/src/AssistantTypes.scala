/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Opaque type aliases for stringly-typed values throughout Isabelle Assistant.
 * 
 * These type aliases provide compile-time type safety by distinguishing between
 * different string "roles" in the type system. Using opaque types ensures these
 * are checked at compile time but have zero runtime overhead.
 * 
 * Usage guidelines:
 * - Use these aliases in all public API signatures
 * - Internal functions should also use them for consistency
 * - These prevent accidental mixing of semantically different strings
 */
object AssistantTypes {
  /** AWS Bedrock model identifier (e.g., "anthropic.claude-3-sonnet-20240229-v1:0"). */
  opaque type ModelId = String
  object ModelId {
    def apply(s: String): ModelId = s
    extension (m: ModelId) def value: String = m
  }
  
  /** AWS region identifier (e.g., "us-east-1"). */
  opaque type Region = String
  object Region {
    def apply(s: String): Region = s
    extension (r: Region) def value: String = r
  }
  
  /** Complete prompt text sent to LLM. */
  opaque type PromptText = String
  object PromptText {
    def apply(s: String): PromptText = s
    extension (p: PromptText) def value: String = p
  }
  
  /** Isabelle proof text (e.g., "by simp", "proof ... qed"). */
  opaque type ProofText = String
  object ProofText {
    def apply(s: String): ProofText = s
    extension (p: ProofText) def value: String = p
  }
  
  /** Isabelle command source text (e.g., "lemma foo: P"). */
  opaque type CommandText = String
  object CommandText {
    def apply(s: String): CommandText = s
    extension (c: CommandText) def value: String = c
  }
  
  /** Goal state text from PIDE output panel. */
  opaque type GoalState = String
  object GoalState {
    def apply(s: String): GoalState = s
    extension (g: GoalState) def value: String = g
  }
  
  /** Error message text. */
  opaque type ErrorMessage = String
  object ErrorMessage {
    def apply(s: String): ErrorMessage = s
    extension (e: ErrorMessage) def value: String = e
  }
  
  /** LLM response text. */
  opaque type ResponseText = String
  object ResponseText {
    def apply(s: String): ResponseText = s
    extension (r: ResponseText) def value: String = r
  }
  
  /** Theory file name (e.g., "Foo.thy"). */
  opaque type TheoryName = String
  object TheoryName {
    def apply(s: String): TheoryName = s
    extension (t: TheoryName) def value: String = t
  }
  
  /** Lemma or theorem name identifier. */
  opaque type LemmaName = String
  object LemmaName {
    def apply(s: String): LemmaName = s
    extension (l: LemmaName) def value: String = l
  }
  
  /** JSON payload string for API requests. */
  opaque type JsonPayload = String
  object JsonPayload {
    def apply(s: String): JsonPayload = s
    extension (j: JsonPayload) def value: String = j
  }
  
  /** Markdown-formatted text for chat display. */
  opaque type MarkdownText = String
  object MarkdownText {
    def apply(s: String): MarkdownText = s
    extension (m: MarkdownText) def value: String = m
  }
  
  /** HTML-formatted text for rendering. */
  opaque type HtmlText = String
  object HtmlText {
    def apply(s: String): HtmlText = s
    extension (h: HtmlText) def value: String = h
  }
}