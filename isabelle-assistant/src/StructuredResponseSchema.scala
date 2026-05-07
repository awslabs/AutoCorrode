/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Structured response schemas for forced tool_choice.
 * Used with BedrockClient.invokeStructured to guarantee parseable JSON responses.
 */
case class StructuredResponseSchema(
  name: String,
  description: String,
  jsonSchema: String
)

object StructuredResponseSchema {
  /** Schema for planning agent brainstorm phase: generates
    * [[AssistantConstants.PLANNING_NUM_APPROACHES]] distinct approaches.
    * The JSON string literal is built once at construction time so the count
    * in the schema, the count in the prompt, and the count in the
    * orchestrator are all driven by one constant. */
  val PlanningBrainstorm: StructuredResponseSchema = {
    val n = AssistantConstants.PLANNING_NUM_APPROACHES
    StructuredResponseSchema(
      name = "brainstorm_approaches",
      description = s"Generate $n distinct approaches to solve the given problem.",
      jsonSchema = s"""{
      "type": "object",
      "properties": {
        "approaches": {
          "type": "array",
          "description": "$n distinct approaches to the problem",
          "items": {
            "type": "object",
            "properties": {
              "id": {
                "type": "integer",
                "description": "Approach ID (1-based, distinct per approach)"
              },
              "title": {
                "type": "string",
                "description": "Short descriptive title for this approach"
              },
              "summary": {
                "type": "string",
                "description": "2-3 sentence summary of the approach"
              },
              "key_idea": {
                "type": "string",
                "description": "The core insight or strategy that makes this approach work"
              },
              "exploration_hints": {
                "type": "array",
                "description": "Hints for what to explore when elaborating this approach",
                "items": { "type": "string" }
              }
            },
            "required": ["id", "title", "summary", "key_idea", "exploration_hints"]
          },
          "minItems": $n,
          "maxItems": $n
        }
      },
      "required": ["approaches"]
    }"""
    )
  }

  /** Schema for planning agent selection phase: picks best approach and produces final plan. */
  val PlanningSelect: StructuredResponseSchema = StructuredResponseSchema(
    name = "select_best_plan",
    description = "Select the best approach from the elaborated plans and produce a final refined plan.",
    jsonSchema = """{
      "type": "object",
      "properties": {
        "selected_approach": {
          "type": "integer",
          "description": "The ID of the selected approach (1, 2, or 3)"
        },
        "reasoning": {
          "type": "string",
          "description": "Explanation of why this approach was selected over the others"
        },
        "plan": {
          "type": "string",
          "description": "The final detailed plan, potentially refined or combining elements from multiple approaches"
        }
      },
      "required": ["selected_approach", "reasoning", "plan"]
    }"""
  )

  /** Schema for context summarization: compress conversation history into structured summary. */
  val ContextSummary: StructuredResponseSchema = StructuredResponseSchema(
    name = "summarize_context",
    description = "Summarize the conversation history into a structured summary that preserves critical information.",
    jsonSchema = """{
      "type": "object",
      "properties": {
        "user_goal": {
          "type": "string",
          "description": "The user's original request or task, quoted directly or faithfully paraphrased"
        },
        "accomplishments": {
          "type": "string",
          "description": "What has been completed so far. Be specific: list file changes, theorems proved, lemmas extracted, etc."
        },
        "pending_work": {
          "type": "string",
          "description": "What still needs to be done. Reference any task list items. Be explicit about the next steps."
        },
        "key_context": {
          "type": "string",
          "description": "Critical names, files, theorems, definitions that the continuing agent needs to reference. Include exact identifiers, file paths, and proof method names."
        },
        "approach_history": {
          "type": "string",
          "description": "What approaches were tried, in chronological order. Include more detail for recent attempts. Note what worked and what didn't."
        },
        "decisions_and_constraints": {
          "type": "string",
          "description": "Key decisions made. User preferences stated. Things to avoid. Required approaches or styles."
        },
        "current_state": {
          "type": "string",
          "description": "The precise current state: what was the last action, what was its result, what is the immediate situation right now"
        }
      },
      "required": ["user_goal", "accomplishments", "pending_work", "key_context", "approach_history", "decisions_and_constraints", "current_state"]
    }"""
  )
}
