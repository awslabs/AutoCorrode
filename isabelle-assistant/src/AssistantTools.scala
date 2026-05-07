/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import java.util.concurrent.{CountDownLatch, TimeUnit}
import scala.util.control.NonFatal
import software.amazon.awssdk.thirdparty.jackson.core.JsonGenerator

import ToolArgs._

/** Tool definitions and execution for LLM tool use (Anthropic function
  * calling). Tools give the LLM autonomous access to theory files, goal state,
  * and Isabelle queries.
  */
object AssistantTools {

  /** One parameter in a tool's JSON-schema signature, as exposed to the LLM.
    *
    * @param name        Parameter key as it appears in the tool call JSON
    * @param typ         JSON-schema primitive name (e.g. "string", "integer",
    *                    "boolean"). Complex types are expressed as "object"
    *                    with additional schema described in the description.
    * @param description Human-readable doc shown to the model; include value
    *                    shape, defaults, and any validation rules here
    * @param required    Whether the parameter must be present in the call.
    *                    Optional parameters should document their default. */
  /** Internal handler result. Lets downstream handlers branch on the
    * success/error shape without reparsing a stringly-typed "Error: …"
    * prefix. The wire format sent back to the LLM is still a plain String
    * (produced by [[ToolResult.render]]), so this ADT only ever crosses
    * private method boundaries.
    *
    * Use [[Ok]] for a normal payload, [[Err]] with a free-form message for
    * a recoverable failure, and [[Unavailable]] for the specific
    * "dependency missing" failure (currently I/Q not running) so callers
    * that want to display a distinct status can do so. */
  private sealed trait ToolResult {
    def render: String = this match {
      case ToolResult.Ok(text)       => text
      case ToolResult.Err(message)   => s"Error: $message"
      case ToolResult.Unavailable(m) => m
    }
    def isError: Boolean = this match {
      case _: ToolResult.Ok => false
      case _                => true
    }
  }
  private object ToolResult {
    final case class Ok(text: String) extends ToolResult
    final case class Err(message: String) extends ToolResult
    final case class Unavailable(message: String) extends ToolResult
  }

  case class ToolParam(
      name: String,
      typ: String,
      description: String,
      required: Boolean = false
  )

  /** Definition of a single Anthropic tool this plugin exposes.
    *
    * Every tool listed in [[tools]] falls into one of four semantic classes
    * — callers should treat these as the informal typing for each handler:
    *
    *   - '''Pure query''': read-only, no side effects (e.g. `read_theory`,
    *     `search_theories`, `get_entities`). Safe to retry; handler body
    *     never mutates disk, IDE state, or Isabelle's document model.
    *   - '''I/Q introspection''': calls into the I/Q MCP backplane to learn
    *     about the current Isabelle session (e.g. `find_theorems`,
    *     `get_processing_status`). Requires I/Q plugin available; handlers
    *     return a user-visible error when it is not.
    *   - '''Mutation''': writes to the user's disk or to the editor
    *     (`edit_theory`, `create_theory`). Subject to I/Q's mutation-roots
    *     authorization; errors on Left should be surfaced verbatim so the
    *     user can adjust their settings.
    *   - '''Interactive / heavy''': synchronously blocks the turn on a
    *     long-running or user-prompt operation (`ask_user`,
    *     `run_sledgehammer`, `run_nitpick`). These interact with the
    *     ToolPermissions flow (AskAtFirstUse) and may return ask-user
    *     denied errors.
    *
    * Handlers are wired to tool IDs in the `toolHandlers` map below. When
    * adding a new tool, also update `ToolPermissions.defaultPermissions`
    * and `toolDescriptionsById`, and add test coverage in
    * `ToolIdTest.scala`, `AssistantToolsTest.scala`, and
    * `ToolPermissionsTest.scala`. See CONTRIBUTING.md 'Adding a New Tool'.
    *
    * @param id          Stable identifier; `id.wireName` is the string the
    *                    LLM sees in tool-use responses
    * @param description One-line purpose statement shown to the model;
    *                    include return-shape and edge-case notes here
    * @param params      JSON-schema parameters the tool accepts */
  case class ToolDef(
      id: ToolId,
      description: String,
      params: List[ToolParam]
  ) {
    val name: String = id.wireName
  }

  /** Full registry of tools the Assistant exposes to the LLM.
    *
    * Order does not affect selection — Anthropic picks by semantic match
    * from the descriptions — but grouping related tools together makes the
    * file easier to audit. Broadly, the list proceeds:
    *   1. theory I/O (read / list / search / edit / create)
    *   2. I/Q introspection (find_theorems, verify_proof, diagnostics)
    *   3. heavy search (sledgehammer, nitpick, quickcheck)
    *   4. interactive helpers (ask_user, memory_*, task_list_*)
    *   5. web (web_search, web_fetch) — guarded by ToolPermissions
    *
    * See `ToolDef`'s scaladoc for the four semantic classes and pointers
    * to CONTRIBUTING.md for the "Adding a New Tool" checklist. */
  val tools: List[ToolDef] = List(
    ToolDef(
      ToolId.ReadTheory,
      "Read lines from an open Isabelle theory file. Returns the file content. Use start_line/end_line to read a specific range.",
      List(
        ToolParam(
          "theory",
          "string",
          "Theory name (e.g. 'Foo' or 'Foo.thy')",
          required = true
        ),
        ToolParam(
          "start_line",
          "integer",
          "First line to read (1-based, default: 1)"
        ),
        ToolParam(
          "end_line",
          "integer",
          "Last line to read (default: end of file)"
        )
      )
    ),
    ToolDef(
      ToolId.ListTheories,
      "List all currently open Isabelle theory files.",
      Nil
    ),
    ToolDef(
      ToolId.SearchInTheory,
      "Search for a text pattern in an open theory file. Returns matching lines with line numbers.",
      List(
        ToolParam("theory", "string", "Theory name", required = true),
        ToolParam(
          "pattern",
          "string",
          "Text pattern to search for (case-insensitive)",
          required = true
        ),
        ToolParam(
          "max_results",
          "integer",
          "Maximum results to return (default: 20)"
        )
      )
    ),
    ToolDef(
      ToolId.SearchTheories,
      "Search for a text pattern in theory files. Unified tool replacing search_in_theory and search_all_theories. Returns matching lines with theory names and line numbers.",
      List(
        ToolParam(
          "pattern",
          "string",
          "Text pattern to search for (case-insensitive)",
          required = true
        ),
        ToolParam(
          "scope",
          "string",
          "Scope: 'current' (current buffer), 'all' (all open theories), or a theory name",
          required = true
        ),
        ToolParam(
          "max_results",
          "integer",
          "Maximum results to return (default: 20)"
        )
      )
    ),
    ToolDef(
      ToolId.GetGoalState,
      "Get the current proof goal state at the cursor position. Returns the goal or empty if not in a proof.",
      Nil
    ),
    ToolDef(
      ToolId.GetSubgoal,
      "Extract a single subgoal by index from the current proof state. More efficient than get_goal_state for multi-subgoal proofs when you only need to focus on one subgoal.",
      List(
        ToolParam(
          "index",
          "integer",
          "Subgoal index (1-based). Use 1 for the first subgoal.",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.GetProofContext,
      "Get local facts and assumptions in scope at the cursor position.",
      Nil
    ),
    ToolDef(
      ToolId.FindTheorems,
      "Search for Isabelle theorems matching a pattern. Requires I/Q plugin.",
      List(
        ToolParam(
          "pattern",
          "string",
          "Search pattern for find_theorems",
          required = true
        ),
        ToolParam("max_results", "integer", "Maximum results (default: 20)")
      )
    ),
    ToolDef(
      ToolId.VerifyProof,
      "Verify a proof method against the current goal using Isabelle. Returns success/failure. Requires I/Q plugin.",
      List(
        ToolParam(
          "proof",
          "string",
          "Proof method to verify (e.g. 'by simp', 'by auto')",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.RunSledgehammer,
      "Run Sledgehammer to find proofs using external ATP provers. Returns found proof methods. Requires I/Q plugin.",
      Nil
    ),
    ToolDef(
      ToolId.RunNitpick,
      "Run Nitpick model finder to search for counterexamples to the current goal. Returns counterexample if found. Requires I/Q plugin.",
      Nil
    ),
    ToolDef(
      ToolId.RunQuickcheck,
      "Run QuickCheck to test the current goal with random examples. Returns counterexample if found. Requires I/Q plugin.",
      Nil
    ),
    ToolDef(
      ToolId.FindCounterexample,
      "Search for counterexamples to the current goal using Nitpick or QuickCheck. Returns counterexample if found. Requires I/Q plugin.",
      List(
        ToolParam(
          "method",
          "string",
          "Method: 'nitpick', 'quickcheck', or 'both' (default: 'quickcheck')"
        )
      )
    ),
    ToolDef(
      ToolId.GetType,
      "Get type information for the term at the cursor position. Returns the term and its type.",
      Nil
    ),
    ToolDef(
      ToolId.GetCommandText,
      "Get the source text of the Isabelle command at the cursor position.",
      Nil
    ),
    ToolDef(
      ToolId.GetErrors,
      "Get error messages from PIDE's processed region. IMPORTANT: Only returns errors from the already-processed portion of the theory. To check if a file is completely error-free, first use set_cursor_position to move to the end of the file, then call get_errors. By default returns all errors in the current buffer with line numbers. Use scope='cursor' to get only errors at cursor position.",
      List(
        ToolParam(
          "scope",
          "string",
          "Scope: 'all' (default, all errors in current buffer), 'cursor' (only at cursor position), or a theory name"
        )
      )
    ),
    ToolDef(
      ToolId.GetDiagnostics,
      "Get error or warning messages from PIDE's processed region. IMPORTANT: Only returns diagnostics from the already-processed portion of the theory. To check if a file is completely error/warning-free, first use set_cursor_position to move to the end of the file, then call get_diagnostics.",
      List(
        ToolParam(
          "severity",
          "string",
          "Severity level: 'error', 'warning', or 'all'",
          required = true
        ),
        ToolParam(
          "scope",
          "string",
          "Scope: 'all' (default, all diagnostics in current buffer), 'cursor' (only at cursor position), or a theory name"
        ),
        ToolParam(
          "count_only",
          "boolean",
          "Return only counts instead of full diagnostic messages (default: false)"
        )
      )
    ),
    ToolDef(
      ToolId.GetDefinitions,
      "Get definitions for specified constant or type names. Returns the definition text for each name. Requires I/Q plugin.",
      List(
        ToolParam(
          "names",
          "string",
          "Space-separated list of constant/type names to look up",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.GetFileStats,
      "Get file statistics (line count, entity count, processing status) without reading full content. Efficient alternative to read_theory + get_entities for overview. Requires I/Q plugin.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      ToolId.GetProcessingStatus,
      "Get PIDE processing status (unprocessed/running/finished/failed command counts). Use this to check if a theory has been fully processed before querying for errors. Requires I/Q plugin.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      ToolId.GetSorryPositions,
      "Find all sorry/oops commands in a theory file with their line numbers and enclosing proof names. Useful for identifying incomplete proofs. Requires I/Q plugin.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      ToolId.ExecuteStep,
      "Execute a proof step and return the resulting proof state. Use this to explore what happens when you apply a proof method. Returns the new goal state and whether the proof is complete. Requires I/Q plugin.",
      List(
        ToolParam(
          "proof",
          "string",
          "Proof text to execute (e.g., 'by simp', 'apply auto')",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.TraceSimplifier,
      "Trace the simplifier to understand rewriting steps. Returns detailed trace of simp/auto operations. Requires I/Q plugin.",
      List(
        ToolParam(
          "method",
          "string",
          "Method to trace: 'simp' or 'auto' (default: 'simp')"
        )
      )
    ),
    ToolDef(
      ToolId.GetProofBlock,
      "Get the full proof block (lemma/theorem...qed/done) at the cursor position. Returns the complete proof text including the statement.",
      Nil
    ),
    ToolDef(
      ToolId.GetProofOutline,
      "Get a structural outline of the proof block at the cursor position. Returns only the proof skeleton (keyword lines) with line numbers, filtering out proof details. Useful for understanding proof structure without full content.",
      Nil
    ),
    ToolDef(
      ToolId.GetContextInfo,
      "Get structured context information at cursor: whether in a proof, whether there's a goal, whether on an error, etc. Returns a summary of the cursor context.",
      Nil
    ),
    ToolDef(
      ToolId.SearchAllTheories,
      "Search for a text pattern across all open theory files. Returns matching lines with theory names and line numbers.",
      List(
        ToolParam(
          "pattern",
          "string",
          "Text pattern to search for (case-insensitive)",
          required = true
        ),
        ToolParam(
          "max_results",
          "integer",
          "Maximum total results across all theories (default: 50)"
        )
      )
    ),
    ToolDef(
      ToolId.GetDependencies,
      "Get the import dependencies for a specific theory file. Returns the list of imported theories.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      ToolId.GetWarnings,
      "Get warning messages from PIDE's processed region. IMPORTANT: Only returns warnings from the already-processed portion of the theory. To check if a file is completely warning-free, first use set_cursor_position to move to the end of the file, then call get_warnings. By default returns all warnings in the current buffer with line numbers. Use scope='cursor' to get only warnings at cursor position.",
      List(
        ToolParam(
          "scope",
          "string",
          "Scope: 'all' (default, all warnings in current buffer), 'cursor' (only at cursor position), or a theory name"
        )
      )
    ),
    ToolDef(
      ToolId.SetCursorPosition,
      "Move the cursor to a specific line number in the current theory. This allows inspection of goals and context at different positions. Returns confirmation or error.",
      List(
        ToolParam(
          "line",
          "integer",
          "Line number to move cursor to (1-based)",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.EditTheory,
      "Edit a theory file by inserting, replacing, or deleting text at specified line ranges. Use read_theory first to see current content. For multi-line inserts/replacements, include literal \\n characters in the text parameter. All edits are wrapped in compound edits for proper undo support.",
      List(
        ToolParam("theory", "string", "Theory name", required = true),
        ToolParam(
          "operation",
          "string",
          "Operation: 'insert', 'replace', or 'delete'",
          required = true
        ),
        ToolParam(
          "start_line",
          "integer",
          "Starting line number (1-based)",
          required = true
        ),
        ToolParam(
          "end_line",
          "integer",
          "Ending line number for replace/delete operations (1-based, inclusive)"
        ),
        ToolParam(
          "text",
          "string",
          "Text to insert or use as replacement (required for insert/replace)"
        )
      )
    ),
    ToolDef(
      ToolId.TryMethods,
      "Try multiple proof methods at once and return which ones succeed. More efficient than calling verify_proof repeatedly. Returns results for all methods. Requires I/Q plugin.",
      List(
        ToolParam(
          "methods",
          "string",
          "Comma-separated list of proof methods to try (e.g., 'by simp, by auto, by blast')",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.GetEntities,
      "List all named entities (lemmas, definitions, datatypes, etc.) in a theory file with their line numbers. Returns a structured listing of the theory's contents.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      ToolId.WebSearch,
      "Search the web for Isabelle documentation, AFP entries, or formalization patterns. Returns titles, snippets, and URLs from search results.",
      List(
        ToolParam("query", "string", "Search query", required = true),
        ToolParam(
          "max_results",
          "integer",
          "Maximum results to return (default: 5)"
        )
      )
    ),
    ToolDef(
      ToolId.CreateTheory,
      "Create a new Isabelle theory file in the same directory as the current buffer. The file will be opened in jEdit after creation.",
      List(
        ToolParam(
          "name",
          "string",
          "Theory name (without .thy extension)",
          required = true
        ),
        ToolParam(
          "imports",
          "string",
          "Space-separated list of theories to import (default: 'Main')"
        ),
        ToolParam(
          "content",
          "string",
          "Initial content to add after 'begin' (optional)"
        )
      )
    ),
    ToolDef(
      ToolId.OpenTheory,
      "Open an existing theory file that is not currently open. Makes it available for inspection and editing with other tools.",
      List(
        ToolParam(
          "path",
          "string",
          "Path to theory file (relative or absolute)",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.AskUser,
      "Ask the user a multiple-choice question when you are uncertain about something, need clarification on their intent, or want their perspective on a decision. The user will see the question and options in the chat panel and click their choice. Use this sparingly — only when the answer genuinely affects your approach.",
      List(
        ToolParam(
          "question",
          "string",
          "The question to present to the user. Be clear and concise.",
          required = true
        ),
        ToolParam(
          "options",
          "string",
          "Comma-separated list of short option labels (minimum 2). Keep options brief and clear for best UX.",
          required = true
        ),
        ToolParam(
          "context",
          "string",
          "Optional brief context explaining why you're asking (shown as a subtitle)"
        )
      )
    ),
    ToolDef(
      ToolId.TaskListAdd,
      "Add a new task to the session task list. Each task should have a clear title, detailed description of what needs to be done, and specific acceptance criteria for completion.",
      List(
        ToolParam(
          "title",
          "string",
          "Brief task title (e.g., 'Implement authentication')",
          required = true
        ),
        ToolParam(
          "description",
          "string",
          "Detailed description of what needs to be done",
          required = true
        ),
        ToolParam(
          "acceptance_criteria",
          "string",
          "Clear criteria for when the task is considered complete",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.TaskListDone,
      "Mark a task as completed. Use this when a task has been successfully finished and all acceptance criteria have been met.",
      List(
        ToolParam(
          "task_id",
          "integer",
          "The ID of the task to mark as done",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.TaskListIrrelevant,
      "Mark a task as irrelevant or no longer needed. Use this when a task is obsolete, out of scope, or superseded by other work.",
      List(
        ToolParam(
          "task_id",
          "integer",
          "The ID of the task to mark as irrelevant",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.TaskListNext,
      "Get the next pending task to work on. Returns the first task in the list that has not been completed or marked irrelevant.",
      Nil
    ),
    ToolDef(
      ToolId.TaskListShow,
      "Show all tasks in the task list with their current statuses. Displays a visual overview of progress.",
      Nil
    ),
    ToolDef(
      ToolId.TaskListGet,
      "Get detailed information about a specific task, including its full description and acceptance criteria.",
      List(
        ToolParam(
          "task_id",
          "integer",
          "The ID of the task to retrieve details for",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.MemoryAdd,
      "Add a new memory to the persistent knowledge base under a topic. Memories survive across chat sessions. Use this to record important discoveries about the user, Isabelle behavior, project patterns, or useful techniques.",
      List(
        ToolParam(
          "topic",
          "string",
          "Topic name (e.g., 'user', 'isabelle', 'project'). Use lowercase alphanumeric and underscores only.",
          required = true
        ),
        ToolParam(
          "title",
          "string",
          "Short, scannable title for the memory (max 200 characters)",
          required = true
        ),
        ToolParam(
          "body",
          "string",
          "Detailed memory content (max 2000 characters)",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.MemoryDelete,
      "Delete a specific memory by its ID. Use this to remove outdated or incorrect memories.",
      List(
        ToolParam(
          "memory_id",
          "integer",
          "The ID of the memory to delete",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.MemoryDeleteTopic,
      "Delete an entire topic and all its memories. Use this when a topic is no longer relevant.",
      List(
        ToolParam(
          "topic",
          "string",
          "Topic name to delete",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.MemoryListTopics,
      "List all memory topics with their memory counts. Use this to see what knowledge has been recorded.",
      Nil
    ),
    ToolDef(
      ToolId.MemoryList,
      "List all memories in a specific topic, showing IDs and titles.",
      List(
        ToolParam(
          "topic",
          "string",
          "Topic name to list memories from",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.MemoryGet,
      "Get the full details of a specific memory, including title, body, and creation timestamp.",
      List(
        ToolParam(
          "memory_id",
          "integer",
          "The ID of the memory to retrieve",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.MemorySearch,
      "Search for memories matching a text pattern across all topics. Returns matching memories with context snippets.",
      List(
        ToolParam(
          "query",
          "string",
          "Search query (case-insensitive)",
          required = true
        )
      )
    ),
    ToolDef(
      ToolId.PlanApproach,
      "Run the adaptive tree-of-thought planning agent on a complex problem. Brainstorms three distinct approaches, elaborates each in parallel using read-only exploration tools, and returns a final refined plan. Use BEFORE starting non-trivial multi-step work (complex proofs, multi-file refactors). Returns the selected plan text; the caller should then translate it into concrete task_list_add calls.",
      List(
        ToolParam(
          "problem",
          "string",
          "Detailed problem description. Include the concrete goal, any known constraints, and the current state if relevant. Longer is better — the planner elaborates from this seed.",
          required = true
        ),
        ToolParam(
          "scope",
          "string",
          "Short hint about the planning scope. Typical values: 'proof', 'refactor', 'multi-file'. Used only to steer the brainstorm."
        ),
        ToolParam(
          "context",
          "string",
          "Optional extra context (goal state, error message, surrounding code). Passed through to the planning sub-agents."
        )
      )
    )
  )

  private val toolsById: Map[ToolId, ToolDef] = tools.map(t => t.id -> t).toMap
  require(
    toolsById.size == tools.size,
    "Tool definitions must have unique tool IDs."
  )
  require(
    toolsById.keySet == ToolId.values.toSet,
    "Tool definitions must cover all ToolId values exactly."
  )
  private[assistant] def toolDefinition(toolId: ToolId): Option[ToolDef] =
    toolsById.get(toolId)

  /** Write tool definitions into a JsonGenerator as the Anthropic tools array.
    */
  def writeToolsJson(g: JsonGenerator): Unit = {
    g.writeArrayFieldStart("tools")
    for (tool <- tools) {
      g.writeStartObject()
      g.writeStringField("name", tool.name)
      g.writeStringField("description", tool.description)
      g.writeObjectFieldStart("input_schema")
      g.writeStringField("type", "object")
      g.writeObjectFieldStart("properties")
      for (p <- tool.params) {
        g.writeObjectFieldStart(p.name)
        g.writeStringField("type", p.typ)
        g.writeStringField("description", p.description)
        // Add enum constraints for specific parameters
        if (tool.id == ToolId.EditTheory && p.name == "operation") {
          g.writeArrayFieldStart("enum")
          g.writeString("insert")
          g.writeString("replace")
          g.writeString("delete")
          g.writeEndArray()
        } else if (
          (tool.id == ToolId.GetErrors || tool.id == ToolId.GetWarnings) && p.name == "scope"
        ) {
          g.writeArrayFieldStart("enum")
          g.writeString("all")
          g.writeString("cursor")
          g.writeEndArray()
        }
        g.writeEndObject()
      }
      g.writeEndObject() // properties
      val req = tool.params.filter(_.required).map(_.name)
      if (req.nonEmpty) {
        g.writeArrayFieldStart("required")
        req.foreach(g.writeString)
        g.writeEndArray()
      }
      g.writeEndObject() // input_schema
      g.writeEndObject() // tool
    }
    g.writeEndArray()
  }

  /**
   * Write filtered tool definitions (excludes Deny-level tools).
   * Used when sending tools to the LLM to prevent it from seeing/using denied tools.
   */
  def writeFilteredToolsJson(g: JsonGenerator): Unit = {
    val visibleTools = ToolPermissions.getVisibleTools
    g.writeArrayFieldStart("tools")
    for (tool <- visibleTools) {
      g.writeStartObject()
      g.writeStringField("name", tool.name)
      g.writeStringField("description", tool.description)
      g.writeObjectFieldStart("input_schema")
      g.writeStringField("type", "object")
      g.writeObjectFieldStart("properties")
      for (p <- tool.params) {
        g.writeObjectFieldStart(p.name)
        g.writeStringField("type", p.typ)
        g.writeStringField("description", p.description)
        // Keep enum constraints aligned with writeToolsJson.
        if (tool.id == ToolId.EditTheory && p.name == "operation") {
          g.writeArrayFieldStart("enum")
          g.writeString("insert")
          g.writeString("replace")
          g.writeString("delete")
          g.writeEndArray()
        } else if (
          (tool.id == ToolId.GetErrors || tool.id == ToolId.GetWarnings) && p.name == "scope"
        ) {
          g.writeArrayFieldStart("enum")
          g.writeString("all")
          g.writeString("cursor")
          g.writeEndArray()
        }
        g.writeEndObject()
      }
      g.writeEndObject() // properties
      val req = tool.params.filter(_.required).map(_.name)
      if (req.nonEmpty) {
        g.writeArrayFieldStart("required")
        req.foreach(g.writeString)
        g.writeEndArray()
      }
      g.writeEndObject() // input_schema
      g.writeEndObject() // tool
    }
    g.writeEndArray()
  }

  /**
   * Write planning tool definitions (read-only exploration tools only).
   * Used by planning sub-agents to prevent write operations and recursion.
   */
  def writePlanningToolsJson(g: JsonGenerator): Unit = {
    val planningTools = tools.filter(t => ToolId.planningToolIds.contains(t.id))
    g.writeArrayFieldStart("tools")
    for (tool <- planningTools) {
      g.writeStartObject()
      g.writeStringField("name", tool.name)
      g.writeStringField("description", tool.description)
      g.writeObjectFieldStart("input_schema")
      g.writeStringField("type", "object")
      g.writeObjectFieldStart("properties")
      for (p <- tool.params) {
        g.writeObjectFieldStart(p.name)
        g.writeStringField("type", p.typ)
        g.writeStringField("description", p.description)
        if (tool.id == ToolId.EditTheory && p.name == "operation") {
          g.writeArrayFieldStart("enum")
          g.writeString("insert")
          g.writeString("replace")
          g.writeString("delete")
          g.writeEndArray()
        } else if (
          (tool.id == ToolId.GetErrors || tool.id == ToolId.GetWarnings) && p.name == "scope"
        ) {
          g.writeArrayFieldStart("enum")
          g.writeString("all")
          g.writeString("cursor")
          g.writeEndArray()
        }
        g.writeEndObject()
      }
      g.writeEndObject() // properties
      val req = tool.params.filter(_.required).map(_.name)
      if (req.nonEmpty) {
        g.writeArrayFieldStart("required")
        req.foreach(g.writeString)
        g.writeEndArray()
      }
      g.writeEndObject() // input_schema
      g.writeEndObject() // tool
    }
    g.writeEndArray()
  }

  /**
   * Execute a tool with permission checking.
   * Wraps executeTool with capability-based authorization.
   * Returns tool result or permission denial message.
   */
  sealed trait ToolExecResult {
    def toUserMessage: String
  }
  object ToolExecResult {
    case class Success(output: String) extends ToolExecResult {
      def toUserMessage: String = output
    }
    case class UnknownTool(name: String) extends ToolExecResult {
      def toUserMessage: String = s"Unknown tool: $name"
    }
    case class PermissionDenied(message: String) extends ToolExecResult {
      def toUserMessage: String = message
    }
    case class ExecutionFailure(toolId: ToolId, message: String)
        extends ToolExecResult {
      def toUserMessage: String = s"Tool error: $message"
    }
  }
  import ToolExecResult._

  private val toolHandlers: Map[ToolId, (ResponseParser.ToolArgs, View) => String] =
    Map(
      ToolId.ReadTheory -> ((a, _) => TheoryNavToolHandler.execReadTheory(a)),
      ToolId.ListTheories -> ((_, _) => TheoryNavToolHandler.execListTheories()),
      ToolId.SearchInTheory -> ((a, _) => TheoryNavToolHandler.execSearchInTheory(a)),
      ToolId.SearchTheories -> ((a, v) => TheoryNavToolHandler.execSearchTheories(a, v)),
      ToolId.GetGoalState -> ((_, v) => execGetGoalState(v)),
      ToolId.GetSubgoal -> ((a, v) => execGetSubgoal(a, v)),
      ToolId.GetProofContext -> ((_, v) => execGetProofContext(v)),
      ToolId.FindTheorems -> ((a, _) => execFindTheorems(a)),
      ToolId.VerifyProof -> ((a, _) => ProofOpsToolHandler.execVerifyProof(a)),
      ToolId.RunSledgehammer -> ((_, _) => ProofOpsToolHandler.execRunSledgehammer()),
      ToolId.RunNitpick -> ((_, _) => ProofOpsToolHandler.execRunNitpick()),
      ToolId.RunQuickcheck -> ((_, _) => ProofOpsToolHandler.execRunQuickcheck()),
      ToolId.FindCounterexample -> ((a, _) => ProofOpsToolHandler.execFindCounterexample(a)),
      ToolId.GetType -> ((_, v) => execGetType(v)),
      ToolId.GetCommandText -> ((_, v) => execGetCommandText(v)),
      ToolId.GetErrors -> ((a, v) => execGetErrors(a, v)),
      ToolId.GetDiagnostics -> ((a, v) => execGetDiagnostics(a, v)),
      ToolId.GetDefinitions -> ((a, v) => execGetDefinitions(a, v)),
      ToolId.GetFileStats -> ((a, _) => TheoryMetadataToolHandler.execGetFileStats(a)),
      ToolId.GetProcessingStatus -> ((a, _) => TheoryMetadataToolHandler.execGetProcessingStatus(a)),
      ToolId.GetSorryPositions -> ((a, _) => TheoryMetadataToolHandler.execGetSorryPositions(a)),
      ToolId.ExecuteStep -> ((a, _) => ProofOpsToolHandler.execExecuteStep(a)),
      ToolId.TraceSimplifier -> ((a, _) => ProofOpsToolHandler.execTraceSimplifier(a)),
      ToolId.GetProofBlock -> ((_, v) => execGetProofBlock(v)),
      ToolId.GetProofOutline -> ((_, v) => execGetProofOutline(v)),
      ToolId.GetContextInfo -> ((_, v) => execGetContextInfo(v)),
      ToolId.SearchAllTheories -> ((a, _) => TheoryNavToolHandler.execSearchAllTheories(a)),
      ToolId.GetDependencies -> ((a, _) => TheoryNavToolHandler.execGetDependencies(a)),
      ToolId.GetWarnings -> ((a, v) => execGetWarnings(a, v)),
      ToolId.SetCursorPosition -> ((a, v) => execSetCursorPosition(a, v)),
      ToolId.EditTheory -> ((a, _) => execEditTheory(a)),
      ToolId.TryMethods -> ((a, v) => execTryMethods(a, v)),
      ToolId.GetEntities -> ((a, _) => execGetEntities(a)),
      ToolId.WebSearch -> ((a, _) => WebSearchToolHandler.execWebSearch(a)),
      ToolId.CreateTheory -> ((a, v) => execCreateTheory(a, v)),
      ToolId.OpenTheory -> ((a, v) => execOpenTheory(a, v)),
      ToolId.AskUser -> ((a, v) => AskUserToolHandler.execAskUser(a, v)),
      ToolId.TaskListAdd -> ((a, v) => TaskListToolHandler.execTaskListAdd(a, v)),
      ToolId.TaskListDone -> ((a, v) => TaskListToolHandler.execTaskListDone(a, v)),
      ToolId.TaskListIrrelevant -> ((a, v) => TaskListToolHandler.execTaskListIrrelevant(a, v)),
      ToolId.TaskListNext -> ((_, v) => TaskListToolHandler.execTaskListNext(v)),
      ToolId.TaskListShow -> ((_, v) => TaskListToolHandler.execTaskListShow(v)),
      ToolId.TaskListGet -> ((a, v) => TaskListToolHandler.execTaskListGet(a, v)),
      ToolId.MemoryAdd -> ((a, v) => MemoryToolHandler.execMemoryAdd(a, v)),
      ToolId.MemoryDelete -> ((a, v) => MemoryToolHandler.execMemoryDelete(a, v)),
      ToolId.MemoryDeleteTopic -> ((a, v) => MemoryToolHandler.execMemoryDeleteTopic(a, v)),
      ToolId.MemoryListTopics -> ((_, v) => MemoryToolHandler.execMemoryListTopics(v)),
      ToolId.MemoryList -> ((a, v) => MemoryToolHandler.execMemoryList(a, v)),
      ToolId.MemoryGet -> ((a, v) => MemoryToolHandler.execMemoryGet(a, v)),
      ToolId.MemorySearch -> ((a, v) => MemoryToolHandler.execMemorySearch(a, v)),
      ToolId.PlanApproach -> ((a, v) => PlanApproachToolHandler.execPlanApproach(a, v))
    )

  def executeToolWithPermission(
      name: String,
      args: ResponseParser.ToolArgs,
      view: View
  ): String =
    executeToolWithPermissionResult(name, args, view).toUserMessage

  def executeToolWithPermissionResult(
      name: String,
      args: ResponseParser.ToolArgs,
      view: View
  ): ToolExecResult =
    ToolId.fromWire(name) match {
      case Some(toolId) => executeToolWithPermissionResult(toolId, args, view)
      case None         => UnknownTool(name)
    }

  private def executeToolWithPermissionResult(
      toolId: ToolId,
      args: ResponseParser.ToolArgs,
      view: View
  ): ToolExecResult = {
    ToolPermissions.checkPermission(toolId, args) match {
      case ToolPermissions.Allowed =>
        executeToolResult(toolId, args, view)
      case ToolPermissions.Denied =>
        val name = toolId.wireName
        safeLog(s"[Permissions] Tool '$name' denied by policy")
        PermissionDenied(s"Permission denied: tool '$name' is not allowed.")
      case ToolPermissions.NeedPrompt(promptToolId, resource, details) =>
        val toolName = promptToolId.wireName
        ToolPermissions.promptUser(promptToolId, resource, details, view) match {
          case ToolPermissions.Allowed =>
            executeToolResult(toolId, args, view)
          case ToolPermissions.Denied =>
            safeLog(s"[Permissions] User denied tool '$toolName'")
            PermissionDenied(
              s"Permission denied: user declined tool '$toolName'."
            )
          case _ =>
            safeLog(s"[Permissions] Unexpected decision for tool '$toolName'")
            PermissionDenied(s"Permission denied: tool '$toolName'.")
        }
    }
  }

  private[assistant] def isValidCreateTheoryName(name: String): Boolean =
    ToolArgs.isValidCreateTheoryName(name)

  private[assistant] def normalizeReadRange(
      totalLines: Int,
      requestedStart: Int,
      requestedEnd: Int
  ): (Int, Int) = ToolArgs.normalizeReadRange(totalLines, requestedStart, requestedEnd)

  private[assistant] def clampOffset(offset: Int, bufferLength: Int): Int =
    ToolArgs.clampOffset(offset, bufferLength)

  /** Format the user-facing string for a create_theory outcome.
    *
    * Distinguishes five cases by the `(created, opened, tracked)` tuple
    * returned by the I/Q open_file handler:
    *
    *   - (true, true, true)    — happy path: created + opened + tracked
    *   - (true, true, false)   — created and opened, waiting for PIDE to track
    *   - (true, false, _)      — created on disk but not opened in jEdit
    *   - (false, true, _)      — file already existed, opened without rewrite
    *   - (false, false, _)     — create failed (e.g. mutation-roots denial)
    */
  private[assistant] def formatCreateTheoryResult(
      name: String,
      normalizedDir: String,
      result: IQMcpProtocol.OpenFileResult
  ): String = {
    val detail = if (result.message.nonEmpty) s" (${result.message})" else ""
    if (result.created && result.opened && result.tracked)
      s"Created and opened $name.thy"
    else if (result.created && result.opened)
      s"Error: $name.thy was created but is not yet tracked by Isabelle; retry shortly$detail"
    else if (result.created)
      s"Error: $name.thy was created but not opened in jEdit$detail"
    else if (result.opened)
      s"Note: $name.thy already exists in $normalizedDir and was opened without modification$detail"
    else
      s"Error: $name.thy could not be created or opened$detail"
  }

  private def selectionArgsForCurrentView(view: View): Map[String, Any] =
    ToolHelpers
      .snapshotViewState(view)
      .flatMap(snapshot =>
        snapshot.path.map(path =>
          Map(
            "command_selection" -> "file_offset",
            "path" -> path,
            "offset" -> clampOffset(snapshot.caretOffset, snapshot.bufferLength)
          )
        )
      )
      .getOrElse(Map("command_selection" -> "current"))

  private def formatDiagnosticsMessages(
      diagnostics: IQMcpClient.DiagnosticsResult,
      emptyMessage: String
  ): String = {
    if (diagnostics.diagnostics.isEmpty) emptyMessage
    else
      diagnostics.diagnostics
        .map { d =>
          if (d.line > 0) s"Line ${d.line}: ${d.message}" else d.message
        }
        .distinct
        .mkString("\n")
  }

  private def summarizeToolArgsForLog(args: ResponseParser.ToolArgs): String =
    args.map { case (k, v) =>
      if (ToolArgs.isSensitiveArgName(k)) "***=***"
      else {
        val rendered =
          ResponseParser.toolValueToDisplay(v).replace('\n', ' ').take(100)
        s"$k=$rendered"
      }
    }.mkString(", ")

  private def safeLog(message: String): Unit = {
    try Output.writeln(message)
    catch {
      case NonFatal(_) | _: LinkageError => ()
    }
  }

  /** Execute a tool by name. Returns the result as a string. Called from the
    * agentic loop on a background thread. All arguments are sanitized before
    * use to prevent injection or resource exhaustion.
    */
  def executeTool(
      name: String,
      args: ResponseParser.ToolArgs,
      view: View
  ): String =
    executeToolResult(name, args, view).toUserMessage

  def executeToolResult(
      name: String,
      args: ResponseParser.ToolArgs,
      view: View
  ): ToolExecResult =
    ToolId.fromWire(name) match {
      case Some(toolId) => executeToolResult(toolId, args, view)
      case None         => UnknownTool(name)
    }

  private def executeToolResult(
      toolId: ToolId,
      args: ResponseParser.ToolArgs,
      view: View
  ): ToolExecResult = {
    val toolName = toolId.wireName
    safeLog(s"[Assistant] Tool call: $toolName(${summarizeToolArgsForLog(args)})")
    AssistantDockable.setStatus(s"[tool] $toolName…")
    try {
      toolHandlers.get(toolId) match {
        case Some(handler) => Success(handler(args, view))
        case None =>
          ExecutionFailure(
            toolId,
            s"No execution handler registered for tool '$toolName'"
          )
      }
    } catch {
      case ex: Exception => ExecutionFailure(toolId, ex.getMessage)
    }
  }

  private def getGoalStateResult(view: View): ToolResult = {
    if (!IQAvailable.isAvailable) ToolResult.Unavailable(AssistantConstants.TOOL_IQ_UNAVAILABLE)
    else
      IQMcpClient
        .callGetContextInfo(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = ToolHelpers.readToolsTimeoutMs
        )
        .fold(
          err => ToolResult.Err(err),
          ctx =>
            if (ctx.goal.hasGoal && ctx.goal.goalText.trim.nonEmpty)
              ToolResult.Ok(ctx.goal.goalText.trim)
            else ToolResult.Ok(AssistantConstants.UIText.NO_GOAL_AT_CURSOR)
        )
  }

  private def execGetGoalState(view: View): String =
    getGoalStateResult(view).render

  private def execGetProofContext(view: View): String = {
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else
      IQMcpClient
        .callGetProofContext(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = ToolHelpers.readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          ctx => {
            if (ctx.success && ctx.hasContext && ctx.context.trim.nonEmpty)
              ctx.context.trim
            else if (ctx.timedOut) "Proof context lookup timed out."
            else if (ctx.message.trim.nonEmpty) ctx.message.trim
            else "No local facts in scope."
          }
        )
  }

  private def execFindTheorems(args: ResponseParser.ToolArgs): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      val max = math.min(
        AssistantConstants.MAX_FIND_THEOREMS_RESULTS,
        math.max(1, intArg(args, "max_results", 20))
      )
      val timeout = AssistantOptions.getFindTheoremsTimeout
      val quoted =
        if (pattern.startsWith("\"")) pattern else s"\"$pattern\""

      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.FindTheorems,
          arguments = quoted,
          timeoutMs = timeout,
          extraParams = Map("max_results" -> max)
        )
        .fold(
          mcpErr => s"Error: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty && text != "No results") text
              else s"No theorems found for: $pattern"
            } else if (explore.timedOut) "find_theorems timed out."
            else
              s"Error: ${ProofOpsToolHandler.exploreFailureMessage(explore, "find_theorems failed")}"
          }
        )
    }
  }

  private def execGetType(view: View): String = {
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else
      IQMcpClient
        .callGetTypeAtSelection(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = ToolHelpers.readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          t =>
            if (t.hasType && t.typeText.trim.nonEmpty) t.typeText.trim
            else t.message.filter(_.trim.nonEmpty).getOrElse(
              "No type information at cursor position."
            )
        )
  }

  private def execGetCommandText(view: View): String = {
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else
      IQMcpClient
        .callResolveCommandTarget(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = ToolHelpers.readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          resolved =>
            Option(resolved.command.source)
              .map(_.trim)
              .filter(_.nonEmpty)
              .getOrElse(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
        )
  }

  private def execGetErrors(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val timeoutMs = ToolHelpers.readToolsTimeoutMs

    val rawScope = safeStringArg(args, "scope", 200)
    val effectiveScope = if (rawScope.isEmpty) "all" else rawScope

    effectiveScope.toLowerCase match {
      case "cursor" =>
        IQMcpClient
          .callGetDiagnostics(
            severity = IQMcpClient.DiagnosticSeverity.Error,
            scope = IQMcpClient.DiagnosticScope.Selection,
            timeoutMs = timeoutMs,
            selectionArgs = selectionArgsForCurrentView(view)
          )
          .fold(
            err => s"Error: $err",
            diagnostics =>
              formatDiagnosticsMessages(diagnostics, AssistantConstants.UIText.NO_ERROR_AT_CURSOR)
          )

      case "all" =>
        ToolHelpers.currentBufferPath(view).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetDiagnostics(
                severity = IQMcpClient.DiagnosticSeverity.Error,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                diagnostics =>
                  formatDiagnosticsMessages(
                    diagnostics,
                    "No errors in current buffer."
                  )
              )
        )

      case _ =>
        ToolHelpers.resolveTheoryPath(effectiveScope).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetDiagnostics(
                severity = IQMcpClient.DiagnosticSeverity.Error,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                diagnostics =>
                  formatDiagnosticsMessages(
                    diagnostics,
                    s"No errors in theory '$effectiveScope'."
                  )
              )
        )
    }
  }

  private def execGetDefinitions(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val names = safeStringArg(args, "names", MAX_STRING_ARG_LENGTH)
    if (names.isEmpty) "Error: names required"
    else if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      val nameList = names.split("\\s+").toList.filter(_.nonEmpty)
      if (nameList.isEmpty) "Error: no valid names provided"
      else {
        val latch = new CountDownLatch(1)
        @volatile var result =
          s"No definitions found for: ${nameList.mkString(", ")}"

        IQIntegration.getDefinitionsAsync(
          view,
          nameList,
          AssistantConstants.CONTEXT_FETCH_TIMEOUT,
          {
            case Right(defs)
                if defs.success &&
                  defs.hasDefinitions &&
                  defs.definitions.trim.nonEmpty =>
              result = defs.definitions.trim
              latch.countDown()
            case Right(defs) if defs.timedOut =>
              result = "Definition lookup timed out."
              latch.countDown()
            case Right(defs) =>
              val msg = defs.error.getOrElse(defs.message).trim
              if (msg.nonEmpty) {
                result = s"Error: $msg"
              }
              latch.countDown()
            case Left(err) =>
              result = s"Error: $err"
              latch.countDown()
          }
        )

        if (
          !latch.await(
            AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC +
              AssistantConstants.CONTEXT_FETCH_TIMEOUT / 1000 + 2,
            TimeUnit.SECONDS
          )
        ) "Error: definition lookup timed out"
        else result
      }
    }
  }

  private def execGetProofBlock(view: View): String = {
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else
      IQMcpClient
        .callGetProofBlocksForSelection(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = ToolHelpers.readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          blocks =>
            blocks.proofBlocks.headOption
              .map(_.proofText.trim)
              .filter(_.nonEmpty)
              .getOrElse(
                blocks.message.getOrElse(AssistantConstants.UIText.NO_PROOF_BLOCK_AT_CURSOR)
              )
        )
  }

  private def execGetContextInfo(view: View): String = {
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else
      IQMcpClient
        .callGetContextInfo(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = ToolHelpers.readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          ctx => {
            val commandKeyword = Option(ctx.command.keyword).getOrElse("").trim
            val definitionKeywords = Set(
              "definition",
              "abbreviation",
              "fun",
              "function",
              "primrec",
              "datatype",
              "codatatype",
              "type_synonym",
              "record",
              "typedef"
            )
            val hasSelection =
              Option(view)
                .flatMap(v => Option(v.getTextArea))
                .flatMap(ta => Option(ta.getSelectedText))
                .exists(_.trim.nonEmpty)
            val parts = List(
              s"in_proof: ${ctx.inProofContext}",
              s"has_goal: ${ctx.hasGoal || ctx.goal.hasGoal}",
              s"on_error: false",
              s"on_warning: false",
              s"has_selection: $hasSelection",
              s"has_command: ${ctx.command.source.trim.nonEmpty}",
              s"has_type_info: false",
              s"has_apply_proof: false",
              s"on_definition: ${definitionKeywords.contains(commandKeyword)}",
              "iq_available: true"
            )
            parts.mkString("\n")
          }
        )
  }

  private def execGetWarnings(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val timeoutMs = ToolHelpers.readToolsTimeoutMs

    val rawScope = safeStringArg(args, "scope", 200)
    val effectiveScope = if (rawScope.isEmpty) "all" else rawScope

    effectiveScope.toLowerCase match {
      case "cursor" =>
        IQMcpClient
          .callGetDiagnostics(
            severity = IQMcpClient.DiagnosticSeverity.Warning,
            scope = IQMcpClient.DiagnosticScope.Selection,
            timeoutMs = timeoutMs,
            selectionArgs = selectionArgsForCurrentView(view)
          )
          .fold(
            err => s"Error: $err",
            diagnostics =>
              formatDiagnosticsMessages(
                diagnostics,
                "No warnings at cursor position."
              )
          )

      case "all" =>
        ToolHelpers.currentBufferPath(view).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetDiagnostics(
                severity = IQMcpClient.DiagnosticSeverity.Warning,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                diagnostics =>
                  formatDiagnosticsMessages(
                    diagnostics,
                    "No warnings in current buffer."
                  )
              )
        )

      case _ =>
        ToolHelpers.resolveTheoryPath(effectiveScope).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetDiagnostics(
                severity = IQMcpClient.DiagnosticSeverity.Warning,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                diagnostics =>
                  formatDiagnosticsMessages(
                    diagnostics,
                    s"No warnings in theory '$effectiveScope'."
                  )
              )
        )
    }
  }

  private def execSetCursorPosition(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val line = intArg(args, "line", -1)
    if (line <= 0) "Error: line must be a positive integer"
    else {
      val latch = new CountDownLatch(1)
      @volatile var result = ""
      GUI_Thread.later {
        try {
          val buffer = view.getBuffer
          val lineCount = buffer.getLineCount
          if (line > lineCount) {
            result =
              s"Error: line $line out of range (theory has $lineCount lines)"
          } else {
            val offset = buffer.getLineStartOffset(line - 1)
            view.getTextArea.setCaretPosition(offset)
            result = s"Cursor moved to line $line"
          }
        } catch { case ex: Exception => result = s"Error: ${ex.getMessage}" }
        latch.countDown()
      }
      if (!latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)) {
        "Error: Operation timed out (GUI thread busy)"
      } else if (result.isEmpty) {
        "Error: Operation completed but returned no result"
      } else {
        result
      }
    }
  }

  private def execEditTheory(args: ResponseParser.ToolArgs): String = {
    val operation = safeStringArg(args, "operation", 50).toLowerCase
    val text =
      safeStringArg(args, "text", MAX_STRING_ARG_LENGTH, trim = false).replace(
        "\\n",
        "\n"
      )
    val startLine = intArg(args, "start_line", -1)
    val endLine = intArg(args, "end_line", startLine)

    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        if (startLine <= 0) "Error: start_line must be a positive integer"
        else if (operation == "replace" && endLine < startLine)
          s"Error: end_line ($endLine) must be >= start_line ($startLine)"
        else if (operation == "delete" && endLine < startLine)
          s"Error: end_line ($endLine) must be >= start_line ($startLine)"
        else if (!Set("insert", "replace", "delete").contains(operation))
          s"Error: operation must be 'insert', 'replace', or 'delete', got '$operation'"
        else if (
          (operation == "insert" || operation == "replace") && text.isEmpty
        )
          s"Error: text required for $operation operation"
        else {
          ToolHelpers.resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient
                .callReadFileLine(
                  path = path,
                  startLine = Some(1),
                  endLine = Some(-1),
                  timeoutMs = ToolHelpers.readToolsTimeoutMs
                )
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  numberedContent => {
                    val lineCount = ToolHelpers.lineCountFromNumberedContent(numberedContent)
                    val canAppendAtEnd = operation == "insert" && startLine == lineCount + 1
                    if (startLine > lineCount && !canAppendAtEnd)
                      s"Error: start_line $startLine out of range (theory has $lineCount lines)"
                    else if (
                      (operation == "replace" || operation == "delete") && endLine > lineCount
                    )
                      s"Error: end_line $endLine out of range (theory has $lineCount lines)"
                    else {
                      val writeResult = operation match {
                        case "insert" =>
                          val normalizedText =
                            if (text.endsWith("\n")) text else text + "\n"
                          IQMcpClient.callWriteFileInsert(
                            path = path,
                            insertAfterLine = math.max(0, startLine - 1),
                            newText = normalizedText,
                            timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
                          )
                        case "replace" =>
                          IQMcpClient.callWriteFileLine(
                            path = path,
                            startLine = startLine,
                            endLine = endLine,
                            newText = text,
                            timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
                          )
                        case "delete" =>
                          IQMcpClient.callWriteFileLine(
                            path = path,
                            startLine = startLine,
                            endLine = endLine,
                            newText = "",
                            timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
                          )
                      }

                      writeResult.fold(
                        err => s"Error: $err",
                        _ => {
                          // Invalidate any cached verification outcomes for
                          // this theory — their command IDs / sources may now
                          // be stale. See VerificationCache.invalidateNode.
                          val _ = VerificationCache.invalidateNode(path)
                          val contextStart = math.max(1, startLine - 3)
                          val contextEnd = math.max(contextStart, startLine + 5)
                          val context = IQMcpClient
                            .callReadFileLine(
                              path = path,
                              startLine = Some(contextStart),
                              endLine = Some(contextEnd),
                              timeoutMs = ToolHelpers.readToolsTimeoutMs
                            )
                            .getOrElse("")
                          val action = operation match {
                            case "insert"  => s"Inserted ${text.linesIterator.size} lines before line $startLine"
                            case "replace" => s"Replaced lines $startLine-$endLine"
                            case "delete"  => s"Deleted lines $startLine-$endLine"
                          }
                          if (context.trim.isEmpty) action
                          else s"$action\n\nContext:\n$context"
                        }
                      )
                    }
                  }
                )
          )
        }
    }
  }

  private def execTryMethods(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val methodsStr = safeStringArg(args, "methods", MAX_STRING_ARG_LENGTH)
    if (methodsStr.isEmpty) "Error: methods required"
    else if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      val methods = methodsStr.split(",").map(_.trim).filter(_.nonEmpty).toList
      if (methods.isEmpty) "Error: no valid methods provided"
      else {
        val results = scala.collection.mutable.ListBuffer[String]()
        for (method <- methods) {
          val timeout = AssistantOptions.getVerificationTimeout
          val latch = new CountDownLatch(1)
          @volatile var methodResult = ""
          IQIntegration.verifyProofAsync(
            view,
            method,
            timeout,
            {
              case IQIntegration.ProofSuccess(ms, _) =>
                methodResult = s"[ok] $method (${ms}ms)"
                latch.countDown()
              case IQIntegration.ProofFailure(err) =>
                methodResult = s"[FAIL] $method: ${err.take(50)}"
                latch.countDown()
              case IQIntegration.ProofTimeout =>
                methodResult = s"[TIMEOUT] $method"
                latch.countDown()
              case _ =>
                methodResult = s"[UNAVAILABLE] $method"
                latch.countDown()
            }
          )
          if (!latch.await(timeout + 2000, TimeUnit.MILLISECONDS))
            results += s"[TIMEOUT] $method"
          else if (methodResult.isEmpty)
            results += s"[ERROR] $method returned no result"
          else results += methodResult
        }
        s"Tried ${methods.length} methods:\n${results.mkString("\n")}"
      }
    }
  }

  private def execGetEntities(args: ResponseParser.ToolArgs): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        val maxResultsRaw = intArg(args, "max_results", 200)
        val maxResults = math.max(1, math.min(1000, maxResultsRaw))
        ToolHelpers.resolveTheoryPath(theory).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetEntities(
                path = path,
                maxResults = Some(maxResults),
                timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                entitiesResult => {
                  if (entitiesResult.entities.isEmpty)
                    "No entities found in theory."
                  else {
                    val lines = entitiesResult.entities.map { entity =>
                      s"Line ${entity.line}: ${entity.keyword} ${entity.name}"
                    }
                    val suffix =
                      if (entitiesResult.truncated)
                        s"\n\nResults truncated to ${entitiesResult.returnedEntities} of ${entitiesResult.totalEntities} entities."
                      else ""
                    lines.mkString("\n") + suffix
                  }
                }
              )
        )
    }
  }

  private def execCreateTheory(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val name = safeStringArg(args, "name", 200)
    val imports = safeStringArg(args, "imports", 500)
    val content =
      safeStringArg(args, "content", MAX_STRING_ARG_LENGTH, trim = false)
        .replace("\\n", "\n")

    if (name.isEmpty) "Error: name required"
    else if (!isValidCreateTheoryName(name))
      s"Error: invalid theory name '${describeTheoryName(name)}'"
    else {
      ToolHelpers.currentBufferPath(view).fold(
        err => err,
        currentPath => {
          val currentDir = java.nio.file.Paths.get(currentPath).getParent
          if (currentDir == null) "Error: could not determine current theory directory"
          else {
            val normalizedDir = currentDir.toAbsolutePath.normalize()
            val targetPath = normalizedDir.resolve(s"$name.thy").normalize()

            val effectiveImports = if (imports.isEmpty) "Main" else imports
            val theoryContent =
              s"theory $name\n  imports $effectiveImports\nbegin\n\n${
                  if (content.nonEmpty) content + "\n\n" else ""
                }end\n"

            // Defence-in-depth: isValidCreateTheoryName already rejects any
            // name containing a path separator, but compare the *real* paths
            // so that symlinks or case-folded filesystems cannot conceal an
            // escape from the buffer directory.
            val realDir =
              try normalizedDir.toRealPath()
              catch { case _: java.io.IOException => normalizedDir }
            val realParent =
              try targetPath.getParent.toRealPath()
              catch { case _: java.io.IOException => targetPath.getParent }

            if (realParent != realDir)
              s"Error: invalid theory name '${describeTheoryName(name)}'"
            else {
              // Pass the real-parent-resolved path (not the pre-canonical
              // targetPath) to the server: a dangling relative symlink in
              // the parent directory could otherwise redirect the write
              // after the containment check.
              val realTargetPath = realParent.resolve(s"$name.thy")
              IQMcpClient
                .callOpenFile(
                  path = realTargetPath.toString,
                  createIfMissing = true,
                  inView = true,
                  content = Some(theoryContent),
                  overwriteIfExists = false,
                  timeoutMs = AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC * 1000L
                )
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  result => formatCreateTheoryResult(name, normalizedDir.toString, result)
                )
            }
          }
        }
      )
    }
  }

  private def execOpenTheory(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val path = safeStringArg(args, "path", 1000)
    if (path.isEmpty) "Error: path required"
    else {
      if (!path.endsWith(".thy")) {
        s"Error: not a theory file (must end with .thy): $path"
      } else {
        val resolvedPath = {
          val file = java.io.File(path)
          if (file.isAbsolute) file.getPath
          else
            ToolHelpers.currentBufferPath(view).fold(_ => path, current =>
              java.nio.file.Paths
                .get(current)
                .getParent
                .resolve(path)
                .normalize()
                .toString
            )
        }
        IQMcpClient
          .callOpenFile(
            path = resolvedPath,
            createIfMissing = false,
            inView = true,
            timeoutMs = AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC * 1000L
          )
          .fold(
            err => s"Error: $err",
            result => {
              val detail = if (result.message.nonEmpty) s" (${result.message})" else ""
              val fileName = ToolHelpers.baseName(result.path)
              if (!result.opened) s"Error: $fileName failed to open in jEdit$detail"
              else if (!result.tracked) s"Error: $fileName was opened but is not yet tracked by Isabelle; retry shortly$detail"
              else s"Opened $fileName"
            }
          )
      }
    }
  }

  /** Forwarder to AskUserToolHandler.promptUserWithChoices.
    * Kept so ToolPermissions can reach the prompt through the AssistantTools
    * surface without importing the handler directly.
    */
  private[assistant] def promptUserWithChoices(
      question: String,
      options: List[String],
      context: String,
      view: View
  ): Option[String] =
    AskUserToolHandler.promptUserWithChoices(question, options, context, view)



  private def execGetSubgoal(args: ResponseParser.ToolArgs, view: View): String = {
    val index = intArg(args, "index", -1)
    if (index <= 0) "Error: index must be a positive integer"
    else
      getGoalStateResult(view) match {
        case ToolResult.Err(_) | ToolResult.Unavailable(_) =>
          // Propagate the underlying error verbatim rather than reparsing
          // its string form.
          getGoalStateResult(view).render
        case ToolResult.Ok(goalState) =>
          if (goalState == AssistantConstants.UIText.NO_GOAL_AT_CURSOR) goalState
          else {
            val subgoalPattern = s"""(?s)subgoal\\s+$index(?::|\\s|\\n)(.+?)(?=\\n\\s*(?:subgoal|using|proof|qed|done|by)|\\z)""".r
            subgoalPattern.findFirstMatchIn(goalState) match {
              case Some(m) => m.group(1).trim
              case None    => s"Subgoal $index not found in current proof state."
            }
          }
      }
  }

  private def execGetDiagnostics(args: ResponseParser.ToolArgs, view: View): String = {
    val severity = safeStringArg(args, "severity", 50).toLowerCase
    val scope = safeStringArg(args, "scope", 200)
    val countOnly = args.get("count_only").exists {
      case ResponseParser.BooleanValue(b) => b
      case ResponseParser.StringValue(s) => s.toLowerCase == "true"
      case _ => false
    }
    
    if (severity.isEmpty) "Error: severity required"
    else {
      val modifiedArgs = args + ("scope" -> ResponseParser.StringValue(if (scope.isEmpty) "all" else scope))
      val result = severity match {
        case "error" => execGetErrors(modifiedArgs, view)
        case "warning" => execGetWarnings(modifiedArgs, view)
        case "all" =>
          val errors = execGetErrors(modifiedArgs, view)
          val warnings = execGetWarnings(modifiedArgs, view)
          s"ERRORS:\n$errors\n\nWARNINGS:\n$warnings"
        case _ => s"Error: invalid severity '$severity', must be 'error', 'warning', or 'all'"
      }
      
      if (countOnly) {
        val errorCount = if (severity == "error" || severity == "all") result.linesIterator.count(_.startsWith("Line ")) else 0
        val warningCount = if (severity == "warning" || severity == "all") result.linesIterator.count(_.startsWith("Line ")) else 0
        s"Errors: $errorCount, Warnings: $warningCount"
      } else result
    }
  }

  private def execGetProofOutline(view: View): String = {
    if (!IQAvailable.isAvailable) AssistantConstants.TOOL_IQ_UNAVAILABLE
    else {
      IQMcpClient.callGetProofBlocksForSelection(
        selectionArgs = selectionArgsForCurrentView(view),
        timeoutMs = ToolHelpers.readToolsTimeoutMs
      ).fold(
        err => s"Error: $err",
        blocks =>
          blocks.proofBlocks.headOption match {
            case Some(block) =>
              val keywords = block.proofText.linesIterator.filter { line =>
                val trimmed = line.trim
                trimmed.startsWith("lemma") || trimmed.startsWith("theorem") ||
                trimmed.startsWith("proof") || trimmed.startsWith("qed") ||
                trimmed.startsWith("done") || trimmed.startsWith("next") ||
                trimmed.startsWith("show") || trimmed.startsWith("have")
              }.mkString("\n")
              if (keywords.nonEmpty) keywords else "No structural keywords found in proof block."
            case None => blocks.message.getOrElse(AssistantConstants.UIText.NO_PROOF_BLOCK_AT_CURSOR)
          }
      )
    }
  }

}
