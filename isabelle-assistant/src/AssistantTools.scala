/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import java.util.concurrent.{CountDownLatch, TimeUnit}
import java.util.Locale
import scala.annotation.unused
import scala.util.control.NonFatal
import software.amazon.awssdk.thirdparty.jackson.core.JsonGenerator

/** Tool definitions and execution for LLM tool use (Anthropic function
  * calling). Tools give the LLM autonomous access to theory files, goal state,
  * and Isabelle queries.
  */
object AssistantTools {

  case class ToolParam(
      name: String,
      typ: String,
      description: String,
      required: Boolean = false
  )
  case class ToolDef private (
      id: ToolId,
      description: String,
      params: List[ToolParam]
  ) {
    val name: String = id.wireName
  }
  object ToolDef {
    def apply(id: ToolId, description: String, params: List[ToolParam]): ToolDef =
      new ToolDef(id, description, params)

    def apply(name: String, description: String, params: List[ToolParam]): ToolDef =
      ToolId
        .fromWire(name)
        .map(id => new ToolDef(id, description, params))
        .getOrElse(
          throw new IllegalArgumentException(s"Unknown tool name in definition: $name")
        )
  }

  val tools: List[ToolDef] = List(
    ToolDef(
      "read_theory",
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
      "list_theories",
      "List all currently open Isabelle theory files.",
      Nil
    ),
    ToolDef(
      "search_in_theory",
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
      "get_goal_state",
      "Get the current proof goal state at the cursor position. Returns the goal or empty if not in a proof.",
      Nil
    ),
    ToolDef(
      "get_proof_context",
      "Get local facts and assumptions in scope at the cursor position.",
      Nil
    ),
    ToolDef(
      "find_theorems",
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
      "verify_proof",
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
      "run_sledgehammer",
      "Run Sledgehammer to find proofs using external ATP provers. Returns found proof methods. Requires I/Q plugin.",
      Nil
    ),
    ToolDef(
      "run_nitpick",
      "Run Nitpick model finder to search for counterexamples to the current goal. Returns counterexample if found. Requires I/Q plugin.",
      Nil
    ),
    ToolDef(
      "run_quickcheck",
      "Run QuickCheck to test the current goal with random examples. Returns counterexample if found. Requires I/Q plugin.",
      Nil
    ),
    ToolDef(
      "get_type",
      "Get type information for the term at the cursor position. Returns the term and its type.",
      Nil
    ),
    ToolDef(
      "get_command_text",
      "Get the source text of the Isabelle command at the cursor position.",
      Nil
    ),
    ToolDef(
      "get_errors",
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
      "get_definitions",
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
      "execute_step",
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
      "trace_simplifier",
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
      "get_proof_block",
      "Get the full proof block (lemma/theorem...qed/done) at the cursor position. Returns the complete proof text including the statement.",
      Nil
    ),
    ToolDef(
      "get_context_info",
      "Get structured context information at cursor: whether in a proof, whether there's a goal, whether on an error, etc. Returns a summary of the cursor context.",
      Nil
    ),
    ToolDef(
      "search_all_theories",
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
      "get_dependencies",
      "Get the import dependencies for a specific theory file. Returns the list of imported theories.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      "get_warnings",
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
      "set_cursor_position",
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
      "edit_theory",
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
      "try_methods",
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
      "get_entities",
      "List all named entities (lemmas, definitions, datatypes, etc.) in a theory file with their line numbers. Returns a structured listing of the theory's contents.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      "web_search",
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
      "create_theory",
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
      "open_theory",
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
      "ask_user",
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
      "task_list_add",
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
      "task_list_done",
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
      "task_list_irrelevant",
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
      "task_list_next",
      "Get the next pending task to work on. Returns the first task in the list that has not been completed or marked irrelevant.",
      Nil
    ),
    ToolDef(
      "task_list_show",
      "Show all tasks in the task list with their current statuses. Displays a visual overview of progress.",
      Nil
    ),
    ToolDef(
      "task_list_get",
      "Get detailed information about a specific task, including its full description and acceptance criteria.",
      List(
        ToolParam(
          "task_id",
          "integer",
          "The ID of the task to retrieve details for",
          required = true
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
      ToolId.ReadTheory -> ((a, v) => execReadTheory(a, v)),
      ToolId.ListTheories -> ((_, _) => execListTheories()),
      ToolId.SearchInTheory -> ((a, v) => execSearchInTheory(a, v)),
      ToolId.GetGoalState -> ((_, v) => execGetGoalState(v)),
      ToolId.GetProofContext -> ((_, v) => execGetProofContext(v)),
      ToolId.FindTheorems -> ((a, v) => execFindTheorems(a, v)),
      ToolId.VerifyProof -> ((a, v) => execVerifyProof(a, v)),
      ToolId.RunSledgehammer -> ((_, v) => execRunSledgehammer(v)),
      ToolId.RunNitpick -> ((_, v) => execRunNitpick(v)),
      ToolId.RunQuickcheck -> ((_, v) => execRunQuickcheck(v)),
      ToolId.GetType -> ((_, v) => execGetType(v)),
      ToolId.GetCommandText -> ((_, v) => execGetCommandText(v)),
      ToolId.GetErrors -> ((a, v) => execGetErrors(a, v)),
      ToolId.GetDefinitions -> ((a, v) => execGetDefinitions(a, v)),
      ToolId.ExecuteStep -> ((a, v) => execExecuteStep(a, v)),
      ToolId.TraceSimplifier -> ((a, v) => execTraceSimplifier(a, v)),
      ToolId.GetProofBlock -> ((_, v) => execGetProofBlock(v)),
      ToolId.GetContextInfo -> ((_, v) => execGetContextInfo(v)),
      ToolId.SearchAllTheories -> ((a, v) => execSearchAllTheories(a, v)),
      ToolId.GetDependencies -> ((a, v) => execGetDependencies(a, v)),
      ToolId.GetWarnings -> ((a, v) => execGetWarnings(a, v)),
      ToolId.SetCursorPosition -> ((a, v) => execSetCursorPosition(a, v)),
      ToolId.EditTheory -> ((a, v) => execEditTheory(a, v)),
      ToolId.TryMethods -> ((a, v) => execTryMethods(a, v)),
      ToolId.GetEntities -> ((a, v) => execGetEntities(a, v)),
      ToolId.WebSearch -> ((a, _) => execWebSearch(a)),
      ToolId.CreateTheory -> ((a, v) => execCreateTheory(a, v)),
      ToolId.OpenTheory -> ((a, v) => execOpenTheory(a, v)),
      ToolId.AskUser -> ((a, v) => execAskUser(a, v)),
      ToolId.TaskListAdd -> ((a, v) => execTaskListAdd(a, v)),
      ToolId.TaskListDone -> ((a, v) => execTaskListDone(a, v)),
      ToolId.TaskListIrrelevant -> ((a, v) => execTaskListIrrelevant(a, v)),
      ToolId.TaskListNext -> ((_, v) => execTaskListNext(v)),
      ToolId.TaskListShow -> ((_, v) => execTaskListShow(v)),
      ToolId.TaskListGet -> ((a, v) => execTaskListGet(a, v))
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

  /** Maximum length for string arguments from LLM tool calls. */
  private val MAX_STRING_ARG_LENGTH = 10000

  /** Maximum length for proof text arguments. */
  private val MAX_PROOF_ARG_LENGTH = 5000

  /** Maximum length for search pattern arguments. */
  private val MAX_PATTERN_ARG_LENGTH = 500

  private val sensitiveArgTokens =
    Set("token", "secret", "password", "auth", "credential", "api_key")

  /** Valid theory reference pattern (for referring to already-open theories). */
  private val THEORY_REFERENCE_PATTERN = """^[A-Za-z0-9_.\-/]+$""".r

  /** Valid new theory file name (single file name, no path separators). */
  private val CREATE_THEORY_NAME_PATTERN = """^[A-Za-z][A-Za-z0-9_']*$""".r

  /** Sanitize a string argument: trim, limit length, reject control characters.
    */
  private def safeStringArg(
      args: ResponseParser.ToolArgs,
      key: String,
      maxLen: Int = MAX_STRING_ARG_LENGTH,
      trim: Boolean = true
  ): String = {
    val raw = args.get(key).map(ResponseParser.toolValueToString).getOrElse("")
    val cleaned = raw.filter(c => !c.isControl || c == '\n' || c == '\t')
    val limited = cleaned.take(maxLen)
    if (trim) limited.trim else limited
  }

  /** Validate a theory name argument. */
  private def safeTheoryArg(
      args: ResponseParser.ToolArgs
  ): Either[String, String] = {
    val name = safeStringArg(args, "theory", 200)
    if (name.isEmpty) Left("Error: theory name required")
    else if (THEORY_REFERENCE_PATTERN.findFirstIn(name).isEmpty)
      Left(s"Error: invalid theory name '$name'")
    else Right(name)
  }

  private[assistant] def isValidCreateTheoryName(name: String): Boolean =
    CREATE_THEORY_NAME_PATTERN.findFirstIn(name).isDefined

  private[assistant] def normalizeReadRange(
      totalLines: Int,
      requestedStart: Int,
      requestedEnd: Int
  ): (Int, Int) = {
    if (totalLines <= 0) (1, 0)
    else {
      val start = math.max(1, math.min(totalLines, requestedStart))
      val rawEnd = if (requestedEnd <= 0) totalLines else requestedEnd
      val end = math.max(start, math.min(totalLines, rawEnd))
      (start, end)
    }
  }

  private[assistant] def clampOffset(offset: Int, bufferLength: Int): Int =
    math.max(0, math.min(offset, bufferLength))

  private val readToolsTimeoutMs: Long =
    AssistantConstants.CONTEXT_FETCH_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS

  private val numberedLinePattern = """^\s*(?:→\s*)?(\d+):(.*)$""".r

  private def normalizeTheoryFileName(raw: String): String = {
    val trimmed = raw.trim
    if (trimmed.endsWith(".thy")) trimmed else s"$trimmed.thy"
  }

  private def baseName(path: String): String =
    java.nio.file.Paths.get(path).getFileName.toString

  private def optionalIntArg(args: ResponseParser.ToolArgs, key: String): Option[Int] =
    args.get(key).map {
      case ResponseParser.DecimalValue(d) if !d.isWhole =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer, got decimal value: $d"
        )
      case ResponseParser.DecimalValue(d) => d.toInt
      case ResponseParser.IntValue(i)     => i
      case ResponseParser.StringValue(s) =>
        scala.util.Try(s.toInt).getOrElse(
          throw new IllegalArgumentException(
            s"Parameter '$key' must be an integer, got: '$s'"
          )
        )
      case ResponseParser.BooleanValue(_) | ResponseParser.JsonValue(_) =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer"
        )
      case ResponseParser.NullValue =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer"
        )
    }

  private def selectionArgsForCurrentView(view: View): Map[String, Any] =
    Option(view) match {
      case None => Map("command_selection" -> "current")
      case Some(v) =>
        try {
          val buffer = v.getBuffer
          val pathOpt =
            Option(buffer).flatMap(b => Option(b.getPath)).map(_.trim).filter(_.nonEmpty)
          pathOpt match {
            case Some(path) =>
              val rawOffset = Option(v.getTextArea).map(_.getCaretPosition).getOrElse(0)
              val bufferLength = Option(buffer).map(_.getLength).getOrElse(0)
              val offset = clampOffset(rawOffset, bufferLength)
              Map(
                "command_selection" -> "file_offset",
                "path" -> path,
                "offset" -> offset
              )
            case None =>
              Map("command_selection" -> "current")
          }
        } catch {
          case _: Exception =>
            Map("command_selection" -> "current")
        }
    }

  private def currentBufferPath(view: View): Either[String, String] =
    Option(view)
      .flatMap(v => Option(v.getBuffer))
      .flatMap(b => Option(b.getPath))
      .map(_.trim)
      .filter(_.nonEmpty)
      .toRight("Error: current buffer has no path")

  private def resolveTheoryPath(
      theory: String,
      openOnly: Boolean = true
  ): Either[String, String] = {
    val normalized = normalizeTheoryFileName(theory)
    IQMcpClient
      .callListFiles(
        filterOpen = if (openOnly) Some(true) else None,
        filterTheory = Some(true),
        sortBy = Some("path"),
        timeoutMs = readToolsTimeoutMs
      )
      .flatMap { result =>
        val matches = result.files.filter(f => baseName(f.path) == normalized)
        matches match {
          case one :: Nil => Right(one.path)
          case Nil =>
            val scopeHint =
              if (openOnly) "open or tracked theory files" else "tracked theory files"
            Left(s"Theory '$theory' not found in $scopeHint.")
          case many =>
            Left(
              s"Theory '$theory' is ambiguous; matching paths: ${
                  many.map(_.path).mkString(", ")
                }"
            )
        }
      }
  }

  private def lineCountFromNumberedContent(content: String): Int =
    content.linesIterator.count {
      case numberedLinePattern(_, _) => true
      case _                         => false
    }

  private def stripNumberPrefix(line: String): String = line match {
    case numberedLinePattern(_, rest) => rest
    case _                            => line
  }

  private def stripNumberPrefixes(content: String): String =
    content.linesIterator.map(stripNumberPrefix).mkString("\n")

  private def firstHighlightedOrFirstLine(context: String): String = {
    val nonEmpty = context.linesIterator.map(_.trim).filter(_.nonEmpty).toList
    val picked = nonEmpty.find(_.startsWith("→")).orElse(nonEmpty.headOption).getOrElse("")
    stripNumberPrefix(picked).trim
  }

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

  private def isSensitiveArgName(argName: String): Boolean = {
    val lowered = argName.toLowerCase(Locale.ROOT)
    sensitiveArgTokens.exists(token => lowered.contains(token))
  }

  private def summarizeToolArgsForLog(args: ResponseParser.ToolArgs): String =
    args.map { case (k, v) =>
      val rendered =
        if (isSensitiveArgName(k)) "***"
        else ResponseParser.toolValueToDisplay(v).replace('\n', ' ').take(100)
      s"$k=$rendered"
    }.mkString(", ")

  private def safeLog(message: String): Unit = {
    try Output.writeln(message)
    catch {
      case NonFatal(_) | _: LinkageError => ()
    }
  }

  private def firstNonEmpty(parts: List[String]): Option[String] =
    parts.map(_.trim).find(_.nonEmpty)

  private def exploreFailureMessage(
      result: IQMcpClient.ExploreResult,
      fallback: String
  ): String =
    firstNonEmpty(List(result.error.getOrElse(""), result.message, result.results))
      .getOrElse(fallback)

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
    AssistantDockable.setStatus(s"[tool] $toolName...")
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

  private def execReadTheory(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        val start = optionalIntArg(args, "start_line")
        val end = optionalIntArg(args, "end_line")
        resolveTheoryPath(theory).fold(
          err => err,
          path =>
            IQMcpClient
              .callReadFileLine(
                path = path,
                startLine = start.orElse(Some(1)),
                endLine = end,
                timeoutMs = readToolsTimeoutMs
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                content =>
                  if (content.trim.isEmpty) s"Theory $theory is empty."
                  else s"Theory $theory:\n$content"
              )
        )
    }
  }

  private def execListTheories(): String = {
    IQMcpClient
      .callListFiles(
        filterOpen = Some(true),
        filterTheory = Some(true),
        sortBy = Some("path"),
        timeoutMs = readToolsTimeoutMs
      )
      .fold(
        err => s"Error: $err",
        listed => {
          val theories = listed.files.map(f => baseName(f.path)).distinct.sorted
          if (theories.nonEmpty) theories.mkString("\n") else "No theory files open."
        }
      )
  }

  private def execSearchInTheory(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        if (pattern.isEmpty) "Error: pattern required"
        else {
          val max = math.min(
            AssistantConstants.MAX_SEARCH_RESULTS,
            math.max(1, intArg(args, "max_results", 20))
          )
          resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient
                .callReadFileSearch(
                  path = path,
                  pattern = pattern,
                  contextLines = 0,
                  timeoutMs = readToolsTimeoutMs
                )
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  matches => {
                    val shown = matches.take(max)
                    if (shown.isEmpty) s"No matches for '$pattern' in $theory."
                    else
                      shown
                        .map(m =>
                          s"${m.lineNumber}: ${firstHighlightedOrFirstLine(m.context)}"
                        )
                        .mkString("\n")
                  }
                )
          )
        }
    }
  }

  private def execGetGoalState(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetContextInfo(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          ctx =>
            if (ctx.goal.hasGoal && ctx.goal.goalText.trim.nonEmpty)
              ctx.goal.goalText.trim
            else "No goal at cursor position."
        )
  }

  private def execGetProofContext(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetProofContext(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
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

  private def execFindTheorems(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
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
          query = "find_theorems",
          arguments = quoted,
          timeoutMs = timeout,
          extraParams = Map("max_results" -> max)
        )
        .fold(
          mcpErr => s"Error: find_theorems failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty && text != "No results") text
              else s"No theorems found for: $pattern"
            } else if (explore.timedOut) "find_theorems timed out."
            else
              s"Error: ${exploreFailureMessage(explore, "find_theorems failed")}"
          }
        )
    }
  }

  private def execVerifyProof(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val timeout = AssistantOptions.getVerificationTimeout
      IQMcpClient
        .callExplore(
          query = "proof",
          arguments = proof,
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"[FAIL] I/Q MCP verification failed: $mcpErr",
          explore => {
            if (explore.success) "[ok] Proof verified"
            else if (explore.timedOut) "[FAIL] Timed out"
            else
              s"[FAIL] Failed: ${exploreFailureMessage(explore, "proof verification failed")}"
          }
        )
    }
  }

  private def execRunSledgehammer(@unused view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val timeout = AssistantOptions.getSledgehammerTimeout
      IQMcpClient
        .callExplore(
          query = "sledgehammer",
          arguments = "",
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"Error: sledgehammer failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty) text else "No proofs found."
            } else if (explore.timedOut) "Sledgehammer timed out."
            else s"Error: ${exploreFailureMessage(explore, "sledgehammer failed")}"
          }
        )
    }
  }

  private def execRunNitpick(@unused view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val timeout = AssistantOptions.getNitpickTimeout
      IQMcpClient
        .callExplore(
          query = "proof",
          arguments = "nitpick",
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"Error: nitpick failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty) text else "Nitpick returned no output."
            } else if (explore.timedOut) "Nitpick timed out."
            else s"Error: ${exploreFailureMessage(explore, "nitpick failed")}"
          }
        )
    }
  }

  private def execRunQuickcheck(@unused view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val timeout = AssistantOptions.getQuickcheckTimeout
      IQMcpClient
        .callExplore(
          query = "proof",
          arguments = "quickcheck",
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"Error: quickcheck failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty) text else "Quickcheck returned no output."
            } else if (explore.timedOut) "Quickcheck timed out."
            else s"Error: ${exploreFailureMessage(explore, "quickcheck failed")}"
          }
        )
    }
  }

  private def execGetType(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetTypeAtSelection(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
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
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callResolveCommandTarget(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          resolved =>
            Option(resolved.command.source)
              .map(_.trim)
              .filter(_.nonEmpty)
              .getOrElse("No command at cursor position.")
        )
  }

  private def execGetErrors(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val timeoutMs = readToolsTimeoutMs

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
              formatDiagnosticsMessages(diagnostics, "No errors at cursor position.")
          )

      case "all" =>
        currentBufferPath(view).fold(
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
        resolveTheoryPath(effectiveScope).fold(
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
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
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

  private def execExecuteStep(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val timeout = AssistantOptions.getVerificationTimeout
      val mcpStart = System.currentTimeMillis()
      IQMcpClient
        .callExplore(
          query = "proof",
          arguments = proof,
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"[FAIL] step execution failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.isEmpty) "Error: step execution completed without a result."
              else {
                val stepResult = IQIntegration.parseStepResult(
                  text,
                  System.currentTimeMillis() - mcpStart
                )
                val status =
                  if (stepResult.complete) "[COMPLETE]"
                  else
                    stepResult.numSubgoals match {
                      case Some(n) => s"[$n subgoals]"
                      case None    => "[subgoal count unknown]"
                    }
                s"$status\n${stepResult.stateText}"
              }
            } else if (explore.timedOut) "Step execution timed out."
            else s"[FAIL] ${exploreFailureMessage(explore, "step execution failed")}"
          }
        )
    }
  }

  private def execTraceSimplifier(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val method = safeStringArg(args, "method", 50)
    val effectiveMethod =
      if (method.isEmpty || method == "simp") "simp" else method
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val timeout = AssistantOptions.getTraceTimeout
      val depth = AssistantOptions.getTraceDepth
      val queryTimeoutMs =
        timeout * 1000L + AssistantConstants.TIMEOUT_BUFFER_MS
      val queryArg = s"simp_trace $effectiveMethod $timeout $depth"
      IQMcpClient
        .callExplore(
          query = "proof",
          arguments = queryArg,
          timeoutMs = queryTimeoutMs
        )
        .fold(
          mcpErr => s"Error: simplifier trace failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.nonEmpty) text
              else "Error: simplifier trace completed without a result."
            } else if (explore.timedOut) "Simplifier trace timed out."
            else
              s"Error: ${exploreFailureMessage(explore, "simplifier trace failed")}"
          }
        )
    }
  }

  private def execGetProofBlock(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetProofBlocksForSelection(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          blocks =>
            blocks.proofBlocks.headOption
              .map(_.proofText.trim)
              .filter(_.nonEmpty)
              .getOrElse(
                blocks.message.getOrElse("No proof block at cursor position.")
              )
        )
  }

  private def execGetContextInfo(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetContextInfo(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
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

  private def execSearchAllTheories(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else {
      val maxTotal = math.min(200, math.max(1, intArg(args, "max_results", 50)))
      IQMcpClient
        .callListFiles(
          filterOpen = Some(true),
          filterTheory = Some(true),
          sortBy = Some("path"),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          listed => {
            val allMatches = scala.collection.mutable.ListBuffer[String]()
            listed.files.iterator.takeWhile(_ => allMatches.length < maxTotal).foreach { file =>
              val remaining = maxTotal - allMatches.length
              val matches = IQMcpClient
                .callReadFileSearch(
                  path = file.path,
                  pattern = pattern,
                  contextLines = 0,
                  timeoutMs = readToolsTimeoutMs
                )
                .getOrElse(Nil)
                .take(remaining)
              matches.foreach { m =>
                allMatches += s"${baseName(file.path)}:${m.lineNumber}: ${
                    firstHighlightedOrFirstLine(m.context)
                  }"
              }
            }

            if (allMatches.nonEmpty) {
              val truncated =
                if (allMatches.length >= maxTotal) s" (showing first $maxTotal)"
                else ""
              s"Found ${allMatches.length} matches$truncated:\n${allMatches.mkString("\n")}"
            } else s"No matches for '$pattern' in any open theory."
          }
        )
    }
  }

  private def execGetDependencies(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        resolveTheoryPath(theory).fold(
          err => err,
          path =>
            IQMcpClient
              .callReadFileLine(
                path = path,
                startLine = Some(1),
                endLine = Some(-1),
                timeoutMs = readToolsTimeoutMs
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                numberedContent => {
                  val content = stripNumberPrefixes(numberedContent)
                  val importPattern = """(?s)imports\s+(.*?)(?:\bbegin\b|\z)""".r
                  importPattern.findFirstMatchIn(content) match {
                    case Some(m) =>
                      val tokenPattern = """"[^"]+"|[^\s"]+""".r
                      val imports =
                        tokenPattern.findAllIn(m.group(1)).toList.filter(_.nonEmpty)
                      if (imports.nonEmpty)
                        s"Dependencies of $theory:\n${imports.mkString("\n")}"
                      else s"Theory '$theory' has no explicit imports."
                    case None => s"No imports found in theory '$theory'."
                  }
                }
              )
        )
    }
  }

  private def execGetWarnings(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val timeoutMs = readToolsTimeoutMs

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
        currentBufferPath(view).fold(
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
        resolveTheoryPath(effectiveScope).fold(
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

  private def execEditTheory(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
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
          resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient
                .callReadFileLine(
                  path = path,
                  startLine = Some(1),
                  endLine = Some(-1),
                  timeoutMs = readToolsTimeoutMs
                )
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  numberedContent => {
                    val lineCount = lineCountFromNumberedContent(numberedContent)
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
                          val contextStart = math.max(1, startLine - 3)
                          val contextEnd = math.max(contextStart, startLine + 5)
                          val context = IQMcpClient
                            .callReadFileLine(
                              path = path,
                              startLine = Some(contextStart),
                              endLine = Some(contextEnd),
                              timeoutMs = readToolsTimeoutMs
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
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
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

  private def execGetEntities(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        val maxResultsRaw = intArg(args, "max_results", 200)
        val maxResults = math.max(1, math.min(1000, maxResultsRaw))
        resolveTheoryPath(theory).fold(
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

  private def execWebSearch(args: ResponseParser.ToolArgs): String = {
    val query = safeStringArg(args, "query", MAX_PATTERN_ARG_LENGTH)
    if (query.isEmpty) "Error: query required"
    else {
      val maxResults = math.min(10, math.max(1, intArg(args, "max_results", 5)))
      try {
        val encodedQuery = java.net.URLEncoder.encode(query, "UTF-8")
        val url = s"https://lite.duckduckgo.com/lite/?q=$encodedQuery"

        val client = java.net.http.HttpClient
          .newBuilder()
          .connectTimeout(java.time.Duration.ofSeconds(10))
          .followRedirects(java.net.http.HttpClient.Redirect.NORMAL)
          .build()
        val request = java.net.http.HttpRequest
          .newBuilder()
          .uri(java.net.URI.create(url))
          .timeout(java.time.Duration.ofSeconds(10))
          .GET()
          .build()

        val response = client.send(
          request,
          java.net.http.HttpResponse.BodyHandlers.ofString()
        )
        val html = response.body()

        val results = scala.collection.mutable.ListBuffer[String]()
        val linkPattern = """<a[^>]+href="([^"]+)"[^>]*>([^<]+)</a>""".r

        import scala.util.boundary, boundary.break
        boundary {
          for (m <- linkPattern.findAllMatchIn(html).take(maxResults * 2)) {
            val href = m.group(1)
            val title = m.group(2).trim
            if (!href.startsWith("//duckduckgo.com") && title.nonEmpty) {
              results += s"$title\n  URL: $href"
            }
            if (results.length >= maxResults) break()
          }
        }

        if (results.nonEmpty) results.mkString("\n\n")
        else s"No search results found for: $query"
      } catch {
        case ex: Exception => s"Web search error: ${ex.getMessage}"
      }
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
      s"Error: invalid theory name '$name'"
    else {
      currentBufferPath(view).fold(
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

            if (targetPath.getParent != normalizedDir)
              s"Error: invalid theory name '$name'"
            else
              IQMcpClient
                .callOpenFile(
                  path = targetPath.toString,
                  createIfMissing = true,
                  inView = true,
                  content = Some(theoryContent),
                  overwriteIfExists = false,
                  timeoutMs = AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC * 1000L
                )
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  _ => s"Created and opened $name.thy"
                )
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
            currentBufferPath(view).fold(_ => path, current =>
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
            opened => s"Opened ${baseName(opened.path)}"
          )
      }
    }
  }

  /**
   * Shared method to prompt the user with multiple choice options.
   * Returns Some(selectedOption) or None if cancelled/timeout.
   * Used by both execAskUser and ToolPermissions.promptUser.
   */
  private[assistant] def promptUserWithChoices(
    question: String, options: List[String], context: String, view: View
  ): Option[String] = {
    if (options.length < 2) return None
    
    val latch = new CountDownLatch(1)
    @volatile var selectedOption = ""
    
    GUI_Thread.later {
      val html = buildAskUserHtml(question, context, options, { choice =>
        selectedOption = choice
        latch.countDown()
      })
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html, 
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    AssistantDockable.setStatus("Waiting for your input...")
    
    val timeout = 300L
    var responded = false
    val endTime = System.currentTimeMillis() + timeout * 1000
    while (!responded && !AssistantDockable.isCancelled && System.currentTimeMillis() < endTime) {
      responded = latch.await(500, TimeUnit.MILLISECONDS)
    }
    
    if (AssistantDockable.isCancelled || !responded) {
      None
    } else {
      AssistantDockable.setStatus("Processing your choice...")
      GUI_Thread.later {
        ChatAction.addMessage(ChatAction.Message(ChatAction.User, s"Selected: $selectedOption", 
          java.time.LocalDateTime.now(), transient = true))
        AssistantDockable.showConversation(ChatAction.getHistory)
      }
      Some(selectedOption)
    }
  }

  private def execAskUser(args: ResponseParser.ToolArgs, view: View): String = {
    val question = safeStringArg(args, "question", 500)
    val optionsStr = safeStringArg(args, "options", 1000)
    val context = safeStringArg(args, "context", 500)
    
    if (question.isEmpty) return "Error: question required"
    
    val options = optionsStr.split(",").map(_.trim).filter(_.nonEmpty).toList
    if (options.length < 2) return "Error: at least 2 options required"
    
    promptUserWithChoices(question, options, context, view) match {
      case Some(choice) => choice
      case None if AssistantDockable.isCancelled => "User cancelled the operation."
      case None => "User did not respond within the time limit."
    }
  }

  private def execTaskListAdd(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val title = safeStringArg(args, "title", 500)
    val description = safeStringArg(args, "description", 2000)
    val criteria = safeStringArg(args, "acceptance_criteria", 2000)
    
    val result = TaskList.addTask(title, description, criteria)
    
    // Inject rich HTML widget
    GUI_Thread.later {
      val html = buildTaskAddedHtml(title, description, criteria)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  private def execTaskListDone(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val taskId = intArg(args, "task_id", -1)
    val result = TaskList.markDone(taskId)
    
    // Inject rich HTML widget
    GUI_Thread.later {
      val html = buildTaskStatusHtml(taskId, "done", result)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  private def execTaskListIrrelevant(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val taskId = intArg(args, "task_id", -1)
    val result = TaskList.markIrrelevant(taskId)
    
    // Inject rich HTML widget
    GUI_Thread.later {
      val html = buildTaskStatusHtml(taskId, "irrelevant", result)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  private def execTaskListNext(@unused view: View): String = {
    val result = TaskList.getNextTask()
    
    // Inject rich HTML widget showing full checklist with next task highlighted
    GUI_Thread.later {
      val html = buildTaskListHtml(highlightNext = true)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  private def execTaskListShow(@unused view: View): String = {
    val result = TaskList.listTasks()
    
    // Inject rich HTML widget showing full checklist
    GUI_Thread.later {
      val html = buildTaskListHtml(highlightNext = false)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  private def execTaskListGet(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val taskId = intArg(args, "task_id", -1)
    val result = TaskList.getTask(taskId)
    
    // Inject rich HTML widget showing detailed task card
    GUI_Thread.later {
      TaskList.getTasks.find(_.id == taskId).foreach { task =>
        val html = buildTaskDetailHtml(task)
        ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
          java.time.LocalDateTime.now(), rawHtml = true, transient = true))
        AssistantDockable.showConversation(ChatAction.getHistory)
      }
    }
    
    result
  }

  private def buildTaskAddedHtml(
      title: String,
      description: String,
      criteria: String
  ): String = {
    val border = UIColors.TaskList.border
    val bg = UIColors.TaskList.background
    val headerText = UIColors.TaskList.headerText
    val labelColor = UIColors.TaskList.labelColor
    val taskText = UIColors.TaskList.taskText
    
    val truncDesc = if (description.length > 100) description.take(100) + "..." else description
    val truncCrit = if (criteria.length > 100) criteria.take(100) + "..." else criteria
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:3px;font-weight:bold;'>
       |+ Task Added</div>
       |<div style='font-size:11pt;color:$taskText;margin-bottom:2px;'>
       |"${HtmlUtil.escapeHtml(title)}"</div>
       |<div style='font-size:9pt;color:$labelColor;margin-top:4px;'>
       |Description: <span style='color:$taskText;'>${HtmlUtil.escapeHtml(truncDesc)}</span></div>
       |<div style='font-size:9pt;color:$labelColor;'>
       |Criteria: <span style='color:$taskText;'>${HtmlUtil.escapeHtml(truncCrit)}</span></div>
       |</div>""".stripMargin
  }

  private def buildTaskStatusHtml(taskId: Int, status: String, result: String): String = {
    val border = UIColors.TaskList.border
    val bg = UIColors.TaskList.background
    val headerText = UIColors.TaskList.headerText
    val icon = if (status == "done") UIColors.TaskList.doneIcon else UIColors.TaskList.irrelevantIcon
    val symbol = if (status == "done") "✓" else "✗"
    val action = if (status == "done") "marked as done" else "marked as irrelevant"
    
    TaskList.getTasks.find(_.id == taskId) match {
      case Some(task) =>
        val (doneCount, todoCount, _) = TaskList.getStatusCounts
        val progress = s"$doneCount/${TaskList.getTaskCount} done, $todoCount pending"
        
        s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
           |border-left:4px solid $border;border-radius:3px;
           |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
           |<div style='font-size:10pt;color:$headerText;margin-bottom:3px;font-weight:bold;'>
           |<span style='color:$icon;'>$symbol</span> Task #$taskId $action</div>
           |<div style='font-size:11pt;margin-bottom:2px;'>
           |"${HtmlUtil.escapeHtml(task.title)}"</div>
           |<div style='font-size:9pt;color:${UIColors.TaskList.progressText};'>
           |Progress: $progress</div>
           |</div>""".stripMargin
      case None =>
        s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
           |border-left:4px solid $border;border-radius:3px;
           |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
           |<div style='font-size:10pt;color:$headerText;'>
           |${HtmlUtil.escapeHtml(result)}</div>
           |</div>""".stripMargin
    }
  }

  private def buildTaskListHtml(highlightNext: Boolean): String = {
    val border = UIColors.TaskList.border
    val bg = UIColors.TaskList.background
    val headerText = UIColors.TaskList.headerText
    val progressText = UIColors.TaskList.progressText
    val doneIcon = UIColors.TaskList.doneIcon
    val pendingIcon = UIColors.TaskList.pendingIcon
    val nextIcon = UIColors.TaskList.nextIcon
    val irrelevantIcon = UIColors.TaskList.irrelevantIcon
    val irrelevantText = UIColors.TaskList.irrelevantText
    val taskText = UIColors.TaskList.taskText
    
    val tasks = TaskList.getTasks
    if (tasks.isEmpty) {
      return s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
         |border-left:4px solid $border;border-radius:3px;
         |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
         |<div style='font-size:10pt;color:$headerText;font-weight:bold;'>Task List</div>
         |<div style='font-size:10pt;color:$progressText;margin-top:4px;'>
         |Task list is empty. Add tasks to get started.</div>
         |</div>""".stripMargin
    }
    
    val (doneCount, todoCount, _) = TaskList.getStatusCounts
    val progress = s"$doneCount/${tasks.length} done, $todoCount pending"
    
    val nextTaskId = tasks.find(_.status == TaskList.Todo).map(_.id)
    
    val taskItems = tasks.map { task =>
      val isNext = highlightNext && nextTaskId.contains(task.id)
      val (icon, iconColor) = task.status match {
        case TaskList.Done => ("✓", doneIcon)
        case TaskList.Irrelevant => ("✗", irrelevantIcon)
        case TaskList.Todo if isNext => ("●", nextIcon)
        case TaskList.Todo => ("○", pendingIcon)
      }
      
      val titleStyle = task.status match {
        case TaskList.Irrelevant => s"color:$irrelevantText;text-decoration:line-through;"
        case _ => s"color:$taskText;"
      }
      
      val nextMarker = if (isNext) " <span style='color:$nextIcon;font-size:9pt;'>← next</span>" else ""
      
      s"""<div style='margin:2px 0;'>
         |<span style='color:$iconColor;font-weight:bold;margin-right:6px;'>$icon</span>
         |<span style='$titleStyle;font-size:10pt;'>#${task.id}. ${HtmlUtil.escapeHtml(task.title)}</span>$nextMarker
         |</div>""".stripMargin
    }.mkString("\n")
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:2px;font-weight:bold;'>
       |Task List <span style='font-weight:normal;color:$progressText;'>($progress)</span></div>
       |<div style='margin-top:6px;'>
       |$taskItems
       |</div>
       |</div>""".stripMargin
  }

  private def buildTaskDetailHtml(task: TaskList.Task): String = {
    val border = UIColors.TaskList.border
    val bg = UIColors.TaskList.background
    val headerText = UIColors.TaskList.headerText
    val labelColor = UIColors.TaskList.labelColor
    val taskText = UIColors.TaskList.taskText
    val (icon, iconColor) = task.status match {
      case TaskList.Done => ("✓", UIColors.TaskList.doneIcon)
      case TaskList.Irrelevant => ("✗", UIColors.TaskList.irrelevantIcon)
      case TaskList.Todo => ("○", UIColors.TaskList.pendingIcon)
    }
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:4px;font-weight:bold;'>
       |Task #${task.id}: ${HtmlUtil.escapeHtml(task.title)}
       |<span style='color:$iconColor;margin-left:8px;'>[$icon]</span></div>
       |<div style='font-size:9pt;color:$labelColor;margin-top:6px;margin-bottom:2px;'>Description:</div>
       |<div style='font-size:10pt;color:$taskText;margin-bottom:6px;'>
       |${HtmlUtil.escapeHtml(task.description)}</div>
       |<div style='font-size:9pt;color:$labelColor;margin-bottom:2px;'>Acceptance Criteria:</div>
       |<div style='font-size:10pt;color:$taskText;'>
       |${HtmlUtil.escapeHtml(task.acceptanceCriteria)}</div>
       |</div>""".stripMargin
  }

  private def buildAskUserHtml(
      question: String,
      context: String,
      options: List[String],
      onChoice: String => Unit
  ): String = {
    // Register an action for each option button
    val optionButtons = options.zipWithIndex
      .map { case (opt, idx) =>
        val actionId = AssistantDockable.registerAction(() => onChoice(opt))
        // Use letters A-Z for first 26 options, then numbers 27+ for any beyond
        val label =
          if (idx < 26) ('A' + idx).toChar.toString else (idx + 1).toString
        // Each option as a clickable list item
        s"""<div style='margin:2px 0 2px 12px;'>
         |<a href='action:insert:$actionId' style='text-decoration:none;color:${UIColors.AskUser.optionLetter};font-weight:bold;'>$label.</a>
         |<a href='action:insert:$actionId' style='text-decoration:none;color:${UIColors.AskUser.optionText};margin-left:8px;'>
         |${HtmlUtil.escapeHtml(opt)}</a>
         |</div>""".stripMargin
      }
      .mkString("\n")

    val contextHtml = if (context.nonEmpty) {
      s"<div style='font-size:10pt;color:${UIColors.AskUser.contextText};margin:4px 0 8px;font-style:italic;'>${HtmlUtil.escapeHtml(context)}</div>"
    } else ""

    // Match the message bubble pattern: white background + colored left border only
    s"""<div style='margin:6px 0;padding:8px 10px;background:${UIColors.AskUser.background};
       |border-left:4px solid ${UIColors.AskUser.border};border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:${UIColors.AskUser.title};margin-bottom:3px;'>
       |<b>Assistant needs your input</b></div>
       |<div style='font-size:12pt;color:#333333;margin-bottom:6px;'>
       |${HtmlUtil.escapeHtml(question)}</div>
       |$contextHtml
       |$optionButtons
       |</div>""".stripMargin
  }

  private def intArg(
      args: ResponseParser.ToolArgs,
      key: String,
      default: Int
  ): Int = {
    args.get(key) match {
      case Some(ResponseParser.DecimalValue(d)) if !d.isWhole =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer, got decimal value: $d"
        )
      case Some(ResponseParser.DecimalValue(d)) => d.toInt
      case Some(ResponseParser.IntValue(i))     => i
      case Some(ResponseParser.StringValue(s))  =>
        scala.util.Try(s.toInt).getOrElse(
          throw new IllegalArgumentException(
            s"Parameter '$key' must be an integer, got: '$s'"
          )
        )
      case Some(ResponseParser.BooleanValue(_)) |
          Some(ResponseParser.JsonValue(_)) =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer"
        )
      case Some(ResponseParser.NullValue) =>
        default
      case _ => default
    }
  }
}
