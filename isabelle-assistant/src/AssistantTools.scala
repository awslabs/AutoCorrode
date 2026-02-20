/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import scala.jdk.CollectionConverters._
import java.util.concurrent.{CountDownLatch, TimeUnit}
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
  case class ToolDef(name: String, description: String, params: List[ToolParam])

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
  def executeToolWithPermission(name: String, args: ResponseParser.ToolArgs, view: View): String = {
    ToolPermissions.checkPermission(name, args) match {
      case ToolPermissions.Allowed =>
        executeTool(name, args, view)
      case ToolPermissions.Denied =>
        Output.writeln(s"[Permissions] Tool '$name' denied by policy")
        s"Permission denied: tool '$name' is not allowed."
      case ToolPermissions.NeedPrompt(toolName, resource) =>
        ToolPermissions.promptUser(toolName, resource, view) match {
          case ToolPermissions.Allowed =>
            executeTool(name, args, view)
          case ToolPermissions.Denied =>
            Output.writeln(s"[Permissions] User denied tool '$name'")
            s"Permission denied: user declined tool '$name'."
          case _ =>
            Output.writeln(s"[Permissions] Unexpected decision for tool '$name'")
            s"Permission denied: tool '$name'."
        }
    }
  }

  /** Maximum length for string arguments from LLM tool calls. */
  private val MAX_STRING_ARG_LENGTH = 10000

  /** Maximum length for proof text arguments. */
  private val MAX_PROOF_ARG_LENGTH = 5000

  /** Maximum length for search pattern arguments. */
  private val MAX_PATTERN_ARG_LENGTH = 500

  /** Valid theory name pattern. */
  private val THEORY_NAME_PATTERN = """^[A-Za-z0-9_.\-/]+$""".r

  /** Sanitize a string argument: trim, limit length, reject control characters.
    */
  private def safeStringArg(
      args: ResponseParser.ToolArgs,
      key: String,
      maxLen: Int = MAX_STRING_ARG_LENGTH
  ): String = {
    val raw = args.get(key).map(ResponseParser.toolValueToString).getOrElse("")
    val cleaned = raw.filter(c => !c.isControl || c == '\n' || c == '\t')
    cleaned.take(maxLen).trim
  }

  /** Validate a theory name argument. */
  private def safeTheoryArg(
      args: ResponseParser.ToolArgs
  ): Either[String, String] = {
    val name = safeStringArg(args, "theory", 200)
    if (name.isEmpty) Left("Error: theory name required")
    else if (THEORY_NAME_PATTERN.findFirstIn(name).isEmpty)
      Left(s"Error: invalid theory name '$name'")
    else Right(name)
  }

  /** Execute a tool by name. Returns the result as a string. Called from the
    * agentic loop on a background thread. All arguments are sanitized before
    * use to prevent injection or resource exhaustion.
    */
  def executeTool(
      name: String,
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    Output.writeln(
      s"[Assistant] Tool call: $name(${args.map { case (k, v) => s"$k=${ResponseParser.toolValueToDisplay(v).take(100)}" }.mkString(", ")})"
    )
    AssistantDockable.setStatus(s"[tool] $name...")
    try {
      name match {
        case "read_theory"         => execReadTheory(args, view)
        case "list_theories"       => execListTheories()
        case "search_in_theory"    => execSearchInTheory(args, view)
        case "get_goal_state"      => execGetGoalState(view)
        case "get_proof_context"   => execGetProofContext(view)
        case "find_theorems"       => execFindTheorems(args, view)
        case "verify_proof"        => execVerifyProof(args, view)
        case "run_sledgehammer"    => execRunSledgehammer(view)
        case "run_nitpick"         => execRunNitpick(view)
        case "run_quickcheck"      => execRunQuickcheck(view)
        case "get_type"            => execGetType(view)
        case "get_command_text"    => execGetCommandText(view)
        case "get_errors"          => execGetErrors(args, view)
        case "get_definitions"     => execGetDefinitions(args, view)
        case "execute_step"        => execExecuteStep(args, view)
        case "trace_simplifier"    => execTraceSimplifier(args, view)
        case "get_proof_block"     => execGetProofBlock(view)
        case "get_context_info"    => execGetContextInfo(view)
        case "search_all_theories" => execSearchAllTheories(args, view)
        case "get_dependencies"    => execGetDependencies(args, view)
        case "get_warnings"        => execGetWarnings(args, view)
        case "set_cursor_position" => execSetCursorPosition(args, view)
        case "edit_theory"         => execEditTheory(args, view)
        case "try_methods"         => execTryMethods(args, view)
        case "get_entities"        => execGetEntities(args, view)
        case "web_search"          => execWebSearch(args)
        case "create_theory"       => execCreateTheory(args, view)
        case "open_theory"         => execOpenTheory(args, view)
        case "ask_user"            => execAskUser(args, view)
        case "task_list_add"       => execTaskListAdd(args, view)
        case "task_list_done"      => execTaskListDone(args, view)
        case "task_list_irrelevant" => execTaskListIrrelevant(args, view)
        case "task_list_next"      => execTaskListNext(view)
        case "task_list_show"      => execTaskListShow(view)
        case "task_list_get"       => execTaskListGet(args, view)
        case _                     => s"Unknown tool: $name"
      }
    } catch {
      case ex: Exception => s"Tool error: ${ex.getMessage}"
    }
  }

  private def execReadTheory(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
        findBuffer(normalized) match {
          case None         => s"Theory '$theory' not found in open buffers."
          case Some(buffer) =>
            val content = buffer.getText(0, buffer.getLength)
            val allLines = content.split("\n")
            val start = math.max(0, intArg(args, "start_line", 1) - 1)
            val end = math.min(
              allLines.length,
              intArg(args, "end_line", allLines.length)
            )
            val lines = allLines.slice(start, end)
            val header =
              s"Theory $theory (lines ${start + 1}-$end of ${allLines.length}):\n"
            header + lines.zipWithIndex
              .map { case (l, i) => s"${start + i + 1}: $l" }
              .mkString("\n")
        }
    }
  }

  private def execListTheories(): String = {
    val buffers = org.gjt.sp.jedit.jEdit.getBufferManager().getBuffers().asScala
    val theories = buffers
      .filter(b => b.getPath != null && b.getPath.endsWith(".thy"))
      .map(b => java.io.File(b.getPath).getName)
      .sorted
    if (theories.nonEmpty) theories.mkString("\n") else "No theory files open."
  }

  private def execSearchInTheory(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        if (pattern.isEmpty) "Error: pattern required"
        else {
          val normalized =
            if (theory.endsWith(".thy")) theory else s"$theory.thy"
          findBuffer(normalized) match {
            case None         => s"Theory '$theory' not found."
            case Some(buffer) =>
              val max = math.min(
                AssistantConstants.MAX_SEARCH_RESULTS,
                math.max(1, intArg(args, "max_results", 20))
              )
              val lines = buffer.getText(0, buffer.getLength).split("\n")
              val matches = lines.zipWithIndex
                .filter(_._1.toLowerCase.contains(pattern.toLowerCase))
                .take(max)
              if (matches.isEmpty) s"No matches for '$pattern' in $theory."
              else
                matches
                  .map { case (l, i) => s"${i + 1}: ${l.trim}" }
                  .mkString("\n")
          }
        }
    }
  }

  private def execGetGoalState(view: View): String = {
    val latch = new CountDownLatch(1)
    @volatile var result = "No goal at cursor position."
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition
        GoalExtractor.getGoalState(buffer, offset).foreach(g => result = g)
      } catch {
        case ex: Exception => ErrorHandler.logSilentError("AssistantTools", ex)
      }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execGetProofContext(view: View): String = {
    // getContextString must be called from a background thread (it dispatches to GUI internally)
    PrintContextAction
      .getContextString(view)
      .getOrElse("No local facts in scope.")
  }

  private def execFindTheorems(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      // Read buffer/offset on GUI thread
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          val buffer = view.getBuffer
          val offset = view.getTextArea.getCaretPosition
          commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
        } catch {
          case ex: Exception =>
            ErrorHandler.logSilentError("AssistantTools", ex)
        }
        cmdLatch.countDown()
      }
      cmdLatch.await(
        AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
        TimeUnit.SECONDS
      )

      commandOpt match {
        case None          => "No Isabelle command at cursor position."
        case Some(command) =>
          val max = math.min(
            AssistantConstants.MAX_FIND_THEOREMS_RESULTS,
            math.max(1, intArg(args, "max_results", 20))
          )
          val timeout = AssistantOptions.getFindTheoremsTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          val quoted =
            if (pattern.startsWith("\"")) pattern else s"\"$pattern\""

          GUI_Thread.later {
            IQIntegration.runFindTheoremsAsync(
              view,
              command,
              quoted,
              max,
              timeout,
              {
                case Right(results) =>
                  result =
                    if (results.nonEmpty) results.mkString("\n")
                    else s"No theorems found for: $pattern"
                  latch.countDown()
                case Left(err) =>
                  result = s"Error: $err"
                  latch.countDown()
              }
            )
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "find_theorems timed out." else result
      }
    }
  }

  private def execVerifyProof(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(
            view.getBuffer,
            view.getTextArea.getCaretPosition
          )
        } catch {
          case ex: Exception =>
            ErrorHandler.logSilentError("AssistantTools", ex)
        }
        cmdLatch.countDown()
      }
      cmdLatch.await(
        AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
        TimeUnit.SECONDS
      )

      commandOpt match {
        case None          => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getVerificationTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.verifyProofAsync(
              view,
              command,
              proof,
              timeout,
              {
                case IQIntegration.ProofSuccess(ms, _) =>
                  result = s"[ok] Proof verified (${ms}ms)"; latch.countDown()
                case IQIntegration.ProofFailure(err) =>
                  result = s"[FAIL] Failed: $err"; latch.countDown()
                case IQIntegration.ProofTimeout =>
                  result = "[FAIL] Timed out"; latch.countDown()
                case _ => result = "[FAIL] Unavailable"; latch.countDown()
              }
            )
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "Verification timed out." else result
      }
    }
  }

  private def execRunSledgehammer(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(
            view.getBuffer,
            view.getTextArea.getCaretPosition
          )
        } catch {
          case ex: Exception =>
            ErrorHandler.logSilentError("AssistantTools", ex)
        }
        cmdLatch.countDown()
      }
      cmdLatch.await(
        AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
        TimeUnit.SECONDS
      )

      commandOpt match {
        case None          => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getSledgehammerTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.runSledgehammerAsync(
              view,
              command,
              timeout,
              {
                case Right(results) if results.nonEmpty =>
                  result = results
                    .map(r => s"${r.proofMethod} (${r.timeMs}ms)")
                    .mkString("\n")
                  latch.countDown()
                case Right(_)  => result = "No proofs found."; latch.countDown()
                case Left(err) => result = s"Error: $err"; latch.countDown()
              }
            )
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "Sledgehammer timed out." else result
      }
    }
  }

  private def execRunNitpick(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(
            view.getBuffer,
            view.getTextArea.getCaretPosition
          )
        } catch {
          case ex: Exception =>
            ErrorHandler.logSilentError("AssistantTools", ex)
        }
        cmdLatch.countDown()
      }
      cmdLatch.await(
        AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
        TimeUnit.SECONDS
      )

      commandOpt match {
        case None          => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getNitpickTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.runQueryAsync(
              view,
              command,
              List("nitpick"),
              timeout,
              {
                case Right(output) => result = output; latch.countDown()
                case Left(err)     => result = s"Error: $err"; latch.countDown()
              }
            )
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "Nitpick timed out." else result
      }
    }
  }

  private def execRunQuickcheck(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(
            view.getBuffer,
            view.getTextArea.getCaretPosition
          )
        } catch {
          case ex: Exception =>
            ErrorHandler.logSilentError("AssistantTools", ex)
        }
        cmdLatch.countDown()
      }
      cmdLatch.await(
        AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
        TimeUnit.SECONDS
      )

      commandOpt match {
        case None          => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getQuickcheckTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.runQueryAsync(
              view,
              command,
              List("quickcheck"),
              timeout,
              {
                case Right(output) => result = output; latch.countDown()
                case Left(err)     => result = s"Error: $err"; latch.countDown()
              }
            )
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "Quickcheck timed out." else result
      }
    }
  }

  private def execGetType(view: View): String = {
    val latch = new CountDownLatch(1)
    @volatile var result = "No type information at cursor position."
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition
        ShowTypeAction.getTypeAtOffset(buffer, offset).foreach(t => result = t)
      } catch {
        case ex: Exception => ErrorHandler.logSilentError("AssistantTools", ex)
      }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execGetCommandText(view: View): String = {
    val latch = new CountDownLatch(1)
    @volatile var result = "No command at cursor position."
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition
        CommandExtractor
          .getCommandAtOffset(buffer, offset)
          .foreach(c => result = c)
      } catch {
        case ex: Exception => ErrorHandler.logSilentError("AssistantTools", ex)
      }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execGetErrors(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val rawScope = safeStringArg(args, "scope", 200)
    val effectiveScope = if (rawScope.isEmpty) "all" else rawScope

    effectiveScope.toLowerCase match {
      case "cursor" =>
        val latch = new CountDownLatch(1)
        @volatile var result = "No errors at cursor position."
        GUI_Thread.later {
          try {
            val buffer = view.getBuffer
            val offset = view.getTextArea.getCaretPosition
            ExplainErrorAction
              .extractErrorAtOffset(buffer, offset)
              .foreach(e => result = e)
          } catch {
            case ex: Exception =>
              ErrorHandler.logSilentError("AssistantTools", ex)
          }
          latch.countDown()
        }
        latch.await(
          AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
          TimeUnit.SECONDS
        )
        result

      case "all" =>
        val latch = new CountDownLatch(1)
        @volatile var result = "No errors in current buffer."
        GUI_Thread.later {
          try {
            val buffer = view.getBuffer
            extractMessagesInBuffer(buffer, isError = true).foreach(e =>
              result = e
            )
          } catch {
            case ex: Exception =>
              ErrorHandler.logSilentError("AssistantTools", ex)
          }
          latch.countDown()
        }
        latch.await(
          AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
          TimeUnit.SECONDS
        )
        result

      case _ =>
        // Use original case for theory name (case-sensitive)
        val normalized =
          if (effectiveScope.endsWith(".thy")) effectiveScope
          else s"$effectiveScope.thy"
        findBuffer(normalized) match {
          case None => s"Theory '$effectiveScope' not found in open buffers."
          case Some(buffer) =>
            val latch = new CountDownLatch(1)
            @volatile var result = s"No errors in theory '$effectiveScope'."
            GUI_Thread.later {
              try {
                extractMessagesInBuffer(buffer, isError = true).foreach(e =>
                  result = e
                )
              } catch {
                case ex: Exception =>
                  Output.warning(
                    s"[Assistant] execGetErrors failed: ${ex.getMessage}"
                  )
              }
              latch.countDown()
            }
            latch.await(
              AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
              TimeUnit.SECONDS
            )
            result
        }
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
        val cmdLatch = new CountDownLatch(1)
        @volatile var commandOpt: Option[Command] = None
        GUI_Thread.later {
          try {
            commandOpt = IQIntegration.getCommandAtOffset(
              view.getBuffer,
              view.getTextArea.getCaretPosition
            )
          } catch {
            case ex: Exception =>
              ErrorHandler.logSilentError("AssistantTools", ex)
          }
          cmdLatch.countDown()
        }
        cmdLatch.await(
          AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
          TimeUnit.SECONDS
        )

        commandOpt match {
          case None          => "No Isabelle command at cursor position."
          case Some(command) =>
            ContextFetcher
              .fetchDefinitionsForNames(
                view,
                command,
                nameList,
                AssistantConstants.CONTEXT_FETCH_TIMEOUT
              )
              .getOrElse(
                s"No definitions found for: ${nameList.mkString(", ")}"
              )
        }
      }
    }
  }

  private def execExecuteStep(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(
            view.getBuffer,
            view.getTextArea.getCaretPosition
          )
        } catch {
          case ex: Exception =>
            ErrorHandler.logSilentError("AssistantTools", ex)
        }
        cmdLatch.countDown()
      }
      cmdLatch.await(
        AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
        TimeUnit.SECONDS
      )

      commandOpt match {
        case None          => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getProveStepTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.executeStepAsync(
              view,
              command,
              proof,
              timeout,
              {
                case Right(stepResult) =>
                  val status =
                    if (stepResult.complete) "[COMPLETE]"
                    else s"[${stepResult.numSubgoals} subgoals]"
                  result = s"$status\n${stepResult.stateText}"
                  latch.countDown()
                case Left(err) =>
                  result = s"[FAIL] $err"
                  latch.countDown()
              }
            )
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "Step execution timed out." else result
      }
    }
  }

  private def execTraceSimplifier(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val method = safeStringArg(args, "method", 50)
    val effectiveMethod =
      if (method.isEmpty || method == "simp") "simp" else method
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(
            view.getBuffer,
            view.getTextArea.getCaretPosition
          )
        } catch {
          case ex: Exception =>
            ErrorHandler.logSilentError("AssistantTools", ex)
        }
        cmdLatch.countDown()
      }
      cmdLatch.await(
        AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
        TimeUnit.SECONDS
      )

      commandOpt match {
        case None          => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getTraceTimeout
          val depth = AssistantOptions.getTraceDepth
          val queryTimeoutMs =
            timeout * 1000L + AssistantConstants.TIMEOUT_BUFFER_MS
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.runQueryAsync(
              view,
              command,
              List(s"simp_trace $effectiveMethod $timeout $depth"),
              queryTimeoutMs,
              {
                case Right(output) => result = output; latch.countDown()
                case Left(err)     => result = s"Error: $err"; latch.countDown()
              }
            )
          }
          latch.await(queryTimeoutMs + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "Simplifier trace timed out." else result
      }
    }
  }

  private def execGetProofBlock(view: View): String = {
    val latch = new CountDownLatch(1)
    @volatile var result = "No proof block at cursor position."
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition
        ProofExtractor
          .getProofBlockAtOffset(buffer, offset)
          .foreach(p => result = p)
      } catch {
        case ex: Exception => ErrorHandler.logSilentError("AssistantTools", ex)
      }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execGetContextInfo(view: View): String = {
    val latch = new CountDownLatch(1)
    @volatile var result = ""
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition
        val selection =
          Option(view.getTextArea.getSelectedText).filter(_.trim.nonEmpty)
        val ctx = MenuContext.analyze(view, buffer, offset, selection)
        val parts = List(
          s"in_proof: ${ctx.inProof}",
          s"has_goal: ${ctx.hasGoal}",
          s"on_error: ${ctx.onError}",
          s"on_warning: ${ctx.onWarning}",
          s"has_selection: ${ctx.hasSelection}",
          s"has_command: ${ctx.hasCommand}",
          s"has_type_info: ${ctx.hasTypeInfo}",
          s"has_apply_proof: ${ctx.hasApplyProof}",
          s"on_definition: ${ctx.onDefinition}",
          s"iq_available: ${ctx.iqAvailable}"
        )
        result = parts.mkString("\n")
      } catch { case _: Exception => result = "Error analyzing context" }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execSearchAllTheories(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else {
      val maxTotal = math.min(200, math.max(1, intArg(args, "max_results", 50)))
      val buffers =
        org.gjt.sp.jedit.jEdit.getBufferManager().getBuffers().asScala
      val theories = buffers
        .filter(b => b.getPath != null && b.getPath.endsWith(".thy"))
        .toList

      val allMatches = scala.collection.mutable.ListBuffer[String]()
      for (buffer <- theories if allMatches.length < maxTotal) {
        val theoryName = java.io.File(buffer.getPath).getName
        val lines = buffer.getText(0, buffer.getLength).split("\n")
        val matches = lines.zipWithIndex
          .filter(_._1.toLowerCase.contains(pattern.toLowerCase))
          .take(maxTotal - allMatches.length)
        matches.foreach { case (line, idx) =>
          allMatches += s"$theoryName:${idx + 1}: ${line.trim}"
        }
      }

      if (allMatches.nonEmpty) {
        val truncated =
          if (allMatches.length >= maxTotal) s" (showing first $maxTotal)"
          else ""
        s"Found ${allMatches.length} matches$truncated:\n${allMatches.mkString("\n")}"
      } else s"No matches for '$pattern' in any open theory."
    }
  }

  private def execGetDependencies(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
        findBuffer(normalized) match {
          case None         => s"Theory '$theory' not found in open buffers."
          case Some(buffer) =>
            val content = buffer.getText(0, buffer.getLength)
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
    }
  }

  private def execGetWarnings(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val rawScope = safeStringArg(args, "scope", 200)
    val effectiveScope = if (rawScope.isEmpty) "all" else rawScope

    effectiveScope.toLowerCase match {
      case "cursor" =>
        val latch = new CountDownLatch(1)
        @volatile var result = "No warnings at cursor position."
        GUI_Thread.later {
          try {
            val buffer = view.getBuffer
            val offset = view.getTextArea.getCaretPosition
            extractWarningsAtOffset(buffer, offset).foreach(w => result = w)
          } catch {
            case ex: Exception =>
              ErrorHandler.logSilentError("AssistantTools", ex)
          }
          latch.countDown()
        }
        latch.await(
          AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
          TimeUnit.SECONDS
        )
        result

      case "all" =>
        val latch = new CountDownLatch(1)
        @volatile var result = "No warnings in current buffer."
        GUI_Thread.later {
          try {
            val buffer = view.getBuffer
            extractMessagesInBuffer(buffer, isError = false).foreach(w =>
              result = w
            )
          } catch {
            case ex: Exception =>
              ErrorHandler.logSilentError("AssistantTools", ex)
          }
          latch.countDown()
        }
        latch.await(
          AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
          TimeUnit.SECONDS
        )
        result

      case _ =>
        // Use original case for theory name (case-sensitive)
        val normalized =
          if (effectiveScope.endsWith(".thy")) effectiveScope
          else s"$effectiveScope.thy"
        findBuffer(normalized) match {
          case None => s"Theory '$effectiveScope' not found in open buffers."
          case Some(buffer) =>
            val latch = new CountDownLatch(1)
            @volatile var result = s"No warnings in theory '$effectiveScope'."
            GUI_Thread.later {
              try {
                extractMessagesInBuffer(buffer, isError = false).foreach(w =>
                  result = w
                )
              } catch {
                case ex: Exception =>
                  Output.warning(
                    s"[Assistant] execGetWarnings failed: ${ex.getMessage}"
                  )
              }
              latch.countDown()
            }
            latch.await(
              AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
              TimeUnit.SECONDS
            )
            result
        }
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
      latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
      result
    }
  }

  private def execEditTheory(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val operation = safeStringArg(args, "operation", 50).toLowerCase
    val text =
      safeStringArg(args, "text", MAX_STRING_ARG_LENGTH).replace("\\n", "\n")
    val startLine = intArg(args, "start_line", -1)
    val endLine = intArg(args, "end_line", startLine)

    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        if (startLine <= 0) "Error: start_line must be a positive integer"
        else if (!Set("insert", "replace", "delete").contains(operation))
          s"Error: operation must be 'insert', 'replace', or 'delete', got '$operation'"
        else if (
          (operation == "insert" || operation == "replace") && text.isEmpty
        )
          s"Error: text required for $operation operation"
        else {
          val normalized =
            if (theory.endsWith(".thy")) theory else s"$theory.thy"
          findBuffer(normalized) match {
            case None         => s"Theory '$theory' not found in open buffers."
            case Some(buffer) =>
              val latch = new CountDownLatch(1)
              @volatile var result = ""
              GUI_Thread.later {
                try {
                  val lineCount = buffer.getLineCount
                  if (startLine > lineCount) {
                    result =
                      s"Error: start_line $startLine out of range (theory has $lineCount lines)"
                  } else if (endLine > lineCount) {
                    result =
                      s"Error: end_line $endLine out of range (theory has $lineCount lines)"
                  } else {
                    buffer.beginCompoundEdit()
                    try {
                      operation match {
                        case "insert" =>
                          val offset = buffer.getLineStartOffset(startLine - 1)
                          buffer.insert(offset, text + "\n")
                          result =
                            s"Inserted ${text.linesIterator.size} lines before line $startLine"
                        case "replace" =>
                          val startOffset =
                            buffer.getLineStartOffset(startLine - 1)
                          val endOffset = buffer.getLineEndOffset(endLine - 1)
                          buffer.remove(startOffset, endOffset - startOffset)
                          buffer.insert(startOffset, text)
                          result = s"Replaced lines $startLine-$endLine"
                        case "delete" =>
                          val startOffset =
                            buffer.getLineStartOffset(startLine - 1)
                          val endOffset = buffer.getLineEndOffset(endLine - 1)
                          buffer.remove(startOffset, endOffset - startOffset)
                          result = s"Deleted lines $startLine-$endLine"
                      }
                    } finally {
                      buffer.endCompoundEdit()
                    }
                  }
                } catch {
                  case ex: Exception => result = s"Error: ${ex.getMessage}"
                }
                latch.countDown()
              }
              latch.await(
                AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC,
                TimeUnit.SECONDS
              )
              result
          }
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
        val cmdLatch = new CountDownLatch(1)
        @volatile var commandOpt: Option[Command] = None
        GUI_Thread.later {
          try {
            commandOpt = IQIntegration.getCommandAtOffset(
              view.getBuffer,
              view.getTextArea.getCaretPosition
            )
          } catch {
            case ex: Exception =>
              ErrorHandler.logSilentError("AssistantTools", ex)
          }
          cmdLatch.countDown()
        }
        cmdLatch.await(
          AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
          TimeUnit.SECONDS
        )

        commandOpt match {
          case None          => "No Isabelle command at cursor position."
          case Some(command) =>
            val results = scala.collection.mutable.ListBuffer[String]()
            for (method <- methods) {
              val timeout = AssistantOptions.getVerificationTimeout
              val latch = new CountDownLatch(1)
              @volatile var methodResult = ""
              GUI_Thread.later {
                IQIntegration.verifyProofAsync(
                  view,
                  command,
                  method,
                  timeout,
                  {
                    case IQIntegration.ProofSuccess(ms, _) =>
                      methodResult = s"[ok] $method (${ms}ms)";
                      latch.countDown()
                    case IQIntegration.ProofFailure(err) =>
                      methodResult = s"[FAIL] $method: ${err.take(50)}";
                      latch.countDown()
                    case IQIntegration.ProofTimeout =>
                      methodResult = s"[TIMEOUT] $method"; latch.countDown()
                    case _ =>
                      methodResult = s"[UNAVAILABLE] $method"; latch.countDown()
                  }
                )
              }
              latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
              results += (if (methodResult.isEmpty) s"[TIMEOUT] $method"
                          else methodResult)
            }
            s"Tried ${methods.length} methods:\n${results.mkString("\n")}"
        }
      }
    }
  }

  private def execGetEntities(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
        findBuffer(normalized) match {
          case None         => s"Theory '$theory' not found in open buffers."
          case Some(buffer) =>
            val latch = new CountDownLatch(1)
            @volatile var result = ""
            GUI_Thread.later {
              try {
                Document_Model.get_model(buffer).foreach { model =>
                  val snapshot = Document_Model.snapshot(model)
                  val node = snapshot.get_node(model.node_name)
                  val entities = scala.collection.mutable.ListBuffer[String]()
                  val defKeywords = IsabelleKeywords.entityKeywords

                  for ((cmd, cmdOffset) <- node.command_iterator()) {
                    val keyword = cmd.span.name
                    if (defKeywords.contains(keyword)) {
                      val lineNum = buffer.getLineOfOffset(cmdOffset) + 1
                      val source = cmd.source.take(100).trim
                      val name =
                        """(?:lemma|theorem|corollary|proposition|definition|abbreviation|fun|function|primrec|datatype|type_synonym|inductive|coinductive)\s+(\w+)""".r
                          .findFirstMatchIn(source)
                          .map(_.group(1))
                          .getOrElse("(unnamed)")
                      entities += s"Line $lineNum: $keyword $name"
                    }
                  }
                  result =
                    if (entities.nonEmpty) entities.mkString("\n")
                    else "No entities found in theory."
                }
              } catch {
                case ex: Exception => result = s"Error: ${ex.getMessage}"
              }
              latch.countDown()
            }
            latch.await(
              AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC,
              TimeUnit.SECONDS
            )
            result
        }
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
      safeStringArg(args, "content", MAX_STRING_ARG_LENGTH).replace("\\n", "\n")

    if (name.isEmpty) "Error: name required"
    else if (THEORY_NAME_PATTERN.findFirstIn(name).isEmpty)
      s"Error: invalid theory name '$name'"
    else {
      val latch = new CountDownLatch(1)
      @volatile var result = ""
      GUI_Thread.later {
        try {
          val currentPath = view.getBuffer.getPath
          val currentDir = java.io.File(currentPath).getParent
          val filePath = s"$currentDir/$name.thy"

          if (java.io.File(filePath).exists()) {
            result = s"Error: file $name.thy already exists"
          } else {
            val effectiveImports = if (imports.isEmpty) "Main" else imports
            val theoryContent =
              s"theory $name imports $effectiveImports begin\n\n${
                  if (content.nonEmpty) content + "\n\n" else ""
                }end\n"

            java.nio.file.Files.write(
              java.nio.file.Paths.get(filePath),
              theoryContent.getBytes("UTF-8")
            )
            org.gjt.sp.jedit.jEdit.openFile(view, filePath)
            result = s"Created and opened $name.thy"
          }
        } catch { case ex: Exception => result = s"Error: ${ex.getMessage}" }
        latch.countDown()
      }
      latch.await(
        AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC,
        TimeUnit.SECONDS
      )
      result
    }
  }

  private def execOpenTheory(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val path = safeStringArg(args, "path", 1000)
    if (path.isEmpty) "Error: path required"
    else {
      val latch = new CountDownLatch(1)
      @volatile var result = ""
      GUI_Thread.later {
        try {
          val file =
            if (java.io.File(path).isAbsolute) java.io.File(path)
            else {
              val currentPath = view.getBuffer.getPath
              val currentDir = java.io.File(currentPath).getParent
              java.io.File(s"$currentDir/$path")
            }

          if (!file.exists()) {
            result = s"Error: file not found: ${file.getPath}"
          } else if (!file.getName.endsWith(".thy")) {
            result =
              s"Error: not a theory file (must end with .thy): ${file.getName}"
          } else {
            org.gjt.sp.jedit.jEdit.openFile(view, file.getPath)
            result = s"Opened ${file.getName}"
          }
        } catch { case ex: Exception => result = s"Error: ${ex.getMessage}" }
        latch.countDown()
      }
      latch.await(
        AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC,
        TimeUnit.SECONDS
      )
      result
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

  private def execTaskListAdd(args: ResponseParser.ToolArgs, view: View): String = {
    val title = safeStringArg(args, "title", 500)
    val description = safeStringArg(args, "description", 2000)
    val criteria = safeStringArg(args, "acceptance_criteria", 2000)
    
    val result = TaskList.addTask(title, description, criteria)
    
    // Inject rich HTML widget
    GUI_Thread.later {
      val html = buildTaskAddedHtml(title, description, criteria, result)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  private def execTaskListDone(args: ResponseParser.ToolArgs, view: View): String = {
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

  private def execTaskListIrrelevant(args: ResponseParser.ToolArgs, view: View): String = {
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

  private def execTaskListNext(view: View): String = {
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

  private def execTaskListShow(view: View): String = {
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

  private def execTaskListGet(args: ResponseParser.ToolArgs, view: View): String = {
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

  private def buildTaskAddedHtml(title: String, description: String, criteria: String, result: String): String = {
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
       |<div style='font-size:12pt;margin-bottom:6px;'>
       |${HtmlUtil.escapeHtml(question)}</div>
       |$contextHtml
       |$optionButtons
       |</div>""".stripMargin
  }

  /** Extract messages (errors or warnings) from an entire buffer with line
    * numbers. Uses Isabelle's canonical Rendering.text_messages() API to
    * retrieve messages from Command.State.results.
    */
  private def extractMessagesInBuffer(
      buffer: org.gjt.sp.jedit.buffer.JEditBuffer,
      isError: Boolean
  ): Option[String] = {
    try {
      Document_Model.get_model(buffer).flatMap { model =>
        val snapshot = Document_Model.snapshot(model)
        val range = Text.Range(0, buffer.getLength)

        val filter: XML.Elem => Boolean =
          if (isError) Protocol.is_error
          else elem => Protocol.is_warning(elem) || Protocol.is_legacy(elem)

        val messages = Rendering.text_messages(snapshot, range, filter)

        if (messages.nonEmpty) {
          val withLines = messages.map { case Text.Info(msgRange, elem) =>
            val offset = msgRange.start
            val line = buffer.getLineOfOffset(offset) + 1
            val text = XML.content(elem)
            s"Line $line: $text"
          }.distinct
          Some(withLines.mkString("\n"))
        } else None
      }
    } catch {
      case ex: Exception =>
        Output.warning(
          s"[Assistant] extractMessagesInBuffer failed: ${ex.getClass.getSimpleName}: ${ex.getMessage}"
        )
        None
    }
  }

  private def extractWarningsAtOffset(
      buffer: org.gjt.sp.jedit.buffer.JEditBuffer,
      offset: Int
  ): Option[String] = {
    try {
      Document_Model.get_model(buffer).flatMap { model =>
        val snapshot = Document_Model.snapshot(model)
        val range = Text.Range(offset, offset + 1)
        val warnings = snapshot.cumulate(
          range,
          List.empty[String],
          Markup
            .Elements(Markup.WARNING_MESSAGE, Markup.WARNING, Markup.LEGACY),
          _ => {
            case (
                  acc,
                  Text
                    .Info(_, XML.Elem(Markup(Markup.WARNING_MESSAGE, _), body))
                ) =>
              Some(acc :+ XML.content(body))
            case (
                  acc,
                  Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), body))
                ) =>
              Some(acc :+ XML.content(body))
            case (
                  acc,
                  Text.Info(_, XML.Elem(Markup(Markup.LEGACY, _), body))
                ) =>
              Some(acc :+ XML.content(body))
            case _ => None
          }
        )
        val allWarnings = warnings.flatMap(_._2).distinct
        if (allWarnings.nonEmpty) Some(allWarnings.mkString("\n")) else None
      }
    } catch {
      case _: Exception => None
    }
  }

  private def findBuffer(
      normalized: String
  ): Option[org.gjt.sp.jedit.buffer.JEditBuffer] =
    MenuContext.findTheoryBuffer(normalized)

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
        try { s.toInt }
        catch { case _: NumberFormatException => default }
      case Some(ResponseParser.BooleanValue(_)) |
          Some(ResponseParser.JsonValue(_)) | Some(ResponseParser.NullValue) =>
        default
      case _ => default
    }
  }
}
