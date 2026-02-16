/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import scala.jdk.CollectionConverters._
import java.util.concurrent.{CountDownLatch, TimeUnit}
import software.amazon.awssdk.thirdparty.jackson.core.JsonGenerator

/**
 * Tool definitions and execution for LLM tool use (Anthropic function calling).
 * Tools give the LLM autonomous access to theory files, goal state, and Isabelle queries.
 */
object AssistantTools {

  case class ToolParam(name: String, typ: String, description: String, required: Boolean = false)
  case class ToolDef(name: String, description: String, params: List[ToolParam])

  val tools: List[ToolDef] = List(
    ToolDef("read_theory",
      "Read lines from an open Isabelle theory file. Returns the file content. Use start_line/end_line to read a specific range.",
      List(
        ToolParam("theory", "string", "Theory name (e.g. 'Foo' or 'Foo.thy')", required = true),
        ToolParam("start_line", "integer", "First line to read (1-based, default: 1)"),
        ToolParam("end_line", "integer", "Last line to read (default: end of file)")
      )),
    ToolDef("list_theories",
      "List all currently open Isabelle theory files.",
      Nil),
    ToolDef("search_in_theory",
      "Search for a text pattern in an open theory file. Returns matching lines with line numbers.",
      List(
        ToolParam("theory", "string", "Theory name", required = true),
        ToolParam("pattern", "string", "Text pattern to search for (case-insensitive)", required = true),
        ToolParam("max_results", "integer", "Maximum results to return (default: 20)")
      )),
    ToolDef("get_goal_state",
      "Get the current proof goal state at the cursor position. Returns the goal or empty if not in a proof.",
      Nil),
    ToolDef("get_proof_context",
      "Get local facts and assumptions in scope at the cursor position.",
      Nil),
    ToolDef("find_theorems",
      "Search for Isabelle theorems matching a pattern. Requires I/Q plugin.",
      List(
        ToolParam("pattern", "string", "Search pattern for find_theorems", required = true),
        ToolParam("max_results", "integer", "Maximum results (default: 20)")
      )),
    ToolDef("verify_proof",
      "Verify a proof method against the current goal using Isabelle. Returns success/failure. Requires I/Q plugin.",
      List(
        ToolParam("proof", "string", "Proof method to verify (e.g. 'by simp', 'by auto')", required = true)
      )),
    ToolDef("run_sledgehammer",
      "Run Sledgehammer to find proofs using external ATP provers. Returns found proof methods. Requires I/Q plugin.",
      Nil),
    ToolDef("run_nitpick",
      "Run Nitpick model finder to search for counterexamples to the current goal. Returns counterexample if found. Requires I/Q plugin.",
      Nil),
    ToolDef("run_quickcheck",
      "Run QuickCheck to test the current goal with random examples. Returns counterexample if found. Requires I/Q plugin.",
      Nil),
    ToolDef("get_type",
      "Get type information for the term at the cursor position. Returns the term and its type.",
      Nil),
    ToolDef("get_command_text",
      "Get the source text of the Isabelle command at the cursor position.",
      Nil),
    ToolDef("get_errors",
      "Get error messages at the cursor position from PIDE. Returns error text if any errors are present.",
      Nil),
    ToolDef("get_definitions",
      "Get definitions for specified constant or type names. Returns the definition text for each name. Requires I/Q plugin.",
      List(
        ToolParam("names", "string", "Space-separated list of constant/type names to look up", required = true)
      )),
    ToolDef("execute_step",
      "Execute a proof step and return the resulting proof state. Use this to explore what happens when you apply a proof method. Returns the new goal state and whether the proof is complete. Requires I/Q plugin.",
      List(
        ToolParam("proof", "string", "Proof text to execute (e.g., 'by simp', 'apply auto')", required = true)
      )),
    ToolDef("trace_simplifier",
      "Trace the simplifier to understand rewriting steps. Returns detailed trace of simp/auto operations. Requires I/Q plugin.",
      List(
        ToolParam("method", "string", "Method to trace: 'simp' or 'auto' (default: 'simp')")
      )),
    ToolDef("get_proof_block",
      "Get the full proof block (lemma/theorem...qed/done) at the cursor position. Returns the complete proof text including the statement.",
      Nil),
    ToolDef("get_context_info",
      "Get structured context information at cursor: whether in a proof, whether there's a goal, whether on an error, etc. Returns a summary of the cursor context.",
      Nil),
    ToolDef("search_all_theories",
      "Search for a text pattern across all open theory files. Returns matching lines with theory names and line numbers.",
      List(
        ToolParam("pattern", "string", "Text pattern to search for (case-insensitive)", required = true),
        ToolParam("max_results", "integer", "Maximum total results across all theories (default: 50)")
      )),
    ToolDef("get_dependencies",
      "Get the import dependencies for a specific theory file. Returns the list of imported theories.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )),
    ToolDef("get_warnings",
      "Get warning messages at the cursor position from PIDE. Returns warning text if any warnings are present.",
      Nil),
    ToolDef("set_cursor_position",
      "Move the cursor to a specific line number in the current theory. This allows inspection of goals and context at different positions. Returns confirmation or error.",
      List(
        ToolParam("line", "integer", "Line number to move cursor to (1-based)", required = true)
      )),
    ToolDef("edit_theory",
      "Edit a theory file by inserting, replacing, or deleting text at specified line ranges. Use read_theory first to see current content. All edits are wrapped in compound edits for proper undo support.",
      List(
        ToolParam("theory", "string", "Theory name", required = true),
        ToolParam("operation", "string", "Operation: 'insert', 'replace', or 'delete'", required = true),
        ToolParam("start_line", "integer", "Starting line number (1-based)", required = true),
        ToolParam("end_line", "integer", "Ending line number for replace/delete operations (1-based, inclusive)"),
        ToolParam("text", "string", "Text to insert or use as replacement (required for insert/replace)")
      )),
    ToolDef("try_methods",
      "Try multiple proof methods at once and return which ones succeed. More efficient than calling verify_proof repeatedly. Returns results for all methods. Requires I/Q plugin.",
      List(
        ToolParam("methods", "string", "Comma-separated list of proof methods to try (e.g., 'by simp, by auto, by blast')", required = true)
      )),
    ToolDef("get_entities",
      "List all named entities (lemmas, definitions, datatypes, etc.) in a theory file with their line numbers. Returns a structured listing of the theory's contents.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )),
    ToolDef("web_search",
      "Search the web for Isabelle documentation, AFP entries, or formalization patterns. Returns titles, snippets, and URLs from search results.",
      List(
        ToolParam("query", "string", "Search query", required = true),
        ToolParam("max_results", "integer", "Maximum results to return (default: 5)")
      )),
    ToolDef("create_theory",
      "Create a new Isabelle theory file in the same directory as the current buffer. The file will be opened in jEdit after creation.",
      List(
        ToolParam("name", "string", "Theory name (without .thy extension)", required = true),
        ToolParam("imports", "string", "Space-separated list of theories to import (default: 'Main')"),
        ToolParam("content", "string", "Initial content to add after 'begin' (optional)")
      )),
    ToolDef("open_theory",
      "Open an existing theory file that is not currently open. Makes it available for inspection and editing with other tools.",
      List(
        ToolParam("path", "string", "Path to theory file (relative or absolute)", required = true)
      ))
  )

  /** Write tool definitions into a JsonGenerator as the Anthropic tools array. */
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

  /** Maximum length for string arguments from LLM tool calls. */
  private val MAX_STRING_ARG_LENGTH = 10000
  /** Maximum length for proof text arguments. */
  private val MAX_PROOF_ARG_LENGTH = 5000
  /** Maximum length for search pattern arguments. */
  private val MAX_PATTERN_ARG_LENGTH = 500
  /** Valid theory name pattern. */
  private val THEORY_NAME_PATTERN = """^[A-Za-z0-9_.\-/]+$""".r

  /** Sanitize a string argument: trim, limit length, reject control characters. */
  private def safeStringArg(args: Map[String, Any], key: String, maxLen: Int = MAX_STRING_ARG_LENGTH): String = {
    val raw = args.getOrElse(key, "").toString
    val cleaned = raw.filter(c => !c.isControl || c == '\n' || c == '\t')
    cleaned.take(maxLen).trim
  }

  /** Validate a theory name argument. */
  private def safeTheoryArg(args: Map[String, Any]): Either[String, String] = {
    val name = safeStringArg(args, "theory", 200)
    if (name.isEmpty) Left("Error: theory name required")
    else if (THEORY_NAME_PATTERN.findFirstIn(name).isEmpty) Left(s"Error: invalid theory name '$name'")
    else Right(name)
  }

  /**
   * Execute a tool by name. Returns the result as a string.
   * Called from the agentic loop on a background thread.
   * All arguments are sanitized before use to prevent injection or resource exhaustion.
   */
  def executeTool(name: String, args: Map[String, Any], view: View): String = {
    Output.writeln(s"[Assistant] Tool call: $name(${args.map { case (k, v) => s"$k=${v.toString.take(100)}" }.mkString(", ")})")
    AssistantDockable.setStatus(s"[tool] $name...")
    try {
      name match {
        case "read_theory" => execReadTheory(args, view)
        case "list_theories" => execListTheories()
        case "search_in_theory" => execSearchInTheory(args, view)
        case "get_goal_state" => execGetGoalState(view)
        case "get_proof_context" => execGetProofContext(view)
        case "find_theorems" => execFindTheorems(args, view)
        case "verify_proof" => execVerifyProof(args, view)
        case "run_sledgehammer" => execRunSledgehammer(view)
        case "run_nitpick" => execRunNitpick(view)
        case "run_quickcheck" => execRunQuickcheck(view)
        case "get_type" => execGetType(view)
        case "get_command_text" => execGetCommandText(view)
        case "get_errors" => execGetErrors(view)
        case "get_definitions" => execGetDefinitions(args, view)
        case "execute_step" => execExecuteStep(args, view)
        case "trace_simplifier" => execTraceSimplifier(args, view)
        case "get_proof_block" => execGetProofBlock(view)
        case "get_context_info" => execGetContextInfo(view)
        case "search_all_theories" => execSearchAllTheories(args, view)
        case "get_dependencies" => execGetDependencies(args, view)
        case "get_warnings" => execGetWarnings(view)
        case "set_cursor_position" => execSetCursorPosition(args, view)
        case "edit_theory" => execEditTheory(args, view)
        case "try_methods" => execTryMethods(args, view)
        case "get_entities" => execGetEntities(args, view)
        case "web_search" => execWebSearch(args)
        case "create_theory" => execCreateTheory(args, view)
        case "open_theory" => execOpenTheory(args, view)
        case _ => s"Unknown tool: $name"
      }
    } catch {
      case ex: Exception => s"Tool error: ${ex.getMessage}"
    }
  }

  private def execReadTheory(args: Map[String, Any], view: View): String = {
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
      val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
      findBuffer(normalized) match {
        case None => s"Theory '$theory' not found in open buffers."
        case Some(buffer) =>
          val content = buffer.getText(0, buffer.getLength)
          val allLines = content.split("\n")
          val start = math.max(0, intArg(args, "start_line", 1) - 1)
          val end = math.min(allLines.length, intArg(args, "end_line", allLines.length))
          val lines = allLines.slice(start, end)
          val header = s"Theory $theory (lines ${start + 1}-$end of ${allLines.length}):\n"
          header + lines.zipWithIndex.map { case (l, i) => s"${start + i + 1}: $l" }.mkString("\n")
      }
    }
  }

  private def execListTheories(): String = {
    val buffers = org.gjt.sp.jedit.jEdit.getBufferManager().getBuffers().asScala
    val theories = buffers.filter(b => b.getPath != null && b.getPath.endsWith(".thy"))
      .map(b => java.io.File(b.getPath).getName).sorted
    if (theories.nonEmpty) theories.mkString("\n") else "No theory files open."
  }

  private def execSearchInTheory(args: Map[String, Any], view: View): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
      if (pattern.isEmpty) "Error: pattern required"
      else {
      val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
      findBuffer(normalized) match {
        case None => s"Theory '$theory' not found."
        case Some(buffer) =>
          val max = math.min(AssistantConstants.MAX_SEARCH_RESULTS, math.max(1, intArg(args, "max_results", 20)))
          val lines = buffer.getText(0, buffer.getLength).split("\n")
          val matches = lines.zipWithIndex
            .filter(_._1.toLowerCase.contains(pattern.toLowerCase))
            .take(max)
          if (matches.isEmpty) s"No matches for '$pattern' in $theory."
          else matches.map { case (l, i) => s"${i + 1}: ${l.trim}" }.mkString("\n")
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
      } catch { case _: Exception => }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execGetProofContext(view: View): String = {
    // getContextString must be called from a background thread (it dispatches to GUI internally)
    PrintContextAction.getContextString(view).getOrElse("No local facts in scope.")
  }

  private def execFindTheorems(args: Map[String, Any], view: View): String = {
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
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val max = math.min(AssistantConstants.MAX_FIND_THEOREMS_RESULTS, math.max(1, intArg(args, "max_results", 20)))
          val timeout = AssistantOptions.getFindTheoremsTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          val quoted = if (pattern.startsWith("\"")) pattern else s"\"$pattern\""

          GUI_Thread.later {
            IQIntegration.runFindTheoremsAsync(view, command, quoted, max, timeout, {
              case Right(results) =>
                result = if (results.nonEmpty) results.mkString("\n") else s"No theorems found for: $pattern"
                latch.countDown()
              case Left(err) =>
                result = s"Error: $err"
                latch.countDown()
            })
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "find_theorems timed out." else result
      }
    }
  }

  private def execVerifyProof(args: Map[String, Any], view: View): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getVerificationTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.verifyProofAsync(view, command, proof, timeout, {
              case IQIntegration.ProofSuccess(ms, _) => result = s"[ok] Proof verified (${ms}ms)"; latch.countDown()
              case IQIntegration.ProofFailure(err) => result = s"[FAIL] Failed: $err"; latch.countDown()
              case IQIntegration.ProofTimeout => result = "[FAIL] Timed out"; latch.countDown()
              case _ => result = "[FAIL] Unavailable"; latch.countDown()
            })
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
          commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getSledgehammerTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.runSledgehammerAsync(view, command, timeout, {
              case Right(results) if results.nonEmpty =>
                result = results.map(r => s"${r.proofMethod} (${r.timeMs}ms)").mkString("\n")
                latch.countDown()
              case Right(_) => result = "No proofs found."; latch.countDown()
              case Left(err) => result = s"Error: $err"; latch.countDown()
            })
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
          commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getNitpickTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.runQueryAsync(view, command, List("nitpick"), timeout, {
              case Right(output) => result = output; latch.countDown()
              case Left(err) => result = s"Error: $err"; latch.countDown()
            })
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
          commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getQuickcheckTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.runQueryAsync(view, command, List("quickcheck"), timeout, {
              case Right(output) => result = output; latch.countDown()
              case Left(err) => result = s"Error: $err"; latch.countDown()
            })
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
      } catch { case _: Exception => }
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
        CommandExtractor.getCommandAtOffset(buffer, offset).foreach(c => result = c)
      } catch { case _: Exception => }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execGetErrors(view: View): String = {
    val latch = new CountDownLatch(1)
    @volatile var result = "No errors at cursor position."
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition
        ExplainErrorAction.extractErrorAtOffset(buffer, offset).foreach(e => result = e)
      } catch { case _: Exception => }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execGetDefinitions(args: Map[String, Any], view: View): String = {
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
            commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
          } catch { case _: Exception => }
          cmdLatch.countDown()
        }
        cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

        commandOpt match {
          case None => "No Isabelle command at cursor position."
          case Some(command) =>
            ContextFetcher.fetchDefinitionsForNames(view, command, nameList, AssistantConstants.CONTEXT_FETCH_TIMEOUT)
              .getOrElse(s"No definitions found for: ${nameList.mkString(", ")}")
        }
      }
    }
  }

  private def execExecuteStep(args: Map[String, Any], view: View): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getProveStepTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.executeStepAsync(view, command, proof, timeout, {
              case Right(stepResult) =>
                val status = if (stepResult.complete) "[COMPLETE]" else s"[${stepResult.numSubgoals} subgoals]"
                result = s"$status\n${stepResult.stateText}"
                latch.countDown()
              case Left(err) =>
                result = s"[FAIL] $err"
                latch.countDown()
            })
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "Step execution timed out." else result
      }
    }
  }

  private def execTraceSimplifier(args: Map[String, Any], view: View): String = {
    val method = safeStringArg(args, "method", 50)
    val effectiveMethod = if (method.isEmpty || method == "simp") "simp" else method
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getTraceTimeout
          val depth = AssistantOptions.getTraceDepth
          val queryTimeoutMs = timeout * 1000L + AssistantConstants.TIMEOUT_BUFFER_MS
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.runQueryAsync(view, command, List(s"simp_trace $effectiveMethod $timeout $depth"), queryTimeoutMs, {
              case Right(output) => result = output; latch.countDown()
              case Left(err) => result = s"Error: $err"; latch.countDown()
            })
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
        ProofExtractor.getProofBlockAtOffset(buffer, offset).foreach(p => result = p)
      } catch { case _: Exception => }
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
        val selection = Option(view.getTextArea.getSelectedText).filter(_.trim.nonEmpty)
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

  private def execSearchAllTheories(args: Map[String, Any], view: View): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else {
      val maxTotal = math.min(200, math.max(1, intArg(args, "max_results", 50)))
      val buffers = org.gjt.sp.jedit.jEdit.getBufferManager().getBuffers().asScala
      val theories = buffers.filter(b => b.getPath != null && b.getPath.endsWith(".thy")).toList
      
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
        val truncated = if (allMatches.length >= maxTotal) s" (showing first $maxTotal)" else ""
        s"Found ${allMatches.length} matches$truncated:\n${allMatches.mkString("\n")}"
      } else s"No matches for '$pattern' in any open theory."
    }
  }

  private def execGetDependencies(args: Map[String, Any], view: View): String = {
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
        findBuffer(normalized) match {
          case None => s"Theory '$theory' not found in open buffers."
          case Some(buffer) =>
            val content = buffer.getText(0, buffer.getLength)
            val importPattern = """(?s)imports\s+(.*?)(?:\bbegin\b|\z)""".r
            importPattern.findFirstMatchIn(content) match {
              case Some(m) =>
                val tokenPattern = """"[^"]+"|[^\s"]+""".r
                val imports = tokenPattern.findAllIn(m.group(1)).toList.filter(_.nonEmpty)
                if (imports.nonEmpty) s"Dependencies of $theory:\n${imports.mkString("\n")}"
                else s"Theory '$theory' has no explicit imports."
              case None => s"No imports found in theory '$theory'."
            }
        }
    }
  }

  private def execGetWarnings(view: View): String = {
    val latch = new CountDownLatch(1)
    @volatile var result = "No warnings at cursor position."
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition
        extractWarningsAtOffset(buffer, offset).foreach(w => result = w)
      } catch { case _: Exception => }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execSetCursorPosition(args: Map[String, Any], view: View): String = {
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
            result = s"Error: line $line out of range (theory has $lineCount lines)"
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

  private def execEditTheory(args: Map[String, Any], view: View): String = {
    val operation = safeStringArg(args, "operation", 50).toLowerCase
    val text = safeStringArg(args, "text", MAX_STRING_ARG_LENGTH)
    val startLine = intArg(args, "start_line", -1)
    val endLine = intArg(args, "end_line", startLine)

    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        if (startLine <= 0) "Error: start_line must be a positive integer"
        else if (!Set("insert", "replace", "delete").contains(operation))
          s"Error: operation must be 'insert', 'replace', or 'delete', got '$operation'"
        else if ((operation == "insert" || operation == "replace") && text.isEmpty)
          s"Error: text required for $operation operation"
        else {
          val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
          findBuffer(normalized) match {
            case None => s"Theory '$theory' not found in open buffers."
            case Some(buffer) =>
              val latch = new CountDownLatch(1)
              @volatile var result = ""
              GUI_Thread.later {
                try {
                  val lineCount = buffer.getLineCount
                  if (startLine > lineCount) {
                    result = s"Error: start_line $startLine out of range (theory has $lineCount lines)"
                  } else if (endLine > lineCount) {
                    result = s"Error: end_line $endLine out of range (theory has $lineCount lines)"
                  } else {
                    buffer.beginCompoundEdit()
                    try {
                      operation match {
                        case "insert" =>
                          val offset = buffer.getLineStartOffset(startLine - 1)
                          buffer.insert(offset, text + "\n")
                          result = s"Inserted ${text.linesIterator.size} lines before line $startLine"
                        case "replace" =>
                          val startOffset = buffer.getLineStartOffset(startLine - 1)
                          val endOffset = buffer.getLineEndOffset(endLine - 1)
                          buffer.remove(startOffset, endOffset - startOffset)
                          buffer.insert(startOffset, text)
                          result = s"Replaced lines $startLine-$endLine"
                        case "delete" =>
                          val startOffset = buffer.getLineStartOffset(startLine - 1)
                          val endOffset = buffer.getLineEndOffset(endLine - 1)
                          buffer.remove(startOffset, endOffset - startOffset)
                          result = s"Deleted lines $startLine-$endLine"
                      }
                    } finally {
                      buffer.endCompoundEdit()
                    }
                  }
                } catch { case ex: Exception => result = s"Error: ${ex.getMessage}" }
                latch.countDown()
              }
              latch.await(AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC, TimeUnit.SECONDS)
              result
          }
        }
    }
  }

  private def execTryMethods(args: Map[String, Any], view: View): String = {
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
            commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
          } catch { case _: Exception => }
          cmdLatch.countDown()
        }
        cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

        commandOpt match {
          case None => "No Isabelle command at cursor position."
          case Some(command) =>
            val results = scala.collection.mutable.ListBuffer[String]()
            for (method <- methods) {
              val timeout = AssistantOptions.getVerificationTimeout
              val latch = new CountDownLatch(1)
              @volatile var methodResult = ""
              GUI_Thread.later {
                IQIntegration.verifyProofAsync(view, command, method, timeout, {
                  case IQIntegration.ProofSuccess(ms, _) => methodResult = s"[ok] $method (${ms}ms)"; latch.countDown()
                  case IQIntegration.ProofFailure(err) => methodResult = s"[FAIL] $method: ${err.take(50)}"; latch.countDown()
                  case IQIntegration.ProofTimeout => methodResult = s"[TIMEOUT] $method"; latch.countDown()
                  case _ => methodResult = s"[UNAVAILABLE] $method"; latch.countDown()
                })
              }
              latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
              results += (if (methodResult.isEmpty) s"[TIMEOUT] $method" else methodResult)
            }
            s"Tried ${methods.length} methods:\n${results.mkString("\n")}"
        }
      }
    }
  }

  private def execGetEntities(args: Map[String, Any], view: View): String = {
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
        findBuffer(normalized) match {
          case None => s"Theory '$theory' not found in open buffers."
          case Some(buffer) =>
            val latch = new CountDownLatch(1)
            @volatile var result = ""
            GUI_Thread.later {
              try {
                Document_Model.get_model(buffer).foreach { model =>
                  val snapshot = Document_Model.snapshot(model)
                  val node = snapshot.get_node(model.node_name)
                  val entities = scala.collection.mutable.ListBuffer[String]()
                  val defKeywords = Set("lemma", "theorem", "corollary", "proposition", "definition",
                    "abbreviation", "fun", "function", "primrec", "datatype", "type_synonym",
                    "inductive", "coinductive")
                  
                  for ((cmd, cmdOffset) <- node.command_iterator()) {
                    val keyword = cmd.span.name
                    if (defKeywords.contains(keyword)) {
                      val lineNum = buffer.getLineOfOffset(cmdOffset) + 1
                      val source = cmd.source.take(100).trim
                      val name = """(?:lemma|theorem|corollary|proposition|definition|abbreviation|fun|function|primrec|datatype|type_synonym|inductive|coinductive)\s+(\w+)""".r
                        .findFirstMatchIn(source).map(_.group(1)).getOrElse("(unnamed)")
                      entities += s"Line $lineNum: $keyword $name"
                    }
                  }
                  result = if (entities.nonEmpty) entities.mkString("\n") else "No entities found in theory."
                }
              } catch { case ex: Exception => result = s"Error: ${ex.getMessage}" }
              latch.countDown()
            }
            latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
            result
        }
    }
  }

  private def execWebSearch(args: Map[String, Any]): String = {
    val query = safeStringArg(args, "query", MAX_PATTERN_ARG_LENGTH)
    if (query.isEmpty) "Error: query required"
    else {
      val maxResults = math.min(10, math.max(1, intArg(args, "max_results", 5)))
      try {
        val encodedQuery = java.net.URLEncoder.encode(query, "UTF-8")
        val url = s"https://lite.duckduckgo.com/lite/?q=$encodedQuery"
        
        val client = java.net.http.HttpClient.newBuilder()
          .connectTimeout(java.time.Duration.ofSeconds(10))
          .build()
        val request = java.net.http.HttpRequest.newBuilder()
          .uri(java.net.URI.create(url))
          .timeout(java.time.Duration.ofSeconds(10))
          .GET()
          .build()
        
        val response = client.send(request, java.net.http.HttpResponse.BodyHandlers.ofString())
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

  private def execCreateTheory(args: Map[String, Any], view: View): String = {
    val name = safeStringArg(args, "name", 200)
    val imports = safeStringArg(args, "imports", 500)
    val content = safeStringArg(args, "content", MAX_STRING_ARG_LENGTH)
    
    if (name.isEmpty) "Error: name required"
    else if (THEORY_NAME_PATTERN.findFirstIn(name).isEmpty) s"Error: invalid theory name '$name'"
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
            val theoryContent = s"""theory $name imports $effectiveImports begin
              |
              |${if (content.nonEmpty) content + "\n\n" else ""}end
              |""".stripMargin
            
            java.nio.file.Files.write(java.nio.file.Paths.get(filePath), theoryContent.getBytes("UTF-8"))
            org.gjt.sp.jedit.jEdit.openFile(view, filePath)
            result = s"Created and opened $name.thy"
          }
        } catch { case ex: Exception => result = s"Error: ${ex.getMessage}" }
        latch.countDown()
      }
      latch.await(AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC, TimeUnit.SECONDS)
      result
    }
  }

  private def execOpenTheory(args: Map[String, Any], view: View): String = {
    val path = safeStringArg(args, "path", 1000)
    if (path.isEmpty) "Error: path required"
    else {
      val latch = new CountDownLatch(1)
      @volatile var result = ""
      GUI_Thread.later {
        try {
          val file = if (java.io.File(path).isAbsolute) java.io.File(path)
            else {
              val currentPath = view.getBuffer.getPath
              val currentDir = java.io.File(currentPath).getParent
              java.io.File(s"$currentDir/$path")
            }
          
          if (!file.exists()) {
            result = s"Error: file not found: ${file.getPath}"
          } else if (!file.getName.endsWith(".thy")) {
            result = s"Error: not a theory file (must end with .thy): ${file.getName}"
          } else {
            org.gjt.sp.jedit.jEdit.openFile(view, file.getPath)
            result = s"Opened ${file.getName}"
          }
        } catch { case ex: Exception => result = s"Error: ${ex.getMessage}" }
        latch.countDown()
      }
      latch.await(AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC, TimeUnit.SECONDS)
      result
    }
  }

  private def extractWarningsAtOffset(buffer: org.gjt.sp.jedit.buffer.JEditBuffer, offset: Int): Option[String] = {
    try {
      Document_Model.get_model(buffer).flatMap { model =>
        val snapshot = Document_Model.snapshot(model)
        val range = Text.Range(offset, offset + 1)
        val warnings = snapshot.cumulate(range, List.empty[String],
          Markup.Elements(Markup.WARNING_MESSAGE, Markup.WARNING, Markup.LEGACY), _ => {
            case (acc, Text.Info(_, XML.Elem(Markup(Markup.WARNING_MESSAGE, _), body))) =>
              Some(acc :+ XML.content(body))
            case (acc, Text.Info(_, XML.Elem(Markup(Markup.WARNING, _), body))) =>
              Some(acc :+ XML.content(body))
            case (acc, Text.Info(_, XML.Elem(Markup(Markup.LEGACY, _), body))) =>
              Some(acc :+ XML.content(body))
            case _ => None
          })
        val allWarnings = warnings.flatMap(_._2).distinct
        if (allWarnings.nonEmpty) Some(allWarnings.mkString("\n")) else None
      }
    } catch {
      case _: Exception => None
    }
  }

  private def findBuffer(normalized: String): Option[org.gjt.sp.jedit.buffer.JEditBuffer] =
    MenuContext.findTheoryBuffer(normalized)

  private def intArg(args: Map[String, Any], key: String, default: Int): Int = {
    args.get(key) match {
      case Some(n: Number) => n.intValue()
      case Some(s: String) => try { s.toInt } catch { case _: NumberFormatException => default }
      case _ => default
    }
  }
}
