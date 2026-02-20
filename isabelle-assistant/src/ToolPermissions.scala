/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.{jEdit, View}
import java.util.concurrent.{CountDownLatch, TimeUnit}

/**
 * Capability-based permission system for LLM tool use.
 * 
 * Provides four permission levels (Deny, AskAlways, AskAtFirstUse, Allow)
 * with per-tool defaults, session-scoped memory, and user prompting via
 * the same UI mechanism as the ask_user tool.
 */
object ToolPermissions {

  // --- Permission Levels ---

  sealed trait PermissionLevel {
    def toConfigString: String = this match {
      case Deny => "Deny"
      case AskAlways => "AskAlways"
      case AskAtFirstUse => "AskAtFirstUse"
      case Allow => "Allow"
    }
    
    def toDisplayString: String = this match {
      case Deny => "Deny"
      case AskAlways => "Ask Always"
      case AskAtFirstUse => "Ask at First Use"
      case Allow => "Allow"
    }
  }
  case object Deny extends PermissionLevel
  case object AskAlways extends PermissionLevel
  case object AskAtFirstUse extends PermissionLevel
  case object Allow extends PermissionLevel

  object PermissionLevel {
    def fromString(s: String): Option[PermissionLevel] = s match {
      case "Deny" => Some(Deny)
      case "AskAlways" => Some(AskAlways)
      case "AskAtFirstUse" => Some(AskAtFirstUse)
      case "Allow" => Some(Allow)
      case _ => None
    }
    
    def fromDisplayString(s: String): Option[PermissionLevel] = s match {
      case "Deny" => Some(Deny)
      case "Ask Always" => Some(AskAlways)
      case "Ask at First Use" => Some(AskAtFirstUse)
      case "Allow" => Some(Allow)
      case _ => None
    }
    
    val displayOptions: Array[String] = Array("Deny", "Ask Always", "Ask at First Use", "Allow")
  }

  // --- Permission Decision ---

  sealed trait PermissionDecision
  case object Allowed extends PermissionDecision
  case object Denied extends PermissionDecision
  case class NeedPrompt(toolName: String, resource: Option[String]) extends PermissionDecision

  // --- Session State ---

  private val sessionLock = new Object()
  @volatile private var sessionAllowedTools: Set[String] = Set.empty
  @volatile private var sessionDeniedTools: Set[String] = Set.empty

  /** Clear session-scoped permission decisions. Called on chat clear and plugin stop. */
  def clearSession(): Unit = sessionLock.synchronized {
    sessionAllowedTools = Set.empty
    sessionDeniedTools = Set.empty
  }

  private[assistant] def setSessionAllowedForTest(toolName: String): Unit =
    setSessionAllowed(toolName)

  private def isSessionAllowed(toolName: String): Boolean =
    sessionAllowedTools.contains(toolName)

  private def isSessionDenied(toolName: String): Boolean =
    sessionDeniedTools.contains(toolName)

  private def setSessionAllowed(toolName: String): Unit = sessionLock.synchronized {
    sessionAllowedTools += toolName
    sessionDeniedTools -= toolName
  }

  private def setSessionDenied(toolName: String): Unit = sessionLock.synchronized {
    sessionDeniedTools += toolName
    sessionAllowedTools -= toolName
  }

  // --- Default Permission Levels ---

  /** Default permission level for each tool. Consulted if no user override exists. */
  private val defaultPermissions: Map[String, PermissionLevel] = Map(
    // Safe read-only operations → Allow
    "read_theory" -> Allow,
    "list_theories" -> Allow,
    "search_in_theory" -> Allow,
    "search_all_theories" -> Allow,
    "get_goal_state" -> Allow,
    "get_proof_context" -> Allow,
    "get_command_text" -> Allow,
    "get_type" -> Allow,
    "get_errors" -> Allow,
    "get_warnings" -> Allow,
    "get_context_info" -> Allow,
    "get_proof_block" -> Allow,
    "get_dependencies" -> Allow,
    "get_entities" -> Allow,
    "set_cursor_position" -> Allow,
    
    // I/Q-dependent verification (computational but non-destructive) → AskAtFirstUse
    "verify_proof" -> AskAtFirstUse,
    "execute_step" -> AskAtFirstUse,
    "try_methods" -> AskAtFirstUse,
    "find_theorems" -> AskAtFirstUse,
    "get_definitions" -> AskAtFirstUse,
    "run_sledgehammer" -> AskAtFirstUse,
    "run_nitpick" -> AskAtFirstUse,
    "run_quickcheck" -> AskAtFirstUse,
    "trace_simplifier" -> AskAtFirstUse,
    
    // Side effects (file creation, modification, network) → AskAlways
    "edit_theory" -> AskAlways,
    "create_theory" -> AskAlways,
    "open_theory" -> AskAlways,
    "web_search" -> AskAlways,
    
    // Meta-tool for user interaction → Always Allow (exempt from permission checks)
    "ask_user" -> Allow,
    
    // Task list management → Always Allow (pure in-memory state, no side effects)
    "task_list_add" -> Allow,
    "task_list_done" -> Allow,
    "task_list_irrelevant" -> Allow,
    "task_list_next" -> Allow,
    "task_list_show" -> Allow,
    "task_list_get" -> Allow
  )

  /** Human-readable description of what each tool does (for permission prompts). */
  private[assistant] val toolDescriptions: Map[String, String] = Map(
    "read_theory" -> "read the content of theory files",
    "list_theories" -> "list all open theory files",
    "search_in_theory" -> "search for text patterns in theory files",
    "search_all_theories" -> "search for text patterns across all theory files",
    "get_goal_state" -> "check the current proof goal state",
    "get_proof_context" -> "view local facts and assumptions",
    "get_command_text" -> "read Isabelle command text",
    "get_type" -> "get type information",
    "get_errors" -> "read error messages",
    "get_warnings" -> "read warning messages",
    "get_context_info" -> "analyze proof context",
    "get_proof_block" -> "read complete proof blocks",
    "get_dependencies" -> "read theory dependencies",
    "get_entities" -> "list definitions and lemmas",
    "set_cursor_position" -> "move the cursor position",
    "verify_proof" -> "verify proof methods using Isabelle",
    "execute_step" -> "execute proof steps",
    "try_methods" -> "try multiple proof methods",
    "find_theorems" -> "search for theorems",
    "get_definitions" -> "look up definitions",
    "run_sledgehammer" -> "run automated theorem provers",
    "run_nitpick" -> "search for counterexamples",
    "run_quickcheck" -> "test with random examples",
    "trace_simplifier" -> "trace simplifier operations",
    "edit_theory" -> "modify theory file content",
    "create_theory" -> "create new theory files",
    "open_theory" -> "open existing theory files",
    "web_search" -> "search the web",
    "ask_user" -> "ask you questions"
  )

  // --- Tool Name Formatting ---

  /** Convert snake_case tool name to user-friendly PascalCase display name. */
  private def toolNameToDisplay(toolName: String): String = {
    toolName.split("_").map(_.capitalize).mkString
  }

  // --- Resource Extraction ---

  /** Extract a displayable resource identifier from tool arguments (e.g., theory name, URL). */
  private def extractResource(toolName: String, args: ResponseParser.ToolArgs): Option[String] = {
    toolName match {
      case "read_theory" | "search_in_theory" | "edit_theory" | 
           "get_entities" | "get_dependencies" =>
        args.get("theory").map(ResponseParser.toolValueToString)
      case "create_theory" =>
        args.get("name").map(n => s"${ResponseParser.toolValueToString(n)}.thy")
      case "open_theory" =>
        args.get("path").map(ResponseParser.toolValueToString)
      case "web_search" =>
        args.get("query").map(q => s"query: ${ResponseParser.toolValueToString(q)}")
      case _ => None
    }
  }

  // --- Configuration Persistence ---

  /** Get the configured permission level for a tool from jEdit properties. */
  def getConfiguredLevel(toolName: String): PermissionLevel = {
    // ask_user is always Allow and cannot be changed (would create recursion)
    if (toolName == "ask_user") return Allow
    
    val key = s"assistant.permissions.tool.$toolName"
    val value = jEdit.getProperty(key, "")
    PermissionLevel.fromString(value).getOrElse(
      defaultPermissions.getOrElse(toolName, AskAtFirstUse)
    )
  }

  /** Set the permission level for a tool in jEdit properties. */
  def setConfiguredLevel(toolName: String, level: PermissionLevel): Unit = {
    if (toolName == "ask_user") return // ask_user is locked to Allow
    val key = s"assistant.permissions.tool.$toolName"
    jEdit.setProperty(key, level.toConfigString)
  }

  /** Reset all tool permissions to defaults. */
  def resetToDefaults(): Unit = {
    for ((toolName, level) <- defaultPermissions if toolName != "ask_user") {
      setConfiguredLevel(toolName, level)
    }
  }

  /** Get all tool names with their configured or default permission levels. */
  def getAllToolPermissions: List[(String, PermissionLevel)] = {
    AssistantTools.tools.map { tool =>
      (tool.name, getConfiguredLevel(tool.name))
    }
  }

  // --- Permission Check ---

  /**
   * Check if a tool is permitted to execute.
   * 
   * @param toolName The name of the tool
   * @param args The tool arguments (for resource extraction)
   * @return PermissionDecision
   */
  def checkPermission(toolName: String, args: ResponseParser.ToolArgs): PermissionDecision = {
    // 1. Check session-scoped denials
    if (isSessionDenied(toolName)) return Denied

    // 2. Get configured level
    val level = getConfiguredLevel(toolName)

    // 3. Apply policy
    level match {
      case Deny => Denied
      case Allow => Allowed
      case AskAtFirstUse =>
        if (isSessionAllowed(toolName)) Allowed
        else NeedPrompt(toolName, extractResource(toolName, args))
      case AskAlways =>
        NeedPrompt(toolName, extractResource(toolName, args))
    }
  }

  /**
   * Prompt the user for permission using the same UI as ask_user.
   * Blocks until user responds or times out.
   * 
   * @param toolName The tool requesting permission
   * @param resource Optional resource identifier (e.g., theory name)
   * @param view The current jEdit view
   * @return PermissionDecision (Allowed or Denied)
   */
  def promptUser(toolName: String, resource: Option[String], view: View): PermissionDecision = {
    val displayName = toolNameToDisplay(toolName)
    val resourceText = resource.map(r => s" on '$r'").getOrElse("")
    val action = toolDescriptions.getOrElse(toolName, "perform this action")
    val question = s"Tool '$displayName' wants to $action$resourceText. Allow?"
    
    val toolDef = AssistantTools.tools.find(_.name == toolName)
    val context = toolDef.map(_.description).getOrElse("")
    val level = getConfiguredLevel(toolName)
    val options =
      if (level == AskAlways)
        List("Allow Once", "Deny (for this session)")
      else
        List(
          "Allow (for this session)",
          "Allow Once",
          "Deny (for this session)"
        )
    
    // Reuse the exact same prompt mechanism as execAskUser
    AssistantTools.promptUserWithChoices(question, options, context, view) match {
      case Some(choice) =>
        choice match {
          case "Allow (for this session)" =>
            setSessionAllowed(toolName)
            Output.writeln(s"[Permissions] User allowed '$toolName' for session")
            Allowed
          case "Allow Once" =>
            Output.writeln(s"[Permissions] User allowed '$toolName' once")
            Allowed
          case "Deny (for this session)" =>
            setSessionDenied(toolName)
            Output.writeln(s"[Permissions] User denied '$toolName' for session")
            Denied
          case _ =>
            Output.writeln(s"[Permissions] Unexpected choice for '$toolName': $choice")
            Denied
        }
      case None =>
        // Timeout or cancellation
        Output.writeln(s"[Permissions] User did not respond, denying '$toolName'")
        Denied
    }
  }

  // --- Filtered Tool List for LLM ---

  /**
   * Get the list of tools that should be sent to the LLM.
   * Excludes tools with Deny permission level.
   */
  def getVisibleTools: List[AssistantTools.ToolDef] = {
    AssistantTools.tools.filter(tool => getConfiguredLevel(tool.name) != Deny)
  }
}
