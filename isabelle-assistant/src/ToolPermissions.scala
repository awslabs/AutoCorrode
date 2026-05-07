/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.{jEdit, View}

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
    
    def fromDisplayString(s: String): Option[PermissionLevel] = {
      s.trim.toLowerCase match {
        case "deny" => Some(Deny)
        case "ask always" => Some(AskAlways)
        case "ask at first use" => Some(AskAtFirstUse)
        case "allow" => Some(Allow)
        case _ => None
      }
    }
    
    val displayOptions: Array[String] = Array("Deny", "Ask Always", "Ask at First Use", "Allow")
  }

  // --- Permission Decision ---

  sealed trait PermissionDecision
  case object Allowed extends PermissionDecision
  case object Denied extends PermissionDecision
  case class NeedPrompt(
      toolId: ToolId,
      resource: Option[String],
      details: Option[String]
  ) extends PermissionDecision

  type PromptChoicesFn = (String, List[String], String, View) => Option[String]

  // --- Session State ---

  private val sessionLock = new Object()
  private var sessionAllowedTools: Set[ToolId] = Set.empty  // guarded by sessionLock
  private var sessionDeniedTools: Set[ToolId] = Set.empty   // guarded by sessionLock
  private var promptChoicesFn: PromptChoicesFn =            // guarded by sessionLock
    AssistantTools.promptUserWithChoices

  /** Clear session-scoped permission decisions. Called on chat clear and plugin stop. */
  def clearSession(): Unit = sessionLock.synchronized {
    sessionAllowedTools = Set.empty
    sessionDeniedTools = Set.empty
  }

  /** Snapshot of tool names session-allowed in the current session, sorted. */
  def sessionAllowedToolNames: List[String] = sessionLock.synchronized {
    sessionAllowedTools.toList.map(_.wireName).sorted
  }

  /** Snapshot of tool names session-denied in the current session, sorted. */
  def sessionDeniedToolNames: List[String] = sessionLock.synchronized {
    sessionDeniedTools.toList.map(_.wireName).sorted
  }

  private[assistant] def setSessionAllowedForTest(toolName: String): Unit =
    ToolId.fromWire(toolName).foreach(setSessionAllowed)

  private[assistant] def withPromptChoicesForTest[A](
      fn: PromptChoicesFn
  )(body: => A): A = {
    val previous = sessionLock.synchronized {
      val old = promptChoicesFn
      promptChoicesFn = fn
      old
    }
    try body
    finally sessionLock.synchronized { promptChoicesFn = previous }
  }

  private def isSessionAllowed(toolId: ToolId): Boolean = sessionLock.synchronized {
    sessionAllowedTools.contains(toolId)
  }

  private def isSessionDenied(toolId: ToolId): Boolean = sessionLock.synchronized {
    sessionDeniedTools.contains(toolId)
  }

  private def setSessionAllowed(toolId: ToolId): Unit = sessionLock.synchronized {
    sessionAllowedTools += toolId
    sessionDeniedTools -= toolId
  }

  private def setSessionDenied(toolId: ToolId): Unit = sessionLock.synchronized {
    sessionDeniedTools += toolId
    sessionAllowedTools -= toolId
  }

  // --- Default Permission Levels ---

  /** Default permission level for each tool. Consulted if no user override exists. */
  private val defaultPermissions: Map[ToolId, PermissionLevel] = Map(
    // Safe read-only operations → Allow
    ToolId.ReadTheory -> Allow,
    ToolId.ListTheories -> Allow,
    ToolId.SearchInTheory -> Allow,
    ToolId.SearchTheories -> Allow,
    ToolId.SearchAllTheories -> Allow,
    ToolId.GetGoalState -> Allow,
    ToolId.GetSubgoal -> Allow,
    ToolId.GetProofContext -> Allow,
    ToolId.GetCommandText -> Allow,
    ToolId.GetType -> Allow,
    ToolId.GetErrors -> Allow,
    ToolId.GetDiagnostics -> Allow,
    ToolId.GetWarnings -> Allow,
    ToolId.GetContextInfo -> Allow,
    ToolId.GetProofBlock -> Allow,
    ToolId.GetProofOutline -> Allow,
    ToolId.GetDependencies -> Allow,
    ToolId.GetEntities -> Allow,
    ToolId.GetFileStats -> Allow,
    ToolId.GetProcessingStatus -> Allow,
    ToolId.GetSorryPositions -> Allow,
    ToolId.SetCursorPosition -> Allow,
    
    // I/Q-dependent verification (computational but non-destructive) → AskAtFirstUse
    ToolId.VerifyProof -> AskAtFirstUse,
    ToolId.ExecuteStep -> AskAtFirstUse,
    ToolId.TryMethods -> AskAtFirstUse,
    ToolId.FindTheorems -> AskAtFirstUse,
    ToolId.GetDefinitions -> AskAtFirstUse,
    ToolId.RunSledgehammer -> AskAtFirstUse,
    ToolId.RunNitpick -> AskAtFirstUse,
    ToolId.RunQuickcheck -> AskAtFirstUse,
    ToolId.FindCounterexample -> AskAtFirstUse,
    ToolId.TraceSimplifier -> AskAtFirstUse,
    
    // Side effects (file creation, modification, network) → AskAlways
    ToolId.EditTheory -> AskAlways,
    ToolId.CreateTheory -> AskAlways,
    ToolId.OpenTheory -> AskAlways,
    ToolId.WebSearch -> AskAlways,
    
    // Meta-tool for user interaction → Always Allow (exempt from permission checks)
    ToolId.AskUser -> Allow,
    
    // Task list management → Always Allow (pure in-memory state, no side effects)
    ToolId.TaskListAdd -> Allow,
    ToolId.TaskListDone -> Allow,
    ToolId.TaskListIrrelevant -> Allow,
    ToolId.TaskListNext -> Allow,
    ToolId.TaskListShow -> Allow,
    ToolId.TaskListGet -> Allow,
    
    // Memory management → Allow for read/add, AskAtFirstUse for delete
    ToolId.MemoryAdd -> Allow,
    ToolId.MemoryDelete -> AskAtFirstUse,
    ToolId.MemoryDeleteTopic -> AskAtFirstUse,
    ToolId.MemoryListTopics -> Allow,
    ToolId.MemoryList -> Allow,
    ToolId.MemoryGet -> Allow,
    ToolId.MemorySearch -> Allow,
    
    // Planning agent → Allow (read-only exploration, no side effects)
    ToolId.PlanApproach -> Allow
  )
  require(
    defaultPermissions.keySet == ToolId.values.toSet,
    "defaultPermissions must cover all ToolId values."
  )

  /** Human-readable description of what each tool does (for permission prompts). */
  private val toolDescriptionsById: Map[ToolId, String] = Map(
    ToolId.ReadTheory -> "read the content of theory files",
    ToolId.ListTheories -> "list all open theory files",
    ToolId.SearchInTheory -> "search for text patterns in theory files",
    ToolId.SearchTheories -> "search for text patterns in theory files",
    ToolId.SearchAllTheories -> "search for text patterns across all theory files",
    ToolId.GetGoalState -> "check the current proof goal state",
    ToolId.GetSubgoal -> "extract a single subgoal by index",
    ToolId.GetProofContext -> "view local facts and assumptions",
    ToolId.GetCommandText -> "read Isabelle command text",
    ToolId.GetType -> "get type information",
    ToolId.GetErrors -> "read error messages",
    ToolId.GetDiagnostics -> "read error or warning messages",
    ToolId.GetWarnings -> "read warning messages",
    ToolId.GetContextInfo -> "analyze proof context",
    ToolId.GetProofBlock -> "read complete proof blocks",
    ToolId.GetProofOutline -> "read proof structure outline",
    ToolId.GetDependencies -> "read theory dependencies",
    ToolId.GetEntities -> "list definitions and lemmas",
    ToolId.GetFileStats -> "get file statistics without reading content",
    ToolId.GetProcessingStatus -> "check PIDE processing status",
    ToolId.GetSorryPositions -> "find incomplete proofs (sorry/oops)",
    ToolId.SetCursorPosition -> "move the cursor position",
    ToolId.WebSearch -> "search the web for documentation and information",
    ToolId.VerifyProof -> "verify proof methods using Isabelle",
    ToolId.ExecuteStep -> "execute proof steps",
    ToolId.TryMethods -> "try multiple proof methods",
    ToolId.FindTheorems -> "search for theorems",
    ToolId.GetDefinitions -> "look up definitions",
    ToolId.RunSledgehammer -> "run automated theorem provers",
    ToolId.RunNitpick -> "search for counterexamples",
    ToolId.RunQuickcheck -> "test with random examples",
    ToolId.FindCounterexample -> "search for counterexamples",
    ToolId.TraceSimplifier -> "trace simplifier operations",
    ToolId.EditTheory -> "modify theory file content",
    ToolId.CreateTheory -> "create new theory files",
    ToolId.OpenTheory -> "open existing theory files",
    ToolId.AskUser -> "ask you questions",
    ToolId.TaskListAdd -> "add items to the task list",
    ToolId.TaskListDone -> "mark task list items as done",
    ToolId.TaskListIrrelevant -> "mark task list items as irrelevant",
    ToolId.TaskListNext -> "retrieve the next pending task list item",
    ToolId.TaskListShow -> "show the current task list",
    ToolId.TaskListGet -> "retrieve a specific task list item",
    ToolId.MemoryAdd -> "add persistent memories to the knowledge base",
    ToolId.MemoryDelete -> "delete specific memories",
    ToolId.MemoryDeleteTopic -> "delete entire memory topics",
    ToolId.MemoryListTopics -> "list all memory topics",
    ToolId.MemoryList -> "list memories in a topic",
    ToolId.MemoryGet -> "retrieve specific memory details",
    ToolId.MemorySearch -> "search for memories",
    ToolId.PlanApproach -> "launch a planning agent to analyze problems and generate implementation plans"
  )
  require(
    toolDescriptionsById.keySet == ToolId.values.toSet,
    "toolDescriptionsById must cover all ToolId values."
  )

  private[assistant] val toolDescriptions: Map[String, String] =
    toolDescriptionsById.map { case (id, description) =>
      id.wireName -> description
    }


  // --- Tool Name Formatting ---

  /** Convert snake_case tool name to user-friendly PascalCase display name. */
  private def toolNameToDisplay(toolId: ToolId): String =
    ToolId.displayName(toolId).replace(" ", "")

  // --- Resource Extraction ---

  /** Extract a displayable resource identifier from tool arguments (e.g., theory name, URL). */
  private def extractResource(
      toolId: ToolId,
      args: ResponseParser.ToolArgs
  ): Option[String] = {
    toolId match {
      case ToolId.ReadTheory | ToolId.SearchInTheory | ToolId.EditTheory |
          ToolId.GetEntities | ToolId.GetDependencies =>
        args.get("theory").map(ResponseParser.toolValueToString)
      case ToolId.CreateTheory =>
        args.get("name").map(n => s"${ResponseParser.toolValueToString(n)}.thy")
      case ToolId.OpenTheory =>
        args.get("path").map(ResponseParser.toolValueToString)
      case _ => None
    }
  }

  private def summarizeArgs(
      args: ResponseParser.ToolArgs,
      maxPairs: Int = 4,
      maxValueLength: Int = 80
  ): Option[String] = {
    if (args.isEmpty) return None
    val summary = args.toList.sortBy(_._1).take(maxPairs).map { case (k, v) =>
      if (ToolArgs.isSensitiveArgName(k)) "***=***"
      else {
        val raw = ResponseParser.toolValueToDisplay(v).replace('\n', ' ').trim
        val value =
          if (raw.length > maxValueLength) raw.take(maxValueLength) + "…" else raw
        s"$k=$value"
      }
    }
    Some(summary.mkString(", "))
  }

  // --- Configuration Persistence ---

  /** Get the configured permission level for a tool from jEdit properties. */
  def getConfiguredLevel(toolName: String): PermissionLevel = {
    ToolId.fromWire(toolName).map(getConfiguredLevel).getOrElse(AskAtFirstUse)
  }

  def getConfiguredLevel(toolId: ToolId): PermissionLevel = {
    // ask_user is always Allow and cannot be changed (would create recursion)
    if (toolId == ToolId.AskUser) return Allow

    val key = s"assistant.permissions.tool.${toolId.wireName}"
    val value = jEdit.getProperty(key, "")
    PermissionLevel
      .fromString(value)
      .getOrElse(defaultPermissions.getOrElse(toolId, AskAtFirstUse))
  }

  /** Set the permission level for a tool in jEdit properties. */
  def setConfiguredLevel(toolName: String, level: PermissionLevel): Unit = {
    ToolId.fromWire(toolName).foreach(toolId => setConfiguredLevel(toolId, level))
  }

  def setConfiguredLevel(toolId: ToolId, level: PermissionLevel): Unit = {
    if (toolId == ToolId.AskUser) return // ask_user is locked to Allow
    val key = s"assistant.permissions.tool.${toolId.wireName}"
    jEdit.setProperty(key, level.toConfigString)
  }

  /** Reset all tool permissions to defaults. */
  def resetToDefaults(): Unit = {
    for ((toolId, level) <- defaultPermissions if toolId != ToolId.AskUser) {
      setConfiguredLevel(toolId, level)
    }
  }

  /** Get the default permission level for a tool (before any user customization). */
  def getDefaultLevel(toolId: ToolId): PermissionLevel =
    defaultPermissions.getOrElse(toolId, AskAtFirstUse)

  /** Get human-readable description for a tool by ToolId. */
  def getToolDescription(toolId: ToolId): String =
    toolDescriptionsById.getOrElse(toolId, "perform this action")

  /** Get all tool names with their configured or default permission levels. */
  def getAllToolPermissions: List[(String, PermissionLevel)] = {
    AssistantTools.tools.map { tool =>
      (tool.name, getConfiguredLevel(tool.id))
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
    ToolId
      .fromWire(toolName)
      .map(checkPermission(_, args))
      .getOrElse(Denied)
  }

  def checkPermission(
      toolId: ToolId,
      args: ResponseParser.ToolArgs
  ): PermissionDecision = {
    // 1. Get configured level FIRST - this takes precedence
    val level = getConfiguredLevel(toolId)

    // 2. Apply policy based on configured level
    level match {
      case Deny => Denied  // Absolute denial
      case Allow => Allowed  // Absolute permission
      case AskAtFirstUse =>
        // Check session state for AskAtFirstUse
        if (isSessionDenied(toolId)) Denied
        else if (isSessionAllowed(toolId)) Allowed
        else
          NeedPrompt(
            toolId,
            extractResource(toolId, args),
            summarizeArgs(args)
          )
      case AskAlways =>
        // AskAlways MUST always prompt - never respect session state
        // This ensures the user is asked every single time
        NeedPrompt(toolId, extractResource(toolId, args), summarizeArgs(args))
    }
  }

  /**
   * Prompt the user for permission using the same UI as ask_user.
   * Blocks until user responds or times out.
   * 
   * @param toolName The tool requesting permission
   * @param resource Optional resource identifier (e.g., theory name)
   * @param details Optional argument summary (sanitized for display)
   * @param view The current jEdit view
   * @return PermissionDecision (Allowed or Denied)
   */
  def promptUser(
      toolName: String,
      resource: Option[String],
      details: Option[String],
      view: View
  ): PermissionDecision =
    ToolId
      .fromWire(toolName)
      .map(promptUser(_, resource, details, view))
      .getOrElse(Denied)

  def promptUser(
      toolId: ToolId,
      resource: Option[String],
      details: Option[String],
      view: View
  ): PermissionDecision = {
    val toolName = toolId.wireName
    val displayName = toolNameToDisplay(toolId)
    val resourceText = resource.map(r => s" on '$r'").getOrElse("")
    val action = toolDescriptionsById.getOrElse(toolId, "perform this action")
    val question = s"Tool '$displayName' wants to $action$resourceText. Allow now?"
    
    val toolDef = AssistantTools.toolDefinition(toolId)
    val level = getConfiguredLevel(toolId)
    val contextLines =
      List(
        toolDef.map(_.description).filter(_.nonEmpty),
        details.map(d => s"Arguments: $d"),
        Some(s"Policy: ${level.toDisplayString}")
      ).flatten
    val context = contextLines.mkString("\n")
    // AskAlways is, by contract, "always prompt": session-wide allow decisions
    // are never consulted for this level (see checkPermission), so offering
    // "Allow (for this session)" would be a lie — the user would be asked
    // again on the very next call regardless. Offer only the honest choices.
    val options =
      if (level == AskAlways)
        List("Allow Once", "Deny Once")
      else
        List(
          "Allow (for this session)",
          "Allow Once",
          "Deny (for this session)"
        )
    
    // Capture the prompt function under lock to avoid race conditions
    val choicesFn = sessionLock.synchronized { promptChoicesFn }
    
    // Reuse the exact same prompt mechanism as execAskUser
    choicesFn(question, options, context, view) match {
      case Some(choice) =>
        choice match {
          case "Allow (for this session)" =>
            setSessionAllowed(toolId)
            ErrorHandler.safeLog(s"[Permissions] User allowed '$toolName' for session")
            Allowed
          case "Allow Once" =>
            ErrorHandler.safeLog(s"[Permissions] User allowed '$toolName' once")
            Allowed
          case "Deny (for this session)" =>
            setSessionDenied(toolId)
            ErrorHandler.safeLog(s"[Permissions] User denied '$toolName' for session")
            Denied
          case "Deny Once" =>
            ErrorHandler.safeLog(s"[Permissions] User denied '$toolName' once")
            Denied
          case _ =>
            ErrorHandler.safeLog(s"[Permissions] Unexpected choice for '$toolName': $choice")
            Denied
        }
      case None =>
        // Timeout or cancellation
        ErrorHandler.safeLog(s"[Permissions] User did not respond, denying '$toolName'")
        Denied
    }
  }

  // --- Filtered Tool List for LLM ---

  /**
   * Get the list of tools that should be sent to the LLM.
   * Excludes tools with Deny permission level.
   */
  def getVisibleTools: List[AssistantTools.ToolDef] = {
    AssistantTools.tools.filter(tool => getConfiguredLevel(tool.id) != Deny)
  }
}