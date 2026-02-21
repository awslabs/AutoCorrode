/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.{jEdit, View}
import java.util.Locale

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
  case class NeedPrompt(
      toolName: String,
      resource: Option[String],
      details: Option[String]
  ) extends PermissionDecision

  type PromptChoicesFn = (String, List[String], String, View) => Option[String]

  // --- Session State ---

  private val sessionLock = new Object()
  @volatile private var sessionAllowedTools: Set[ToolId] = Set.empty
  @volatile private var sessionDeniedTools: Set[ToolId] = Set.empty
  @volatile private var promptChoicesFn: PromptChoicesFn =
    AssistantTools.promptUserWithChoices

  /** Clear session-scoped permission decisions. Called on chat clear and plugin stop. */
  def clearSession(): Unit = sessionLock.synchronized {
    sessionAllowedTools = Set.empty
    sessionDeniedTools = Set.empty
  }

  private[assistant] def setSessionAllowedForTest(toolName: String): Unit =
    ToolId.fromWire(toolName).foreach(setSessionAllowed)

  private[assistant] def withPromptChoicesForTest[A](
      fn: PromptChoicesFn
  )(body: => A): A = {
    val previous = promptChoicesFn
    promptChoicesFn = fn
    try body
    finally promptChoicesFn = previous
  }

  private def isSessionAllowed(toolId: ToolId): Boolean =
    sessionAllowedTools.contains(toolId)

  private def isSessionDenied(toolId: ToolId): Boolean =
    sessionDeniedTools.contains(toolId)

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
    ToolId.SearchAllTheories -> Allow,
    ToolId.GetGoalState -> Allow,
    ToolId.GetProofContext -> Allow,
    ToolId.GetCommandText -> Allow,
    ToolId.GetType -> Allow,
    ToolId.GetErrors -> Allow,
    ToolId.GetWarnings -> Allow,
    ToolId.GetContextInfo -> Allow,
    ToolId.GetProofBlock -> Allow,
    ToolId.GetDependencies -> Allow,
    ToolId.GetEntities -> Allow,
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
    ToolId.TaskListGet -> Allow
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
    ToolId.SearchAllTheories -> "search for text patterns across all theory files",
    ToolId.GetGoalState -> "check the current proof goal state",
    ToolId.GetProofContext -> "view local facts and assumptions",
    ToolId.GetCommandText -> "read Isabelle command text",
    ToolId.GetType -> "get type information",
    ToolId.GetErrors -> "read error messages",
    ToolId.GetWarnings -> "read warning messages",
    ToolId.GetContextInfo -> "analyze proof context",
    ToolId.GetProofBlock -> "read complete proof blocks",
    ToolId.GetDependencies -> "read theory dependencies",
    ToolId.GetEntities -> "list definitions and lemmas",
    ToolId.SetCursorPosition -> "move the cursor position",
    ToolId.VerifyProof -> "verify proof methods using Isabelle",
    ToolId.ExecuteStep -> "execute proof steps",
    ToolId.TryMethods -> "try multiple proof methods",
    ToolId.FindTheorems -> "search for theorems",
    ToolId.GetDefinitions -> "look up definitions",
    ToolId.RunSledgehammer -> "run automated theorem provers",
    ToolId.RunNitpick -> "search for counterexamples",
    ToolId.RunQuickcheck -> "test with random examples",
    ToolId.TraceSimplifier -> "trace simplifier operations",
    ToolId.EditTheory -> "modify theory file content",
    ToolId.CreateTheory -> "create new theory files",
    ToolId.OpenTheory -> "open existing theory files",
    ToolId.WebSearch -> "search the web",
    ToolId.AskUser -> "ask you questions",
    ToolId.TaskListAdd -> "add items to the task list",
    ToolId.TaskListDone -> "mark task list items as done",
    ToolId.TaskListIrrelevant -> "mark task list items as irrelevant",
    ToolId.TaskListNext -> "retrieve the next pending task list item",
    ToolId.TaskListShow -> "show the current task list",
    ToolId.TaskListGet -> "retrieve a specific task list item"
  )
  require(
    toolDescriptionsById.keySet == ToolId.values.toSet,
    "toolDescriptionsById must cover all ToolId values."
  )

  private[assistant] val toolDescriptions: Map[String, String] =
    toolDescriptionsById.map { case (id, description) =>
      id.wireName -> description
    }

  private def safeLog(message: String): Unit = {
    try Output.writeln(message)
    catch { case _: Throwable => () }
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
      case ToolId.WebSearch =>
        args.get("query").map(q => s"query: ${ResponseParser.toolValueToString(q)}")
      case _ => None
    }
  }

  private val sensitiveArgTokens =
    Set("token", "secret", "password", "auth", "credential", "api_key")

  private def isSensitiveArg(argName: String): Boolean = {
    val lowered = argName.toLowerCase(Locale.ROOT)
    sensitiveArgTokens.exists(token => lowered.contains(token))
  }

  private def summarizeArgs(
      args: ResponseParser.ToolArgs,
      maxPairs: Int = 4,
      maxValueLength: Int = 80
  ): Option[String] = {
    if (args.isEmpty) return None
    val summary = args.toList.sortBy(_._1).take(maxPairs).map { case (k, v) =>
      val value =
        if (isSensitiveArg(k)) "***"
        else {
          val raw = ResponseParser.toolValueToDisplay(v).replace('\n', ' ').trim
          if (raw.length > maxValueLength) raw.take(maxValueLength) + "..." else raw
        }
      s"$k=$value"
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
    // 1. Check session-scoped denials
    if (isSessionDenied(toolId)) return Denied

    // 2. Get configured level
    val level = getConfiguredLevel(toolId)

    // 3. Apply policy
    level match {
      case Deny => Denied
      case Allow => Allowed
      case AskAtFirstUse =>
        if (isSessionAllowed(toolId)) Allowed
        else
          NeedPrompt(
            toolId.wireName,
            extractResource(toolId, args),
            summarizeArgs(args)
          )
      case AskAlways =>
        NeedPrompt(toolId.wireName, extractResource(toolId, args), summarizeArgs(args))
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
    promptChoicesFn(question, options, context, view) match {
      case Some(choice) =>
        choice match {
          case "Allow (for this session)" =>
            setSessionAllowed(toolId)
            safeLog(s"[Permissions] User allowed '$toolName' for session")
            Allowed
          case "Allow Once" =>
            safeLog(s"[Permissions] User allowed '$toolName' once")
            Allowed
          case "Deny (for this session)" =>
            setSessionDenied(toolId)
            safeLog(s"[Permissions] User denied '$toolName' for session")
            Denied
          case _ =>
            safeLog(s"[Permissions] Unexpected choice for '$toolName': $choice")
            Denied
        }
      case None =>
        // Timeout or cancellation
        safeLog(s"[Permissions] User did not respond, denying '$toolName'")
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
