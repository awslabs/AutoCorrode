/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/**
 * Renders HTML widgets for interactive chat elements (task lists, user prompts, tool results).
 * Extracted from AssistantTools to separate rendering concerns from tool execution.
 *
 * All cards route through `UIDesign.card` so elevation, radius, padding, and the
 * white background (required by `MarkdownRenderer.renderLatex`) stay consistent.
 * Font sizes, spacing, and radius come from `UIDesign` tokens — do not hand-pick
 * literals.
 */
object WidgetRenderer {

  /** Convert snake_case tool name to PascalCase for display.
    * Example: "read_theory" → "ReadTheory"
    */
  private def toolNameToDisplay(wireName: String): String =
    wireName.split("_").map(_.capitalize).mkString

  /** Word-aware truncation: cut on the nearest whitespace before `max` and
    * append an ellipsis. Falls back to a hard cut if there is no whitespace. */
  private def truncateWord(s: String, max: Int): String = {
    if (s.length <= max) s
    else {
      val cut = s.take(max)
      val lastSpace = cut.lastIndexWhere(_.isWhitespace)
      val base =
        if (lastSpace > max / 2) cut.substring(0, lastSpace).trim
        else cut.trim
      base + "…"
    }
  }

  /** Render HTML widget for a tool result with smart truncation.
    *
    * Creates a styled card showing the tool name and a summary of the result.
    * For short results (≤3 lines), displays inline. For longer results, shows
    * first 3 lines plus a "Show full output" clickable action link.
    *
    * @param toolName Tool's wire name (e.g., "read_theory")
    * @param result Tool execution result text
    * @param registerAction Function to register expand action and return its ID
    * @return HTML string for injection into chat
    */
  def toolResult(
      toolName: String,
      result: String,
      registerAction: (() => Unit) => String
  ): String = {
    val border = UIColors.ToolMessage.border
    val headerText = UIColors.ToolMessage.headerText
    val resultText = UIColors.TaskList.taskText
    val linkColor = UIColors.linkColor

    val displayName = toolNameToDisplay(toolName)
    val lines = result.linesIterator.toList
    val lineCount = lines.length

    // Smart truncation: show full if ≤3 lines, otherwise truncate with expand link
    val displayContent = if (lineCount <= 3) {
      HtmlUtil.escapeHtml(result)
    } else {
      val preview = lines.take(3).mkString("\n")
      val expandId = registerAction(() => {
        // When user clicks "Show full output", replace the widget with full content
        GUI_Thread.later {
          val fullHtml = toolResultFull(toolName, result)
          ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, fullHtml,
            java.time.LocalDateTime.now(), rawHtml = true, transient = true))
          AssistantDockable.showConversation(ChatAction.getHistory)
        }
      })
      val previewHtml = HtmlUtil.escapeHtml(preview)
      val expandLink =
        s"<div style='margin-top:${UIDesign.Space.md};font-size:${UIDesign.FontSize.sm};'>" +
          s"<a href='action:insert:$expandId' style='color:$linkColor;text-decoration:none;'>" +
          s"Show full output ($lineCount lines)</a></div>"
      previewHtml + expandLink
    }

    val body =
      s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.xs};font-weight:bold;'>" +
        s"Tool Result: <span style='font-family:${MarkdownRenderer.codeFont};font-weight:normal;'>$displayName</span></div>" +
        s"<div style='font-family:${MarkdownRenderer.codeFont};font-size:${UIDesign.FontSize.sm};color:$resultText;white-space:pre-wrap;'>" +
        displayContent +
        "</div>"

    UIDesign.card(body, border)
  }

  /** Render full (non-truncated) tool result widget.
    * Used when user clicks "Show full output" on a truncated result.
    */
  private def toolResultFull(toolName: String, result: String): String = {
    val border = UIColors.ToolMessage.border
    val headerText = UIColors.ToolMessage.headerText
    val resultText = UIColors.TaskList.taskText
    val muted = UIColors.ToolMessage.timestamp

    val displayName = toolNameToDisplay(toolName)
    val lineCount = result.linesIterator.size

    val body =
      s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.xs};font-weight:bold;'>" +
        s"Tool Result: <span style='font-family:${MarkdownRenderer.codeFont};font-weight:normal;'>$displayName</span> " +
        s"<span style='color:$muted;font-weight:normal;'>($lineCount lines)</span></div>" +
        s"<div style='font-family:${MarkdownRenderer.codeFont};font-size:${UIDesign.FontSize.sm};color:$resultText;white-space:pre-wrap;'>" +
        HtmlUtil.escapeHtml(result) +
        "</div>"

    UIDesign.card(body, border)
  }

  /** Render HTML widget for a newly added task notification.
    *
    * Displays a compact card showing the task title with truncated description
    * and acceptance criteria. Used when the LLM calls task_list_add.
    *
    * @param title Task title (max displayed: full)
    * @param description Task description (truncated to 100 chars for display)
    * @param criteria Acceptance criteria (truncated to 100 chars for display)
    * @return HTML string for injection into chat as a Widget message
    */
  def taskAdded(
      title: String,
      description: String,
      criteria: String
  ): String = {
    val border = UIColors.TaskList.border
    val headerText = UIColors.TaskList.headerText
    val labelColor = UIColors.TaskList.labelColor
    val taskText = UIColors.TaskList.taskText

    val truncDesc = truncateWord(description, 100)
    val truncCrit = truncateWord(criteria, 100)

    val body =
      s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.xs};font-weight:bold;'>Task Added</div>" +
        s"<div style='font-size:${UIDesign.FontSize.base};color:$taskText;margin-bottom:${UIDesign.Space.xs};'>" +
        s"&ldquo;${HtmlUtil.escapeHtml(title)}&rdquo;</div>" +
        s"<div style='font-size:${UIDesign.FontSize.xs};color:$labelColor;margin-top:${UIDesign.Space.sm};'>" +
        s"Description: <span style='color:$taskText;'>${HtmlUtil.escapeHtml(truncDesc)}</span></div>" +
        s"<div style='font-size:${UIDesign.FontSize.xs};color:$labelColor;'>" +
        s"Criteria: <span style='color:$taskText;'>${HtmlUtil.escapeHtml(truncCrit)}</span></div>"

    UIDesign.card(body, border)
  }

  /** Render HTML widget for a task status change (done/irrelevant).
    *
    * Shows a status update card with the task title, new status icon, and
    * overall progress summary. Used when the LLM calls task_list_done or
    * task_list_irrelevant.
    *
    * @param taskId ID of the task that changed status
    * @param status New status: "done" or "irrelevant"
    * @param result Status message returned by TaskList operation
    * @return HTML string for injection into chat as a Widget message
    */
  def taskStatus(taskId: Int, status: String, result: String): String = {
    val border = UIColors.TaskList.border
    val headerText = UIColors.TaskList.headerText
    val iconColor = if (status == "done") UIColors.TaskList.doneIcon else UIColors.TaskList.irrelevantIcon
    val symbol = if (status == "done") "✓" else "✗"
    val srLabel = if (status == "done") "Done" else "Irrelevant"
    val action = if (status == "done") "marked as done" else "marked as irrelevant"

    TaskList.getTasks.find(_.id == taskId) match {
      case Some(task) =>
        val (doneCount, todoCount, _) = TaskList.getStatusCounts
        val progress = s"$doneCount/${TaskList.getTaskCount} done, $todoCount pending"

        val body =
          s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.xs};font-weight:bold;'>" +
            HtmlUtil.accessibleGlyph(symbol, srLabel, iconColor) +
            s" Task #$taskId $action</div>" +
            s"<div style='font-size:${UIDesign.FontSize.base};margin-bottom:${UIDesign.Space.xs};'>" +
            s"&ldquo;${HtmlUtil.escapeHtml(task.title)}&rdquo;</div>" +
            s"<div style='font-size:${UIDesign.FontSize.xs};color:${UIColors.TaskList.progressText};'>" +
            s"Progress: $progress</div>"

        UIDesign.card(body, border)
      case None =>
        val body =
          s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;'>" +
            HtmlUtil.escapeHtml(result) +
            "</div>"
        UIDesign.card(body, border)
    }
  }

  /** Render HTML widget showing the full task list as a checklist.
    *
    * Displays all tasks with status icons (✓ done, ○ pending, ✗ irrelevant, ● next).
    * Used when the LLM calls task_list_show or task_list_next.
    *
    * @param highlightNext If true, visually emphasizes the next pending task with
    *                      a filled circle (●) and a "NEXT" badge
    * @return HTML string for injection into chat as a Widget message
    */
  def taskList(highlightNext: Boolean): String = {
    val border = UIColors.TaskList.border
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
      val body =
        s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;font-weight:bold;'>Task List</div>" +
          s"<div style='font-size:${UIDesign.FontSize.sm};color:$progressText;margin-top:${UIDesign.Space.sm};'>" +
          "Task list is empty. Add tasks to get started." +
          "</div>"
      UIDesign.card(body, border)
    } else {
      val (doneCount, todoCount, _) = TaskList.getStatusCounts
      val progress = s"$doneCount/${tasks.length} done, $todoCount pending"

      val nextTaskId = tasks.find(_.status == TaskList.Todo).map(_.id)

      val taskItems = tasks.map { task =>
        val isNext = highlightNext && nextTaskId.contains(task.id)
        val (icon, iconColor, srLabel) = task.status match {
          case TaskList.Done           => ("✓", doneIcon, "Done")
          case TaskList.Irrelevant     => ("✗", irrelevantIcon, "Irrelevant")
          case TaskList.Todo if isNext => ("●", nextIcon, "Next")
          case TaskList.Todo           => ("○", pendingIcon, "Pending")
        }

        val titleStyle = task.status match {
          case TaskList.Irrelevant => s"color:$irrelevantText;text-decoration:line-through;"
          case _ => s"color:$taskText;"
        }

        val nextBadge =
          if (isNext)
            s" <span style='display:inline-block;margin-left:${UIDesign.Space.sm};padding:0 ${UIDesign.Space.sm};" +
              s"font-size:${UIDesign.FontSize.xs};font-weight:bold;letter-spacing:0.5px;" +
              s"color:$nextIcon;border:1px solid $nextIcon;border-radius:${UIDesign.Radius.sm};'>NEXT</span>"
          else ""

        s"<div style='margin:${UIDesign.Space.xs} 0;'>" +
          s"<span style='margin-right:${UIDesign.Space.sm};'>" +
          HtmlUtil.accessibleGlyph(icon, srLabel, iconColor) +
          "</span>" +
          s"<span style='$titleStyle;font-size:${UIDesign.FontSize.sm};'>#${task.id}. ${HtmlUtil.escapeHtml(task.title)}</span>$nextBadge" +
          "</div>"
      }.mkString("\n")

      val body =
        s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.xs};font-weight:bold;'>" +
          s"Task List <span style='font-weight:normal;color:$progressText;'>($progress)</span></div>" +
          s"<div style='margin-top:${UIDesign.Space.sm};'>$taskItems</div>"

      UIDesign.card(body, border)
    }
  }

  /** Render HTML widget showing detailed information for a specific task.
    *
    * Displays full task title, description, acceptance criteria, and status icon.
    * Used when the LLM calls task_list_get.
    *
    * @param task The task to display details for
    * @return HTML string for injection into chat as a Widget message
    */
  def taskDetail(task: TaskList.Task): String = {
    val border = UIColors.TaskList.border
    val headerText = UIColors.TaskList.headerText
    val labelColor = UIColors.TaskList.labelColor
    val taskText = UIColors.TaskList.taskText
    val (icon, iconColor, srLabel) = task.status match {
      case TaskList.Done       => ("✓", UIColors.TaskList.doneIcon, "Done")
      case TaskList.Irrelevant => ("✗", UIColors.TaskList.irrelevantIcon, "Irrelevant")
      case TaskList.Todo       => ("○", UIColors.TaskList.pendingIcon, "Pending")
    }

    val body =
      s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.sm};font-weight:bold;'>" +
        s"Task #${task.id}: ${HtmlUtil.escapeHtml(task.title)}" +
        s"<span style='margin-left:${UIDesign.Space.md};'>" +
        HtmlUtil.accessibleGlyph(icon, srLabel, iconColor) +
        "</span></div>" +
        s"<div style='font-size:${UIDesign.FontSize.xs};color:$labelColor;margin-top:${UIDesign.Space.md};margin-bottom:${UIDesign.Space.xs};'>Description</div>" +
        s"<div style='font-size:${UIDesign.FontSize.sm};color:$taskText;margin-bottom:${UIDesign.Space.md};'>" +
        HtmlUtil.escapeHtml(task.description) +
        "</div>" +
        s"<div style='font-size:${UIDesign.FontSize.xs};color:$labelColor;margin-bottom:${UIDesign.Space.xs};'>Acceptance Criteria</div>" +
        s"<div style='font-size:${UIDesign.FontSize.sm};color:$taskText;'>" +
        HtmlUtil.escapeHtml(task.acceptanceCriteria) +
        "</div>"

    UIDesign.card(body, border)
  }

  /** Render HTML for a user prompt with multiple choice options.
    * @param question the question to present
    * @param context optional context/explanation
    * @param options list of option strings
    * @param onChoice callback to register actions for each option
    * @return HTML for the prompt widget
    *
    * NOTE: Option selection is click-only. Keyboard-accessible selection
    * would require JS-like focus management which JEditorPane doesn't support.
    * Consider migrating to JPanel-based widgets for full keyboard support.
    */
  def askUser(
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
        s"<div style='margin:${UIDesign.Space.xs} 0 ${UIDesign.Space.xs} ${UIDesign.Space.lg};'>" +
          s"<a href='action:insert:$actionId' style='text-decoration:none;color:${UIColors.AskUser.optionLetter};font-weight:bold;'>$label.</a>" +
          s"<a href='action:insert:$actionId' style='text-decoration:none;color:${UIColors.AskUser.optionText};margin-left:${UIDesign.Space.md};'>" +
          s"${HtmlUtil.escapeHtml(opt)}</a>" +
          "</div>"
      }
      .mkString("\n")

    val contextHtml =
      if (context.nonEmpty)
        s"<div style='font-size:${UIDesign.FontSize.sm};color:${UIColors.AskUser.contextText};" +
          s"margin:${UIDesign.Space.sm} 0 ${UIDesign.Space.md};font-style:italic;'>${HtmlUtil.escapeHtml(context)}</div>"
      else ""

    val hint =
      s"<div style='margin-top:${UIDesign.Space.md};font-size:${UIDesign.FontSize.xs};color:${UIColors.AskUser.contextText};'>" +
        "Click an option to select." +
        "</div>"

    val body =
      s"<div style='font-size:${UIDesign.FontSize.sm};color:${UIColors.AskUser.title};margin-bottom:${UIDesign.Space.xs};font-weight:bold;'>" +
        "Assistant needs your input.</div>" +
        s"<div style='font-size:${UIDesign.FontSize.md};color:${UIColors.AskUser.optionText};margin-bottom:${UIDesign.Space.md};'>" +
        HtmlUtil.escapeHtml(question) +
        "</div>" +
        contextHtml +
        optionButtons +
        hint

    UIDesign.card(body, UIColors.AskUser.border)
  }

  /** Render HTML widget for planning in progress.
    * Shows the current phase of the adaptive tree-of-thought planning process.
    *
    * @param problem Brief description of the problem being planned
    * @param phase Current phase: "brainstorm", "elaborate", or "select"
    * @param approachTitles Titles of the 3 approaches (for elaborate/select phases)
    * @return HTML string for injection into chat as a Widget message
    */
  def planningInProgress(
      problem: String,
      phase: String,
      approachTitles: List[String] = List.empty
  ): String = {
    val border = UIColors.ToolMessage.border
    val headerText = UIColors.ToolMessage.headerText
    val progressText = UIColors.TaskList.progressText

    val truncProblem = truncateWord(problem, 80)

    val phaseDisplay = phase match {
      case "brainstorm" => "Phase 1: Brainstorming approaches…"
      case "elaborate"  => "Phase 2: Elaborating approaches in parallel…"
      case "select"     => "Phase 3: Selecting best approach…"
      case _            => "Planning…"
    }

    val approachesHtml = if (approachTitles.nonEmpty) {
      val items = approachTitles.zipWithIndex.map { case (title, idx) =>
        s"<div style='margin-left:${UIDesign.Space.lg};font-size:${UIDesign.FontSize.sm};color:$progressText;'>" +
          s"Approach ${idx + 1}: ${HtmlUtil.escapeHtml(title)}</div>"
      }.mkString("\n")
      s"\n$items"
    } else ""

    val body =
      s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.xs};font-weight:bold;'>" +
        s"Planning: &ldquo;${HtmlUtil.escapeHtml(truncProblem)}&rdquo;</div>" +
        s"<div style='font-size:${UIDesign.FontSize.sm};color:$progressText;margin-top:${UIDesign.Space.sm};'>" +
        phaseDisplay +
        "</div>" +
        approachesHtml

    UIDesign.card(body, border)
  }

  /** Render HTML widget showing the planning result.
    * Shows all approaches, which was selected, why, and the final plan.
    *
    * Approaches are passed as `(id, title)` pairs so the selected-approach
    * comparison is by ID (matching the orchestrator's semantics) rather
    * than by list position.
    *
    * @param problem The problem that was planned
    * @param approaches List of (id, title) for each approach considered
    * @param selectedApproach ID of selected approach
    * @param reasoning Why this approach was selected
    * @param plan The final detailed plan text
    * @param registerAction Function to register collapse/expand action
    * @return HTML string for injection into chat as a Widget message
    */
  def planningResult(
      problem: String,
      approaches: List[(Int, String)],
      selectedApproach: Int,
      reasoning: String,
      plan: String,
      registerAction: (() => Unit) => String
  ): String = {
    val body = planningResultBody(
      problem,
      approaches,
      selectedApproach,
      reasoning,
      Some((plan, registerAction))
    )
    UIDesign.card(body, UIColors.ToolMessage.border)
  }

  /** Render expanded planning result (full plan, no truncation). */
  private def planningResultExpanded(
      problem: String,
      approaches: List[(Int, String)],
      selectedApproach: Int,
      reasoning: String,
      plan: String
  ): String = {
    val body = planningResultBody(
      problem,
      approaches,
      selectedApproach,
      reasoning,
      collapsible = None,
      forcePlan = Some(plan)
    )
    UIDesign.card(body, UIColors.ToolMessage.border)
  }

  private def planningResultBody(
      problem: String,
      approaches: List[(Int, String)],
      selectedApproach: Int,
      reasoning: String,
      collapsible: Option[(String, (() => Unit) => String)],
      forcePlan: Option[String] = None
  ): String = {
    val headerText = UIColors.ToolMessage.headerText
    val progressText = UIColors.TaskList.progressText
    val selectedIcon = UIColors.TaskList.doneIcon
    val taskText = UIColors.TaskList.taskText
    val linkColor = UIColors.linkColor

    val truncProblem = truncateWord(problem, 80)

    val approachesHtml = approaches.zipWithIndex.map { case ((id, title), idx) =>
      val isSelected = id == selectedApproach
      val marker =
        if (isSelected) HtmlUtil.accessibleGlyph("✓", "Selected", selectedIcon) + " "
        else "&nbsp;&nbsp;&nbsp;"
      val style =
        if (isSelected) s"font-weight:bold;color:$headerText;"
        else s"color:$progressText;"
      s"<div style='margin:${UIDesign.Space.xs} 0 ${UIDesign.Space.xs} ${UIDesign.Space.lg};font-size:${UIDesign.FontSize.sm};$style'>" +
        s"$marker${idx + 1}. ${HtmlUtil.escapeHtml(title)}</div>"
    }.mkString("\n")

    val reasoningHtml =
      s"<div style='margin:${UIDesign.Space.md} 0 ${UIDesign.Space.md} ${UIDesign.Space.lg};" +
        s"font-size:${UIDesign.FontSize.sm};color:$taskText;font-style:italic;'>" +
        s"&ldquo;${HtmlUtil.escapeHtml(reasoning)}&rdquo;</div>"

    val planHtml = forcePlan match {
      case Some(fullPlan) =>
        s"<pre style='font-family:${MarkdownRenderer.codeFont};font-size:${UIDesign.FontSize.sm};" +
          s"color:$taskText;white-space:pre-wrap;margin:${UIDesign.Space.md} 0 0 ${UIDesign.Space.lg};'>" +
          HtmlUtil.escapeHtml(fullPlan) +
          "</pre>"
      case None =>
        collapsible match {
          case Some((plan, register)) =>
            val planLines = plan.linesIterator.toList
            if (planLines.length <= AssistantConstants.PLANNING_RESULT_INLINE_LINE_LIMIT) {
              s"<pre style='font-family:${MarkdownRenderer.codeFont};font-size:${UIDesign.FontSize.sm};" +
                s"color:$taskText;white-space:pre-wrap;margin:${UIDesign.Space.md} 0 0 ${UIDesign.Space.lg};'>" +
                HtmlUtil.escapeHtml(plan) +
                "</pre>"
            } else {
              val preview = planLines.take(5).mkString("\n")
              val expandId = register(() => {
                GUI_Thread.later {
                  val fullHtml = planningResultExpanded(problem, approaches, selectedApproach, reasoning, plan)
                  ChatAction.addMessage(ChatAction.Message(
                    ChatAction.Widget, fullHtml,
                    java.time.LocalDateTime.now(), rawHtml = true, transient = true
                  ))
                  AssistantDockable.showConversation(ChatAction.getHistory)
                }
              })
              s"<pre style='font-family:${MarkdownRenderer.codeFont};font-size:${UIDesign.FontSize.sm};" +
                s"color:$taskText;white-space:pre-wrap;margin:${UIDesign.Space.md} 0 0 ${UIDesign.Space.lg};'>" +
                HtmlUtil.escapeHtml(preview) +
                "</pre>" +
                s"<div style='margin:${UIDesign.Space.sm} 0 0 ${UIDesign.Space.lg};font-size:${UIDesign.FontSize.sm};'>" +
                s"<a href='action:insert:$expandId' style='color:$linkColor;text-decoration:none;'>" +
                s"Show full plan (${planLines.length} lines)</a></div>"
            }
          case None => ""
        }
    }

    s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.sm};font-weight:bold;'>" +
      s"Planning Complete: &ldquo;${HtmlUtil.escapeHtml(truncProblem)}&rdquo;</div>" +
      s"<div style='font-size:${UIDesign.FontSize.xs};color:$progressText;margin:${UIDesign.Space.sm} 0 ${UIDesign.Space.sm} ${UIDesign.Space.lg};'>Approaches considered</div>" +
      approachesHtml +
      s"<div style='font-size:${UIDesign.FontSize.xs};color:$progressText;margin:${UIDesign.Space.md} 0 ${UIDesign.Space.xs} ${UIDesign.Space.lg};'>Selection reasoning</div>" +
      reasoningHtml +
      s"<div style='font-size:${UIDesign.FontSize.xs};color:$progressText;margin:${UIDesign.Space.md} 0 ${UIDesign.Space.xs} ${UIDesign.Space.lg};'>" +
      (if (forcePlan.isDefined) "Full plan" else "Final plan") +
      "</div>" +
      planHtml
  }
}
