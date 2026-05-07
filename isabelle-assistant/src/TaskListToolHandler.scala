/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import scala.annotation.unused

import ToolArgs._

/** Executes the task_list_* tools that manage the assistant's in-session task
  * list. Each handler invokes the TaskList store and then injects a rich HTML
  * widget into chat. Split out of AssistantTools for cohesion.
  */
private[assistant] object TaskListToolHandler {

  def execTaskListAdd(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val title = safeStringArg(args, "title", 500)
    val description = safeStringArg(args, "description", 2000)
    val criteria = safeStringArg(args, "acceptance_criteria", 2000)
    val result = TaskList.addTask(title, description, criteria)
    postWidget(buildTaskAddedHtml(title, description, criteria))
    result
  }

  def execTaskListDone(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val taskId = intArg(args, "task_id", -1)
    val result = TaskList.markDone(taskId)
    postWidget(buildTaskStatusHtml(taskId, "done", result))
    result
  }

  def execTaskListIrrelevant(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val taskId = intArg(args, "task_id", -1)
    val result = TaskList.markIrrelevant(taskId)
    postWidget(buildTaskStatusHtml(taskId, "irrelevant", result))
    result
  }

  def execTaskListNext(@unused view: View): String = {
    val result = TaskList.getNextTask()
    postWidget(buildTaskListHtml(highlightNext = true))
    result
  }

  def execTaskListShow(@unused view: View): String = {
    val result = TaskList.listTasks()
    postWidget(buildTaskListHtml(highlightNext = false))
    result
  }

  def execTaskListGet(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val taskId = intArg(args, "task_id", -1)
    val result = TaskList.getTask(taskId)
    GUI_Thread.later {
      TaskList.getTasks.find(_.id == taskId).foreach { task =>
        val html = buildTaskDetailHtml(task)
        ChatAction.addMessage(
          ChatAction.Message(
            ChatAction.Widget,
            html,
            java.time.LocalDateTime.now(),
            rawHtml = true,
            transient = true
          )
        )
        AssistantDockable.showConversation(ChatAction.getHistory)
      }
    }
    result
  }

  private def postWidget(html: String): Unit = {
    GUI_Thread.later {
      ChatAction.addMessage(
        ChatAction.Message(
          ChatAction.Widget,
          html,
          java.time.LocalDateTime.now(),
          rawHtml = true,
          transient = true
        )
      )
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
  }

  // All task-widget HTML routes through WidgetRenderer so there is exactly one
  // implementation per widget shape. Do not reimplement here — that is how the
  // UI drifted into three different styles per card.
  private def buildTaskAddedHtml(title: String, description: String, criteria: String): String =
    WidgetRenderer.taskAdded(title, description, criteria)

  private def buildTaskStatusHtml(taskId: Int, status: String, result: String): String =
    WidgetRenderer.taskStatus(taskId, status, result)

  private def buildTaskListHtml(highlightNext: Boolean): String =
    WidgetRenderer.taskList(highlightNext)

  private def buildTaskDetailHtml(task: TaskList.Task): String =
    WidgetRenderer.taskDetail(task)
}
