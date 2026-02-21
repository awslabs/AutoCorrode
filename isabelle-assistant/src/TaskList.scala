/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.time.LocalDateTime
import java.time.format.DateTimeFormatter

/**
 * Thread-safe singleton task list for LLM-managed todo lists.
 * 
 * Provides a single global task list per session that is automatically
 * available (no creation needed) and cleared when the chat is cleared.
 * Tasks have three statuses: Todo, Done, Irrelevant.
 */
object TaskList {

  /** Task status enumeration */
  enum TaskStatus(val symbol: String, val displayName: String) {
    case Todo extends TaskStatus("○", "pending")
    case Done extends TaskStatus("✓", "done")
    case Irrelevant extends TaskStatus("✗", "irrelevant")
  }
  export TaskStatus._

  /** Task data structure */
  case class Task(
    id: Int,
    title: String,
    description: String,
    acceptanceCriteria: String,
    status: TaskStatus,
    createdAt: LocalDateTime
  )

  // Thread-safe state
  private val lock = new Object()
  @volatile private var tasks: List[Task] = Nil
  @volatile private var nextId: Int = 1
  private val timeFormatter = DateTimeFormatter.ofPattern("HH:mm")

  /**
   * Add a new task to the list.
   * 
   * @param title Brief task title (required)
   * @param description Detailed description of what needs to be done (required)
   * @param acceptanceCriteria Clear criteria for when the task is considered complete (required)
   * @return Confirmation message with task ID
   */
  def addTask(
    title: String,
    description: String,
    acceptanceCriteria: String
  ): String = lock.synchronized {
    val trimmedTitle = title.trim
    val trimmedDesc = description.trim
    val trimmedCriteria = acceptanceCriteria.trim

    if (trimmedTitle.isEmpty)
      return "Error: task title cannot be empty"
    if (trimmedDesc.isEmpty)
      return "Error: task description cannot be empty"
    if (trimmedCriteria.isEmpty)
      return "Error: acceptance criteria cannot be empty"

    val task = Task(
      id = nextId,
      title = trimmedTitle,
      description = trimmedDesc,
      acceptanceCriteria = trimmedCriteria,
      status = Todo,
      createdAt = LocalDateTime.now()
    )
    tasks = tasks :+ task
    nextId += 1

    val progress = getProgress
    s"Task #${task.id} added: ${task.title}\nProgress: $progress"
  }

  /**
   * Mark a task as done.
   * 
   * @param taskId The ID of the task to mark as done
   * @return Confirmation message with updated progress
   */
  def markDone(taskId: Int): String = lock.synchronized {
    tasks.find(_.id == taskId) match {
      case None => s"Error: task #$taskId not found"
      case Some(task) if task.status == Done =>
        s"Task #$taskId '${task.title}' is already marked as done"
      case Some(task) =>
        tasks = tasks.map(t => 
          if (t.id == taskId) t.copy(status = Done) else t
        )
        val progress = getProgress
        s"Task #$taskId '${task.title}' marked as done\nProgress: $progress"
    }
  }

  /**
   * Mark a task as irrelevant (no longer needed).
   * 
   * @param taskId The ID of the task to mark as irrelevant
   * @return Confirmation message with updated progress
   */
  def markIrrelevant(taskId: Int): String = lock.synchronized {
    tasks.find(_.id == taskId) match {
      case None => s"Error: task #$taskId not found"
      case Some(task) if task.status == Irrelevant =>
        s"Task #$taskId '${task.title}' is already marked as irrelevant"
      case Some(task) =>
        tasks = tasks.map(t =>
          if (t.id == taskId) t.copy(status = Irrelevant) else t
        )
        val progress = getProgress
        s"Task #$taskId '${task.title}' marked as irrelevant\nProgress: $progress"
    }
  }

  /**
   * Get the next pending (Todo) task.
   * 
   * @return The next task to work on, or a message if no tasks are pending
   */
  def getNextTask(): String = lock.synchronized {
    tasks.find(_.status == Todo) match {
      case None =>
        if (tasks.isEmpty) "Task list is empty. Add tasks to get started."
        else {
          val doneCount = tasks.count(_.status == Done)
          val irrelevantCount = tasks.count(_.status == Irrelevant)
          s"No pending tasks. All ${tasks.length} tasks are complete ($doneCount done, $irrelevantCount irrelevant)."
        }
      case Some(task) =>
        val progress = getProgress
        s"Next task: #${task.id} '${task.title}'\n" +
        s"Description: ${task.description}\n" +
        s"Acceptance criteria: ${task.acceptanceCriteria}\n" +
        s"Progress: $progress"
    }
  }

  /**
   * List all tasks with their current statuses.
   * 
   * @return Formatted list of all tasks
   */
  def listTasks(): String = lock.synchronized {
    if (tasks.isEmpty)
      return "Task list is empty. Add tasks to get started."

    val progress = getProgress
    val header = s"Task List ($progress)\n" + "=" * 40

    val taskLines = tasks.map { task =>
      val statusSymbol = task.status.symbol
      val titleDisplay = if (task.status == Irrelevant) {
        s"[crossed out] ${task.title}"
      } else {
        task.title
      }
      s"$statusSymbol  #${task.id}. $titleDisplay"
    }

    (header :: taskLines.toList).mkString("\n")
  }

  /**
   * Get detailed information about a specific task.
   * 
   * @param taskId The ID of the task to retrieve
   * @return Detailed task information
   */
  def getTask(taskId: Int): String = lock.synchronized {
    tasks.find(_.id == taskId) match {
      case None => s"Error: task #$taskId not found"
      case Some(task) =>
        val createdTime = task.createdAt.format(timeFormatter)
        s"Task #${task.id}: ${task.title}\n" +
        s"Status: ${task.status.displayName}\n" +
        s"Created: $createdTime\n\n" +
        s"Description:\n${task.description}\n\n" +
        s"Acceptance Criteria:\n${task.acceptanceCriteria}"
    }
  }

  /**
   * Clear all tasks and reset the task list.
   * Called when the chat is cleared.
   */
  def clear(): Unit = lock.synchronized {
    tasks = Nil
    nextId = 1
  }

  /**
   * Get the current progress as a formatted string.
   * 
   * @return Progress string like "3/6 done" or "all tasks complete"
   */
  private def getProgress: String = {
    val total = tasks.length
    val doneCount = tasks.count(_.status == Done)
    val todoCount = tasks.count(_.status == Todo)
    val irrelevantCount = tasks.count(_.status == Irrelevant)

    if (total == 0) "0 tasks"
    else if (todoCount == 0) s"all tasks complete ($doneCount done, $irrelevantCount irrelevant)"
    else s"$doneCount/$total done, $todoCount pending"
  }

  /**
   * Get a snapshot of the current task list state.
   * Used for generating rich HTML widgets.
   * 
   * @return Current list of tasks
   */
  def getTasks: List[Task] = lock.synchronized { tasks }

  /**
   * Get the total count of tasks.
   * 
   * @return Number of tasks in the list
   */
  def getTaskCount: Int = lock.synchronized { tasks.length }

  /**
   * Get counts by status.
   * 
   * @return Tuple of (doneCount, todoCount, irrelevantCount)
   */
  def getStatusCounts: (Int, Int, Int) = lock.synchronized {
    val doneCount = tasks.count(_.status == Done)
    val todoCount = tasks.count(_.status == Todo)
    val irrelevantCount = tasks.count(_.status == Irrelevant)
    (doneCount, todoCount, irrelevantCount)
  }
}
