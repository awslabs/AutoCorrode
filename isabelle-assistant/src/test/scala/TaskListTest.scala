/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatest.BeforeAndAfterEach

/**
 * Tests for TaskList singleton task management.
 * Tests thread-safe CRUD operations without requiring jEdit runtime.
 */
class TaskListTest extends AnyFunSuite with Matchers with BeforeAndAfterEach {

  // Clear task list before each test
  override def beforeEach(): Unit = {
    TaskList.clear()
  }

  test("new task list should be empty") {
    TaskList.getTasks shouldBe empty
    TaskList.getTaskCount shouldBe 0
  }

  test("addTask should create a new task with auto-incrementing ID") {
    val result = TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    result should include("Task #1 added")
    result should include("Task 1")
    
    val result2 = TaskList.addTask("Task 2", "Description 2", "Criteria 2")
    result2 should include("Task #2 added")
    result2 should include("Task 2")
    
    TaskList.getTaskCount shouldBe 2
  }

  test("addTask should require non-empty title") {
    val result = TaskList.addTask("", "Description", "Criteria")
    result should include("Error")
    result should include("title")
    TaskList.getTaskCount shouldBe 0
  }

  test("addTask should require non-empty description") {
    val result = TaskList.addTask("Title", "", "Criteria")
    result should include("Error")
    result should include("description")
    TaskList.getTaskCount shouldBe 0
  }

  test("addTask should require non-empty acceptance criteria") {
    val result = TaskList.addTask("Title", "Description", "")
    result should include("Error")
    result should include("criteria")
    TaskList.getTaskCount shouldBe 0
  }

  test("addTask should trim whitespace") {
    val result = TaskList.addTask("  Title  ", "  Desc  ", "  Criteria  ")
    result should include("Task #1 added")
    val tasks = TaskList.getTasks
    tasks.head.title shouldBe "Title"
    tasks.head.description shouldBe "Desc"
    tasks.head.acceptanceCriteria shouldBe "Criteria"
  }

  test("markDone should mark a task as completed") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    val result = TaskList.markDone(1)
    
    result should include("Task #1")
    result should include("marked as done")
    result should include("Task 1")
    
    val task = TaskList.getTasks.head
    task.status shouldBe TaskList.Done
  }

  test("markDone should return error for non-existent task") {
    val result = TaskList.markDone(999)
    result should include("Error")
    result should include("not found")
  }

  test("markDone should handle already done task") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.markDone(1)
    val result = TaskList.markDone(1)
    
    result should include("already marked as done")
  }

  test("markIrrelevant should mark a task as irrelevant") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    val result = TaskList.markIrrelevant(1)
    
    result should include("Task #1")
    result should include("marked as irrelevant")
    
    val task = TaskList.getTasks.head
    task.status shouldBe TaskList.Irrelevant
  }

  test("markIrrelevant should return error for non-existent task") {
    val result = TaskList.markIrrelevant(999)
    result should include("Error")
    result should include("not found")
  }

  test("markIrrelevant should handle already irrelevant task") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.markIrrelevant(1)
    val result = TaskList.markIrrelevant(1)
    
    result should include("already marked as irrelevant")
  }

  test("getNextTask should return first pending task") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.addTask("Task 2", "Description 2", "Criteria 2")
    TaskList.addTask("Task 3", "Description 3", "Criteria 3")
    
    val result = TaskList.getNextTask()
    result should include("Next task: #1")
    result should include("Task 1")
    result should include("Description 1")
    result should include("Criteria 1")
  }

  test("getNextTask should skip completed tasks") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.addTask("Task 2", "Description 2", "Criteria 2")
    TaskList.markDone(1)
    
    val result = TaskList.getNextTask()
    result should include("Next task: #2")
    result should include("Task 2")
  }

  test("getNextTask should skip irrelevant tasks") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.addTask("Task 2", "Description 2", "Criteria 2")
    TaskList.markIrrelevant(1)
    
    val result = TaskList.getNextTask()
    result should include("Next task: #2")
    result should include("Task 2")
  }

  test("getNextTask should report when list is empty") {
    val result = TaskList.getNextTask()
    result should include("Task list is empty")
  }

  test("getNextTask should report when all tasks are complete") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.addTask("Task 2", "Description 2", "Criteria 2")
    TaskList.markDone(1)
    TaskList.markIrrelevant(2)
    
    val result = TaskList.getNextTask()
    result should include("No pending tasks")
    result should include("All 2 tasks are complete")
  }

  test("listTasks should return all tasks with statuses") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.addTask("Task 2", "Description 2", "Criteria 2")
    TaskList.addTask("Task 3", "Description 3", "Criteria 3")
    TaskList.markDone(1)
    TaskList.markIrrelevant(3)
    
    val result = TaskList.listTasks()
    result should include("Task List")
    result should include("#1. Task 1")
    result should include("#2. Task 2")
    result should include("#3.")  // Irrelevant tasks include [crossed out] marker
    result should include("Task 3")
    result should include("1/3 done, 1 pending")
  }

  test("listTasks should report empty list") {
    val result = TaskList.listTasks()
    result should include("Task list is empty")
  }

  test("getTask should return task details") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    
    val result = TaskList.getTask(1)
    result should include("Task #1: Task 1")
    result should include("Description 1")
    result should include("Criteria 1")
    result should include("pending")
  }

  test("getTask should return error for non-existent task") {
    val result = TaskList.getTask(999)
    result should include("Error")
    result should include("not found")
  }

  test("clear should reset all state") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.addTask("Task 2", "Description 2", "Criteria 2")
    
    TaskList.clear()
    
    TaskList.getTaskCount shouldBe 0
    TaskList.getTasks shouldBe empty
    
    // Next task should have ID 1 again
    TaskList.addTask("New Task", "New Desc", "New Criteria")
    val tasks = TaskList.getTasks
    tasks.head.id shouldBe 1
  }

  test("getStatusCounts should return correct counts") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.addTask("Task 2", "Description 2", "Criteria 2")
    TaskList.addTask("Task 3", "Description 3", "Criteria 3")
    TaskList.addTask("Task 4", "Description 4", "Criteria 4")
    
    TaskList.markDone(1)
    TaskList.markDone(2)
    TaskList.markIrrelevant(4)
    
    val (doneCount, todoCount, irrelevantCount) = TaskList.getStatusCounts
    doneCount shouldBe 2
    todoCount shouldBe 1
    irrelevantCount shouldBe 1
  }

  test("tasks should have creation timestamps") {
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    val task = TaskList.getTasks.head
    
    task.createdAt should not be null
  }

  test("task status symbols should be correct") {
    TaskList.Todo.symbol shouldBe "○"
    TaskList.Done.symbol shouldBe "✓"
    TaskList.Irrelevant.symbol shouldBe "✗"
  }

  test("task status display names should be correct") {
    TaskList.Todo.displayName shouldBe "pending"
    TaskList.Done.displayName shouldBe "done"
    TaskList.Irrelevant.displayName shouldBe "irrelevant"
  }

  test("progress reporting should handle various states") {
    // Empty list
    TaskList.listTasks() should include("empty")
    
    // One todo task
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.listTasks() should include("0/1 done, 1 pending")
    
    // One done task
    TaskList.markDone(1)
    TaskList.listTasks() should include("all tasks complete")
    
    // Mix of statuses
    TaskList.clear()
    TaskList.addTask("Task 1", "Description 1", "Criteria 1")
    TaskList.addTask("Task 2", "Description 2", "Criteria 2")
    TaskList.addTask("Task 3", "Description 3", "Criteria 3")
    TaskList.markDone(1)
    TaskList.markIrrelevant(2)
    TaskList.listTasks() should include("1/3 done, 1 pending")
  }

  test("multiple operations should maintain consistency") {
    // Add multiple tasks
    for (i <- 1 to 5) {
      TaskList.addTask(s"Task $i", s"Description $i", s"Criteria $i")
    }
    TaskList.getTaskCount shouldBe 5
    
    // Mark some done
    TaskList.markDone(1)
    TaskList.markDone(3)
    TaskList.markDone(5)
    
    // Mark some irrelevant
    TaskList.markIrrelevant(2)
    
    // Verify counts
    val (done, todo, irrelevant) = TaskList.getStatusCounts
    done shouldBe 3
    todo shouldBe 1
    irrelevant shouldBe 1
    
    // Next task should be #4 (only remaining todo)
    val next = TaskList.getNextTask()
    next should include("#4")
  }
}