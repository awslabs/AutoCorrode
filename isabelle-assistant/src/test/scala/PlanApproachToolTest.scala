/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import software.amazon.awssdk.thirdparty.jackson.core.JsonFactory

/**
 * Contract tests for the `plan_approach` tool schema and planning subsystem
 * wiring. These tests deliberately avoid invoking the live BedrockClient —
 * they guard against the class of regression where the handler, schema,
 * orchestrator, and system prompt drift out of sync on parameter names.
 */
class PlanApproachToolTest extends AnyFunSuite with Matchers {

  private val jsonFactory = new JsonFactory()

  // --- Tool schema contract ---

  test("plan_approach tool should be registered in AssistantTools") {
    val names = AssistantTools.tools.map(_.name).toSet
    names should contain("plan_approach")
  }

  test("plan_approach tool should use the canonical ToolId wire name") {
    ToolId.PlanApproach.wireName shouldBe "plan_approach"
  }

  test("plan_approach tool should declare 'problem' as a required parameter") {
    val tool = AssistantTools.tools.find(_.name == "plan_approach").value
    val required = tool.params.filter(_.required).map(_.name)
    required should contain("problem")
  }

  test("plan_approach tool should declare 'scope' and 'context' as optional parameters") {
    val tool = AssistantTools.tools.find(_.name == "plan_approach").value
    val paramNames = tool.params.map(_.name).toSet
    paramNames should contain("scope")
    paramNames should contain("context")

    val optional = tool.params.filter(!_.required).map(_.name).toSet
    optional should contain("scope")
    optional should contain("context")
  }

  test("plan_approach tool MUST NOT retain the old 'task' parameter") {
    // Regression guard: prior to the audit this tool declared `task` +
    // `context`, but the orchestrator took `problem` + `scope`. The
    // mismatch made the handler unreachable in practice. Keep this test
    // so that the same drift can't recur.
    val tool = AssistantTools.tools.find(_.name == "plan_approach").value
    val paramNames = tool.params.map(_.name).toSet
    paramNames should not contain "task"
  }

  test("plan_approach should have a non-empty description that mentions planning") {
    val tool = AssistantTools.tools.find(_.name == "plan_approach").value
    tool.description should not be empty
    tool.description.toLowerCase should include("plan")
  }

  // --- Handler behaviour ---

  test("execPlanApproach should return an error when problem is missing") {
    // We pass view=null because the empty-problem branch returns before
    // touching the view. Any invocation that would reach the orchestrator
    // would fail ambiguously; that's intentional for this test.
    val args: ResponseParser.ToolArgs = Map.empty
    val result = PlanApproachToolHandler.execPlanApproach(args, null)
    result should startWith("Error:")
    result.toLowerCase should include("problem")
  }

  test("execPlanApproach should return an error when problem is blank whitespace") {
    val args: ResponseParser.ToolArgs =
      Map("problem" -> ResponseParser.StringValue("   \n\t  "))
    val result = PlanApproachToolHandler.execPlanApproach(args, null)
    result should startWith("Error:")
  }

  // --- ToolId.planningToolIds contract ---

  test("planningToolIds should contain only read-only exploration tools") {
    val writeTools = Set(
      ToolId.EditTheory, ToolId.CreateTheory, ToolId.OpenTheory,
      ToolId.VerifyProof, ToolId.ExecuteStep, ToolId.TryMethods,
      ToolId.RunSledgehammer, ToolId.RunNitpick, ToolId.RunQuickcheck,
      ToolId.FindCounterexample, ToolId.TraceSimplifier,
      ToolId.WebSearch
    )
    for (w <- writeTools)
      ToolId.planningToolIds should not contain w
  }

  test("planningToolIds MUST NOT contain PlanApproach (recursion guard)") {
    ToolId.planningToolIds should not contain ToolId.PlanApproach
  }

  test("planningToolIds MUST NOT contain AskUser (sub-agents can't prompt)") {
    ToolId.planningToolIds should not contain ToolId.AskUser
  }

  test("planningToolIds MUST NOT contain any task_list_* tools") {
    val taskListTools = Set(
      ToolId.TaskListAdd, ToolId.TaskListDone, ToolId.TaskListIrrelevant,
      ToolId.TaskListNext, ToolId.TaskListShow, ToolId.TaskListGet
    )
    for (t <- taskListTools)
      ToolId.planningToolIds should not contain t
  }

  test("planningToolIds MUST NOT contain any memory_* tools") {
    val memoryTools = Set(
      ToolId.MemoryAdd, ToolId.MemoryDelete, ToolId.MemoryDeleteTopic,
      ToolId.MemoryListTopics, ToolId.MemoryList, ToolId.MemoryGet,
      ToolId.MemorySearch
    )
    for (m <- memoryTools)
      ToolId.planningToolIds should not contain m
  }

  // --- writePlanningToolsJson: output contains only planning tools ---

  test("writePlanningToolsJson should emit only planningToolIds tools") {
    import java.io.StringWriter
    val sw = new StringWriter()
    val gen = jsonFactory.createGenerator(sw)
    gen.writeStartObject()
    AssistantTools.writePlanningToolsJson(gen)
    gen.writeEndObject()
    gen.close()
    val json = sw.toString

    // Every planning tool should appear
    for (id <- ToolId.planningToolIds) {
      json should include(s""""name":"${id.wireName}"""")
    }

    // plan_approach itself must NOT appear (recursion guard at JSON layer)
    json should not include """"name":"plan_approach""""

    // Write-capable tools must not appear
    json should not include """"name":"edit_theory""""
    json should not include """"name":"create_theory""""
    json should not include """"name":"verify_proof""""
  }

  // --- Permissions default ---

  test("plan_approach should have Allow permission (no prompt needed)") {
    ToolPermissions.getDefaultLevel(ToolId.PlanApproach) shouldBe ToolPermissions.Allow
  }

  test("plan_approach should have a human-readable description for prompts") {
    val desc = ToolPermissions.getToolDescription(ToolId.PlanApproach)
    desc should not be empty
    desc.toLowerCase should include("plan")
  }

  // helper: .value-like accessor for Option
  private implicit class OptEx[A](o: Option[A]) {
    def value: A = o.getOrElse(throw new NoSuchElementException("Option was None"))
  }
}
