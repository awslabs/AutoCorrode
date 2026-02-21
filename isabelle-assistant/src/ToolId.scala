/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Canonical identifier for assistant tools.
  *
  * Using a closed enum prevents drift and typo-based bugs across tool
  * definitions, execution dispatch, and permission policy.
  */
enum ToolId(val wireName: String) {
  case ReadTheory extends ToolId("read_theory")
  case ListTheories extends ToolId("list_theories")
  case SearchInTheory extends ToolId("search_in_theory")
  case GetGoalState extends ToolId("get_goal_state")
  case GetProofContext extends ToolId("get_proof_context")
  case FindTheorems extends ToolId("find_theorems")
  case VerifyProof extends ToolId("verify_proof")
  case RunSledgehammer extends ToolId("run_sledgehammer")
  case RunNitpick extends ToolId("run_nitpick")
  case RunQuickcheck extends ToolId("run_quickcheck")
  case GetType extends ToolId("get_type")
  case GetCommandText extends ToolId("get_command_text")
  case GetErrors extends ToolId("get_errors")
  case GetDefinitions extends ToolId("get_definitions")
  case ExecuteStep extends ToolId("execute_step")
  case TraceSimplifier extends ToolId("trace_simplifier")
  case GetProofBlock extends ToolId("get_proof_block")
  case GetContextInfo extends ToolId("get_context_info")
  case SearchAllTheories extends ToolId("search_all_theories")
  case GetDependencies extends ToolId("get_dependencies")
  case GetWarnings extends ToolId("get_warnings")
  case SetCursorPosition extends ToolId("set_cursor_position")
  case EditTheory extends ToolId("edit_theory")
  case TryMethods extends ToolId("try_methods")
  case GetEntities extends ToolId("get_entities")
  case WebSearch extends ToolId("web_search")
  case CreateTheory extends ToolId("create_theory")
  case OpenTheory extends ToolId("open_theory")
  case AskUser extends ToolId("ask_user")
  case TaskListAdd extends ToolId("task_list_add")
  case TaskListDone extends ToolId("task_list_done")
  case TaskListIrrelevant extends ToolId("task_list_irrelevant")
  case TaskListNext extends ToolId("task_list_next")
  case TaskListShow extends ToolId("task_list_show")
  case TaskListGet extends ToolId("task_list_get")
}

object ToolId {
  private val byWire: Map[String, ToolId] =
    ToolId.values.map(t => t.wireName -> t).toMap

  def fromWire(name: String): Option[ToolId] = byWire.get(name)

  def displayName(id: ToolId): String =
    id.wireName.split("_").map(_.capitalize).mkString(" ")
}
