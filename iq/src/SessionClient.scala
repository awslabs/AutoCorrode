/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/* MCP registration for the session-generic diagnostic tools (SessionTools).

   SessionClient is the bridge between SessionTools (pure analyses over an
   isabelle.Session) and a generic McpServer: it declares each tool's wire
   schema, decodes/validates params, resolves the target node or command, calls
   the matching SessionTools function, and returns the result map. It adds no
   analysis of its own.

   File-scope tools take a `path` (resolved to a loaded node via
   SessionTools.resolveNode). Command-scope tools take `path` + `offset` or
   `pattern` (resolved via SessionTools.resolveCommand).

   Host integration: a host (ic2 today; I/Q can adopt it) constructs
   `new SessionClient(session, server).register()`. The set is read-only and
   session-generic — no jEdit, no auth/path-allowlist policy (a host that needs
   those wraps the handlers or filters paths before calling). In `package
   isabelle` so it is shareable into `package isabelle.ic2`. */

package isabelle


final class SessionClient(session: Session, server: McpServer) {

  /* ---- schema DSL (mirrors IRTools' style) ---- */

  private def schema(props: Map[String, Any], required: List[String] = Nil): Map[String, Any] =
    Map("type" -> "object", "properties" -> props, "additionalProperties" -> false) ++
      (if (required.nonEmpty) Map("required" -> required) else Map.empty)
  private def str(desc: String): Map[String, Any] = Map("type" -> "string", "description" -> desc)
  private def int(desc: String): Map[String, Any] = Map("type" -> "integer", "description" -> desc)
  private def bool(desc: String): Map[String, Any] = Map("type" -> "boolean", "description" -> desc)

  private val pathParam = "path" -> str("Theory file path (a loaded/checked session node; " +
    "partial paths are completed against loaded nodes)")

  /** Run a tool via the shared SessionTools.dispatch (the same mapping the wire
    * `query` op uses), wrapping its result map / error as an McpTool result. */
  private def run(tool: String)(params: McpToolParams): Either[String, McpToolResult] =
    SessionTools.dispatch(session, tool, params.toMap).map(McpToolResult.fromMap)


  /* ---- tools (wire order is part of the contract). The schemas/descriptions
   * are the MCP-facing contract; the handlers all route through the shared
   * SessionTools.dispatch, so analysis logic lives in exactly one place. ---- */

  def tools: List[McpTool] = List(
    McpTool("list_files",
      "List the theory nodes the session knows about (loaded/checked theories " +
        "and their imports) with each node's processing status (the document " +
        "graph, not editor buffers).",
      schema(Map("filter_theory" -> bool("Keep only theory nodes (true) or only non-theory (false)"))),
      run("list_files")),

    McpTool("get_processing_status",
      "PIDE processing status of a theory node: counts of unprocessed, running, " +
        "finished, failed commands, and whether it is fully processed/consolidated.",
      schema(Map(pathParam), List("path")),
      run("get_processing_status")),

    McpTool("get_document_info",
      "Whole-theory status: total/finished/unprocessed/failed command counts and " +
        "error/warning totals. Use to check overall state of a theory.",
      schema(Map(pathParam), List("path")),
      run("get_document_info")),

    McpTool("get_diagnostics",
      "Errors or warnings, either for a whole file (scope='file', default) or at a " +
        "command selection (scope='selection' with offset or pattern).",
      schema(Map(
        pathParam,
        "severity" -> str("'error' (default) or 'warning'"),
        "scope" -> str("'file' (default) or 'selection'"),
        "offset" -> int("Character offset (selection scope)"),
        "pattern" -> str("Unique text pattern (selection scope)")),
        List("path")),
      run("get_diagnostics")),

    McpTool("get_sorry_positions",
      "Positions of sorry/oops placeholders in a theory, with line numbers and " +
        "enclosing proof context.",
      schema(Map(pathParam), List("path")),
      run("get_sorry_positions")),

    McpTool("get_entities",
      "Enumerate declaration commands (lemma/definition/fun/datatype/locale/...) in " +
        "a theory with name, keyword, line, and offsets.",
      schema(Map(pathParam, "max_results" -> int("Maximum entities to return (default 500)")),
        List("path")),
      run("get_entities")),

    McpTool("get_proof_blocks",
      "Extract proof blocks from a theory (file scope) — each block's text, line " +
        "range, command count, and whether it is apply-style.",
      schema(Map(pathParam, "min_chars" -> int("Minimum block length to report (default 0)")),
        List("path")),
      run("get_proof_blocks")),

    McpTool("get_command_info",
      "Command metadata, status, and output text (errors/warnings/writeln) at a " +
        "source selection (path + offset or pattern). For the proof goal state " +
        "use get_context_info — the goal is not part of a command's output text.",
      schema(Map(pathParam,
        "offset" -> int("Character offset (alternative to pattern)"),
        "pattern" -> str("Unique text pattern (alternative to offset)")),
        List("path")),
      run("get_command_info")),

    McpTool("get_context_info",
      "Read-only context introspection at a source selection: command metadata, " +
        "proof-context status, and goal-state (text, subgoals, free vars, constants).",
      schema(Map(pathParam,
        "offset" -> int("Character offset (alternative to pattern)"),
        "pattern" -> str("Unique text pattern (alternative to offset)")),
        List("path")),
      run("get_context_info"))
  )

  /** Register all session tools on the server; Left at the first failure. */
  def register(): Either[String, Unit] = server.registerAll(tools)

  /** Unregister all session tools. */
  def unregister(): Unit = tools.foreach(t => server.unregister(t.name))
}
