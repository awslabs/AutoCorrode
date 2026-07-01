/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/* Standalone I/R REPL tool provider.

   Owns all repl_* tools and registers them with a generic McpServer.

   Depends on the running I/R backend only through the injected IRConnection
   seam (connect / client / session / resolveFile) — no jEdit, no IQUtils. The
   production jEdit adapter (JEditIRConnection, over IQExploreDockable) lives on
   the IQ side; a headless host (e.g. ic2) supplies its own IRConnection without
   touching this class. In `package isabelle` so it is shareable into
   `package isabelle.ic2`. */

// In `package isabelle` (as Extended_Query_Operation.scala), so this provider
// is reachable from `package isabelle.ic2` too. Session/Text/Command et al. are
// then in scope unqualified.
package isabelle


/** The I/R backend connection seam.
  *
  *   - `connect` drives whatever lifecycle the host needs (start ML_Repl +
  *     repl.py, connect a client) and returns the connected I/R directory on
  *     success, or a failure message on failure;
  *   - `client` is the connected IRClient used by the per-tool handlers;
  *   - `session` is the live Isabelle session whose document the source-location
  *     resolver inspects (PIDE in jEdit, Headless.Session in ic2);
  *   - `resolveFile` maps a (possibly partial) file argument to its completed
  *     absolute path and full text. The jEdit host completes against open
  *     buffers and reads the live (unsaved) buffer text; a headless host
  *     completes against the session's loaded nodes and reads from disk. */
trait IRConnection {
  def connect(irHome: Option[String]): Either[String, String]
  def client: Option[IRClient]
  def session: Session
  def resolveFile(file: String): Either[String, (String, String)]
}


final class IRTools(server: McpServer, conn: IRConnection) {

  /* ---- schema DSL ---- */

  private def schema(props: Map[String, Any], required: List[String] = Nil): Map[String, Any] =
    Map("type" -> "object", "properties" -> props, "additionalProperties" -> false) ++
      (if (required.nonEmpty) Map("required" -> required) else Map.empty)
  private def str(desc: String): Map[String, Any] = Map("type" -> "string", "description" -> desc)
  private def int(desc: String): Map[String, Any] = Map("type" -> "integer", "description" -> desc)
  private val replPrefix = "I/R REPL: "
  private val replParam = "repl" -> str("REPL session identifier")

  /* ---- parameter extractors ---- */

  private def strParam(params: Map[String, Any], key: String): Either[String, String] =
    params.get(key) match {
      case Some(s: String) if s.nonEmpty => Right(s)
      case _ => Left(s"Missing required parameter: $key")
    }

  private def intParam(params: Map[String, Any], key: String): Either[String, Int] =
    params.get(key) match {
      case Some(n: Long) => Right(n.toInt)
      case Some(n: Int) => Right(n)
      case Some(n: Double) => Right(n.toInt)
      case _ => Left(s"Missing required integer parameter: $key")
    }

  private def optIntParam(params: Map[String, Any], key: String): Option[Int] =
    params.get(key) match {
      case Some(n: Long) => Some(n.toInt)
      case Some(n: Int) => Some(n)
      case Some(n: Double) => Some(n.toInt)
      case _ => None
    }

  /** Run `f` against the connected IRClient, mapping exceptions to a Left. */
  private def withIR(f: IRClient => String): Either[String, Map[String, Any]] = {
    conn.client match {
      case Some(c) if c.isConnected =>
        try Right(Map("text" -> f(c)))
        catch { case ex: Exception => Left(s"I/R error: ${ex.getMessage}") }
      case _ =>
        Left("I/R REPL not connected. Call repl_connect first.")
    }
  }

  /* ---- handlers ---- */

  private val replConnect: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    val home = p.get("ir_home").collect { case s: String if s.nonEmpty => s }
    conn.connect(home).map(dir =>
      McpToolResult.fromMap(Map("text" -> s"I/R REPL connected (ir_home=$dir).")))
  }

  private val replInit: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for {
      repl <- strParam(p, "repl")
      theories = p.get("theories") match {
        case Some(l: List[_]) => l.collect { case s: String => s }
        case _ => Nil
      }
      r <- withIR(_.init(repl, theories))
    } yield McpToolResult.fromMap(r)
  }

  /** Resolve a source location (file + offset or pattern) to a document node +
    * command id, then create a REPL from that document state.
    *
    * The host-specific part — completing the file argument and reading its text
    * — is the injected `conn.resolveFile`. Everything else is session-generic:
    * pin the character offset (from the explicit offset, or the end of a unique
    * substring match via IQNormalization), then look up the command spanning it
    * in `conn.session`'s snapshot. Works for the live PIDE session and a headless
    * Headless.Session alike. */
  private def initFromSourceLocation(
    client: IRClient, repl: String, file: String,
    offset: Option[Int], pattern: Option[String]
  ): String = {
    val (resolvedPath, content) = conn.resolveFile(file) match {
      case Right(pc) => pc
      case Left(err) => throw new IllegalArgumentException(err)
    }
    val charOffset =
      offset match {
        case Some(o) =>
          // Clamp to the document, matching IQUtils.normalizeRequestedOffset.
          if (content.isEmpty) 0 else math.max(0, math.min(o, content.length - 1))
        case None =>
          pattern.map(_.trim).filter(_.nonEmpty) match {
            case Some(pat) =>
              IQNormalization.findUniqueMatch(content, pat) match {
                case Right((start, _)) => start + pat.length - 1
                case Left(IQNormalization.SubstringNotFound) =>
                  throw new IllegalArgumentException(s"Pattern '$pat' not found in $resolvedPath")
                case Left(IQNormalization.SubstringNotUnique) =>
                  throw new IllegalArgumentException(
                    s"Pattern '$pat' matches multiple locations in $resolvedPath; use 'offset'")
                case Left(IQNormalization.SubstringEmpty) =>
                  throw new IllegalArgumentException("Pattern cannot be empty")
              }
            case None =>
              throw new IllegalArgumentException("specify either offset or pattern")
          }
      }
    commandAt(resolvedPath, charOffset) match {
      case Right(command) =>
        val node = command.node_name.node
        val cmdId = command.id.toInt
        client.initFromDocument(repl, node, cmdId)
      case Left(err) => throw new IllegalArgumentException(err)
    }
  }

  /** The command spanning `offset` in `filePath`'s node, looked up in the live
    * session snapshot. Session-generic (no jEdit): rather than jEdit's
    * Resources.node_name(path) (which the base Resources lacks), find the loaded
    * node whose file path matches `filePath` directly in the document graph. */
  private def commandAt(filePath: String, offset: Int): Either[String, Command] = {
    val target = new java.io.File(filePath)
    val snapshot = conn.session.snapshot()
    val nodeName =
      snapshot.version.nodes.iterator
        .map(_._1)
        .find(n => n.node.nonEmpty && File.eq(n.path.file, target))
    nodeName match {
      case None =>
        Left(s"Node not loaded for $filePath (is it checked / a session node?)")
      case Some(name) =>
        val node = snapshot.get_node(name)
        if (node == null || node.commands.isEmpty)
          Left(s"Node empty for $filePath (is it checked / a session node?)")
        else
          node.command_iterator(Text.Range(offset, offset + 1)).toList.headOption match {
            case Some((command, _)) => Right(command)
            case None => Left(s"No command found at offset $offset in $filePath")
          }
    }
  }

  private val replInitFromSource: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for {
      repl <- strParam(p, "repl")
      file <- strParam(p, "file")
      r <- {
        val offset = optIntParam(p, "offset")
        val pattern = p.get("pattern").collect { case s: String if s.nonEmpty => s }
        withIR(initFromSourceLocation(_, repl, file, offset, pattern))
      }
    } yield McpToolResult.fromMap(r)
  }

  private val replFork: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for {
      repl <- strParam(p, "repl")
      newRepl <- strParam(p, "new_repl")
      idx <- intParam(p, "state_idx")
      r <- withIR(_.fork(repl, newRepl, idx))
    } yield McpToolResult.fromMap(r)
  }

  private val replStep: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for { repl <- strParam(p, "repl"); t <- strParam(p, "isar_text"); r <- withIR(_.step(repl, t)) }
    yield McpToolResult.fromMap(r)
  }

  private val replShow: McpToolParams => Either[String, McpToolResult] = params =>
    strParam(params.toMap, "repl").flatMap(r => withIR(_.show(r))).map(McpToolResult.fromMap)

  private val replState: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for { repl <- strParam(p, "repl"); i <- intParam(p, "state_idx"); r <- withIR(_.state(repl, i)) }
    yield McpToolResult.fromMap(r)
  }

  private val replText: McpToolParams => Either[String, McpToolResult] = params =>
    strParam(params.toMap, "repl").flatMap(r => withIR(_.text(r))).map(McpToolResult.fromMap)

  private val replEdit: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for { repl <- strParam(p, "repl"); idx <- intParam(p, "idx"); t <- strParam(p, "isar_text"); r <- withIR(_.edit(repl, idx, t)) }
    yield McpToolResult.fromMap(r)
  }

  private val replReplay: McpToolParams => Either[String, McpToolResult] = params =>
    strParam(params.toMap, "repl").flatMap(r => withIR(_.replay(r))).map(McpToolResult.fromMap)

  private val replTruncate: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for { repl <- strParam(p, "repl"); i <- intParam(p, "idx"); r <- withIR(_.truncate(repl, i)) }
    yield McpToolResult.fromMap(r)
  }

  private val replBack: McpToolParams => Either[String, McpToolResult] = params =>
    strParam(params.toMap, "repl").flatMap(r => withIR(_.back(r))).map(McpToolResult.fromMap)

  private val replMerge: McpToolParams => Either[String, McpToolResult] = params =>
    strParam(params.toMap, "repl").flatMap(r => withIR(_.merge(r))).map(McpToolResult.fromMap)

  private val replRemove: McpToolParams => Either[String, McpToolResult] = params =>
    strParam(params.toMap, "repl").flatMap(r => withIR(_.remove(r))).map(McpToolResult.fromMap)

  private val replList: McpToolParams => Either[String, McpToolResult] =
    _ => withIR(_.repls()).map(McpToolResult.fromMap)

  private val replSledgehammer: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for { repl <- strParam(p, "repl"); s <- intParam(p, "timeout_secs"); r <- withIR(_.sledgehammer(repl, s)) }
    yield McpToolResult.fromMap(r)
  }

  private val replFindTheorems: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for { repl <- strParam(p, "repl"); q <- strParam(p, "query"); r <- withIR(_.findTheorems(repl, p.get("max_results").collect { case n: Long => n.toInt }.getOrElse(40), q)) }
    yield McpToolResult.fromMap(r)
  }

  private val replTimeout: McpToolParams => Either[String, McpToolResult] = params => {
    val p = params.toMap
    for { repl <- strParam(p, "repl"); s <- intParam(p, "secs"); r <- withIR(_.timeout(repl, s)) }
    yield McpToolResult.fromMap(r)
  }

  private val replRaw: McpToolParams => Either[String, McpToolResult] = params =>
    strParam(params.toMap, "ml_code").flatMap(c => withIR(_.send(c))).map(McpToolResult.fromMap)

  /* ---- tools (wire order is part of the contract — see tools/list) ---- */

  def tools: List[McpTool] = List(
    McpTool("repl_connect",
      replPrefix + "Connect to the I/R REPL backend. MUST be called before any other repl_* tool. " +
        "Starts ML_Repl and repl.py if not already running. " +
        "Pass ir_home if the I/R directory cannot be auto-detected.",
      schema(Map(
        "ir_home" -> str("Path to the I/R directory containing repl.py (optional; auto-detected from ISABELLE_IR_HOME or document model)")),
        List.empty[String]),
      replConnect),
    McpTool("repl_init",
      replPrefix + "Create a new REPL session importing theories.",
      schema(Map(replParam,
        "theories" -> Map("type" -> "array", "items" -> Map("type" -> "string"),
          "description" -> "Theory names to import, e.g. [\"Main\"]")),
        List("repl", "theories")),
      replInit),
    McpTool("repl_init_from_source",
      replPrefix + "Create a REPL from a source location in an open file. Specify file + offset or file + pattern.",
      schema(Map(replParam,
        "file" -> str("Theory file path (auto-completed against open files)"),
        "offset" -> int("Character offset in the file (alternative to pattern)"),
        "pattern" -> str("Unique text pattern in the file (alternative to offset)")),
        List("repl", "file")),
      replInitFromSource),
    McpTool("repl_fork",
      replPrefix + "Fork a sub-REPL from an existing REPL at a given state index (0=base, -1=latest).",
      schema(Map(replParam,
        "new_repl" -> str("New REPL identifier"),
        "state_idx" -> int("State index to fork from (0=base, -1=latest)")),
        List("repl", "new_repl", "state_idx")),
      replFork),
    McpTool("repl_step",
      replPrefix + "Execute Isar text as the next step. IMPORTANT: If a step FAILS, the REPL state is UNCHANGED — do NOT call repl_back to undo a failed step.",
      schema(Map(replParam, "isar_text" -> str("Isar command text")), List("repl", "isar_text")),
      replStep),
    McpTool("repl_show",
      replPrefix + "Show REPL: origin, steps, staleness.",
      schema(Map(replParam), List("repl")),
      replShow),
    McpTool("repl_state",
      replPrefix + "Show proof state at a step index (0=base, -1=latest).",
      schema(Map(replParam, "state_idx" -> int("State index")), List("repl", "state_idx")),
      replState),
    McpTool("repl_text",
      replPrefix + "Print concatenated Isar text of all steps.",
      schema(Map(replParam), List("repl")),
      replText),
    McpTool("repl_edit",
      replPrefix + "Replace step at index with new Isar text.",
      schema(Map(replParam,
        "idx" -> int("Step index to replace"),
        "isar_text" -> str("New Isar text")),
        List("repl", "idx", "isar_text")),
      replEdit),
    McpTool("repl_replay",
      replPrefix + "Re-execute all stale steps.",
      schema(Map(replParam), List("repl")),
      replReplay),
    McpTool("repl_truncate",
      replPrefix + "Keep steps 0..idx, discard the rest. Use -1 to revert last step.",
      schema(Map(replParam, "idx" -> int("Keep steps up to this index")), List("repl", "idx")),
      replTruncate),
    McpTool("repl_back",
      replPrefix + "Revert the last SUCCESSFUL step. Failed steps don't change the REPL state.",
      schema(Map(replParam), List("repl")),
      replBack),
    McpTool("repl_merge",
      replPrefix + "Inline sub-REPL back into its parent.",
      schema(Map(replParam), List("repl")),
      replMerge),
    McpTool("repl_remove",
      replPrefix + "Delete a REPL and all its sub-REPLs.",
      schema(Map(replParam), List("repl")),
      replRemove),
    McpTool("repl_list",
      replPrefix + "List all REPL sessions.",
      schema(Map.empty),
      replList),
    McpTool("repl_sledgehammer",
      replPrefix + "Run sledgehammer on the proof goal.",
      schema(Map(replParam, "timeout_secs" -> int("Timeout in seconds")), List("repl", "timeout_secs")),
      replSledgehammer),
    McpTool("repl_find_theorems",
      replPrefix + "Search for theorems.",
      schema(Map(replParam,
        "query" -> str("Search query"),
        "max_results" -> int("Maximum results (default 40)")),
        List("repl", "query")),
      replFindTheorems),
    McpTool("repl_timeout",
      replPrefix + "Set step timeout in seconds for a specific REPL (0=unlimited, default 10s). NOTE: DO NOT set this to values >10s unless you have " +
        "a specific reason to. Calls like `metis`, `auto`, `blast`, `force`, should NOT take longer than 5s. Even if they do, and the call " +
        "ultimately succeeds, it points at a proof that ought to be broken down further. ONLY use a large timeout if you work with very large " +
        "scripts or in special circumstances where, exceptionally, a large timeout is expected / tolerated.",
      schema(Map(replParam, "secs" -> int("Timeout in seconds")), List("repl", "secs")),
      replTimeout),
    McpTool("repl_raw",
      replPrefix + "Send a raw ML expression to the REPL.",
      schema(Map("ml_code" -> str("ML expression")), List("ml_code")),
      replRaw)
  )

  /** Register all repl_* tools with the server. */
  def register(): Either[String, Unit] = server.registerAll(tools)

  /** Unregister all repl_* tools. */
  def unregister(): Unit = tools.foreach(t => server.unregister(t.name))
}
