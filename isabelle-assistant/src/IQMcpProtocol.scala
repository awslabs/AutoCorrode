/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** I/Q MCP protocol data types.
  *
  * Pure data structures representing I/Q JSON-RPC protocol messages and results.
  * No logic — just case classes and enums for type-safe protocol communication.
  */
object IQMcpProtocol {

  /** Type of I/Q explore query. */
  enum ExploreQueryType(val wire: String) {
    case Proof extends ExploreQueryType("proof")
    case Sledgehammer extends ExploreQueryType("sledgehammer")
    case FindTheorems extends ExploreQueryType("find_theorems")
  }

  /** Result from an I/Q explore query (proof verification, sledgehammer, find_theorems).
    * @param success Whether the query completed successfully
    * @param results Query output text (proof state, found theorems, etc.)
    * @param message Human-readable status message
    * @param timedOut Whether the query exceeded its timeout
    * @param error Optional error message if the query failed
    */
  final case class ExploreResult(
      success: Boolean,
      results: String,
      message: String,
      timedOut: Boolean,
      error: Option[String]
  ) {
    /** Extract the best failure message from the result fields.
      * Checks error, message, and results in order, returning the first non-empty value.
      * @param fallback Default message if all fields are empty
      * @return The failure message or fallback
      */
    def failureMessage(fallback: String): String = {
      val candidates = List(
        error.filter(_.trim.nonEmpty),
        Option(message).filter(_.trim.nonEmpty),
        Option(results).filter(_.trim.nonEmpty)
      ).flatten
      candidates.headOption.getOrElse(fallback)
    }
  }

  /** Metadata for a single file from list_files query.
    * @param path Absolute file path
    * @param isTheory Whether the file is a .thy theory file
    * @param isOpen Whether the file is currently open in jEdit
    * @param theoryName Optional parsed theory name (without .thy extension)
    */
  final case class ListedFile(
      path: String,
      isTheory: Boolean,
      isOpen: Boolean,
      theoryName: Option[String]
  )

  /** Aggregated result from list_files query.
    * @param files List of file metadata
    * @param totalCount Total number of files returned
    * @param openCount Count of open buffers
    * @param theoryCount Count of .thy files
    */
  final case class ListFilesResult(
      files: List[ListedFile],
      totalCount: Int,
      openCount: Int,
      theoryCount: Int
  )

  /** Single search match from read_file with mode=Search.
    * @param lineNumber Line number where the match occurred (1-based)
    * @param context Match context (may include surrounding lines)
    */
  final case class ReadFileSearchMatch(
      lineNumber: Int,
      context: String
  )

  /** Result from write_file operations (insert/replace/delete).
    * @param commands List of affected command metadata
    * @param summary Summary statistics about the write operation
    */
  final case class WriteFileResult(
      commands: List[Map[String, Any]],
      summary: Map[String, Any]
  )

  /** Result from open_file operation.
    * @param path Absolute path to the opened file
    * @param created Whether the file was newly created
    * @param overwritten Whether an existing file was overwritten
    * @param opened Whether the file was successfully opened
    * @param inView Whether the file is now visible in a jEdit buffer
    * @param tracked Whether Isabelle has registered a document model for the file;
    *               follow-up tool calls (list_theories, read_theory, ...) only see
    *               the file once this is true
    * @param message Status message from the operation
    */
  final case class OpenFileResult(
      path: String,
      created: Boolean,
      overwritten: Boolean,
      opened: Boolean,
      inView: Boolean,
      tracked: Boolean,
      message: String
  )

  /** How a command was selected for I/Q operations. */
  sealed trait CommandSelection
  /** Current cursor position (default). */
  case object CurrentSelection extends CommandSelection
  /** Specific file offset.
    * @param path File path
    * @param requestedOffset Offset requested by caller
    * @param normalizedOffset Offset after clamping to buffer bounds
    */
  final case class FileOffsetSelection(
      path: String,
      requestedOffset: Option[Int],
      normalizedOffset: Option[Int]
  ) extends CommandSelection
  /** Command matching a text pattern in a file. */
  final case class FilePatternSelection(path: String, pattern: String)
      extends CommandSelection
  /** Unknown selection type (fallback). */
  final case class UnknownSelection(raw: String) extends CommandSelection

  /** Metadata about an Isabelle command (from PIDE).
    * @param id PIDE command ID
    * @param length Source text length in characters
    * @param source Full source text of the command
    * @param keyword Isabelle keyword (lemma, theorem, apply, etc.)
    * @param nodePath Optional file path of the command's theory
    * @param startOffset Optional buffer offset where command starts
    * @param endOffset Optional buffer offset where command ends
    */
  final case class CommandInfo(
      id: Long,
      length: Int,
      source: String,
      keyword: String,
      nodePath: Option[String],
      startOffset: Option[Int],
      endOffset: Option[Int]
  )

  /** Result from resolving a command selection to a specific command.
    * @param selection The command selection mode used
    * @param command Metadata about the resolved command
    */
  final case class ResolvedCommandTarget(
      selection: CommandSelection,
      command: CommandInfo
  )

  /** Structured analysis of a proof goal extracted from PIDE markup.
    * @param hasGoal Whether a goal is present at the cursor position
    * @param goalText The rendered goal state text
    * @param numSubgoals Count of subgoals (parsed from PIDE structure)
    * @param freeVars Free (unbound) variables in the goal
    * @param constants Constants referenced in the goal
    * @param analysisError Optional error if goal parsing failed
    */
  final case class GoalInfo(
      hasGoal: Boolean,
      goalText: String,
      numSubgoals: Int,
      freeVars: List[String],
      constants: List[String],
      analysisError: Option[String]
  )

  /** Combined context information at a cursor position.
    * @param selection How the command was selected (current, file_offset, pattern)
    * @param command Metadata about the Isabelle command at the selection
    * @param inProofContext Whether the cursor is inside a proof block
    * @param hasGoal Whether there's an active proof goal
    * @param goal Structured goal analysis (empty if hasGoal is false)
    */
  final case class ContextInfoResult(
      selection: CommandSelection,
      command: CommandInfo,
      inProofContext: Boolean,
      hasGoal: Boolean,
      goal: GoalInfo
  )

  /** Named entity from a theory file (lemma, definition, datatype, etc.).
    * @param line Line number where the entity is defined (1-based)
    * @param keyword Isabelle keyword (lemma, definition, fun, etc.)
    * @param name Entity name
    * @param startOffset Buffer offset where entity starts
    * @param endOffset Buffer offset where entity ends
    * @param sourcePreview Short preview of the entity source
    */
  final case class EntityInfo(
      line: Int,
      keyword: String,
      name: String,
      startOffset: Int,
      endOffset: Int,
      sourcePreview: String
  )

  /** Result from get_entities query.
    * @param path File path
    * @param nodeName Isabelle node name
    * @param totalEntities Total count of entities in the theory
    * @param returnedEntities Number of entities actually returned
    * @param truncated Whether results were truncated due to limit
    * @param entities List of entity metadata
    */
  final case class EntitiesResult(
      path: String,
      nodeName: String,
      totalEntities: Int,
      returnedEntities: Int,
      truncated: Boolean,
      entities: List[EntityInfo]
  )

  /** Result from get_type_at_selection query.
    * @param selection Command selection metadata
    * @param command Command metadata
    * @param hasType Whether type information was found
    * @param typeText Formatted type information string
    * @param term The term whose type was queried
    * @param typ The type string
    * @param line Line number
    * @param startOffset Optional start offset of the typed term
    * @param endOffset Optional end offset of the typed term
    * @param message Optional status/error message
    */
  final case class TypeAtSelectionResult(
      selection: CommandSelection,
      command: CommandInfo,
      hasType: Boolean,
      typeText: String,
      term: String,
      typ: String,
      line: Int,
      startOffset: Option[Int],
      endOffset: Option[Int],
      message: Option[String]
  )

  /** Single proof block (lemma/theorem...qed/done) metadata.
    * @param proofText Full source text of the proof block
    * @param startOffset Buffer offset where proof starts
    * @param endOffset Buffer offset where proof ends
    * @param startLine Line number where proof starts (1-based)
    * @param endLine Line number where proof ends (1-based)
    * @param commandCount Number of Isabelle commands in the proof
    * @param isApplyStyle Whether the proof uses apply-style (vs structured Isar)
    */
  final case class ProofBlockInfo(
      proofText: String,
      startOffset: Int,
      endOffset: Int,
      startLine: Int,
      endLine: Int,
      commandCount: Int,
      isApplyStyle: Boolean
  )

  enum ProofBlocksScope(val wire: String) {
    case Selection extends ProofBlocksScope("selection")
    case File extends ProofBlocksScope("file")
  }

  /** Result from get_proof_blocks query.
    * @param scope Whether blocks are for Selection (at cursor) or File (entire file)
    * @param path File path (for File scope)
    * @param nodeName Isabelle node name
    * @param totalBlocks Total count of proof blocks found
    * @param returnedBlocks Number of blocks actually returned
    * @param truncated Whether results were truncated
    * @param proofBlocks List of proof block metadata
    * @param selection Command selection metadata (for Selection scope)
    * @param command Command metadata (for Selection scope)
    * @param message Optional status/error message
    */
  final case class ProofBlocksResult(
      scope: ProofBlocksScope,
      path: Option[String],
      nodeName: Option[String],
      totalBlocks: Int,
      returnedBlocks: Int,
      truncated: Boolean,
      proofBlocks: List[ProofBlockInfo],
      selection: Option[CommandSelection],
      command: Option[CommandInfo],
      message: Option[String]
  )

  /** Result from get_proof_context query (local facts and assumptions).
    * @param selection Command selection metadata
    * @param command Command metadata
    * @param success Whether the query succeeded
    * @param timedOut Whether the query exceeded timeout
    * @param hasContext Whether context facts were found
    * @param context Formatted context text (local facts, assumptions)
    * @param message Human-readable status message
    * @param error Optional error message if query failed
    */
  final case class ProofContextResult(
      selection: CommandSelection,
      command: CommandInfo,
      success: Boolean,
      timedOut: Boolean,
      hasContext: Boolean,
      context: String,
      message: String,
      error: Option[String]
  )

  /** Result from get_definitions query.
    * @param selection Command selection metadata
    * @param command Command metadata
    * @param names List of names that were looked up
    * @param success Whether the query succeeded
    * @param timedOut Whether the query exceeded timeout
    * @param hasDefinitions Whether definitions were found
    * @param definitions Formatted definition text
    * @param message Human-readable status message
    * @param error Optional error message if query failed
    */
  final case class DefinitionsResult(
      selection: CommandSelection,
      command: CommandInfo,
      names: List[String],
      success: Boolean,
      timedOut: Boolean,
      hasDefinitions: Boolean,
      definitions: String,
      message: String,
      error: Option[String]
  )

  enum DiagnosticSeverity(val wire: String) {
    case Error extends DiagnosticSeverity("error")
    case Warning extends DiagnosticSeverity("warning")
  }

  enum DiagnosticScope(val wire: String) {
    case Selection extends DiagnosticScope("selection")
    case File extends DiagnosticScope("file")
  }

  /** A single error or warning diagnostic from PIDE.
    * @param line Line number (1-based)
    * @param startOffset Character offset where diagnostic starts
    * @param endOffset Character offset where diagnostic ends
    * @param message Diagnostic message text
    */
  final case class DiagnosticEntry(
      line: Int,
      startOffset: Int,
      endOffset: Int,
      message: String
  )

  /** Result from get_diagnostics query.
    * @param scope Whether diagnostics are for Selection (at cursor) or File (entire buffer)
    * @param severity Error or Warning
    * @param count Total diagnostic count
    * @param diagnostics List of diagnostic entries with line numbers and messages
    * @param path File path (for File scope)
    * @param nodeName Isabelle node name
    * @param selection Command selection metadata (for Selection scope)
    * @param command Command metadata (for Selection scope)
    */
  final case class DiagnosticsResult(
      scope: DiagnosticScope,
      severity: DiagnosticSeverity,
      count: Int,
      diagnostics: List[DiagnosticEntry],
      path: Option[String],
      nodeName: Option[String],
      selection: Option[CommandSelection],
      command: Option[CommandInfo]
  )

  /** Result from get_file_stats query.
    * @param path File path
    * @param lineCount Total line count
    * @param entityCount Count of named entities (lemmas, definitions, etc.)
    * @param fullyProcessed Whether all commands are finished processing
    * @param hasErrors Whether the file has any errors
    * @param errorCount Total error count
    * @param warningCount Total warning count
    */
  final case class FileStatsResult(
      path: String,
      lineCount: Int,
      entityCount: Int,
      fullyProcessed: Boolean,
      hasErrors: Boolean,
      errorCount: Int,
      warningCount: Int
  )

  /** Result from get_processing_status query.
    * @param path File path
    * @param fullyProcessed Whether all commands are finished processing
    * @param unprocessed Count of unprocessed commands
    * @param running Count of running commands
    * @param finished Count of finished commands
    * @param failed Count of failed commands
    * @param hasErrors Whether there are any failed commands
    * @param errorCount Count of failed commands (same as failed)
    * @param consolidated Whether PIDE has consolidated all results
    */
  final case class ProcessingStatusResult(
      path: String,
      fullyProcessed: Boolean,
      unprocessed: Int,
      running: Int,
      finished: Int,
      failed: Int,
      hasErrors: Boolean,
      errorCount: Int,
      consolidated: Boolean
  )

  /** Single sorry/oops position from get_sorry_positions.
    * @param line Line number where sorry/oops appears (1-based)
    * @param keyword The keyword (sorry or oops)
    * @param offset Character offset where it appears
    * @param inProof Name of enclosing proof (lemma name or description)
    */
  final case class SorryPosition(
      line: Int,
      keyword: String,
      offset: Int,
      inProof: String
  )

  /** Result from get_sorry_positions query.
    * @param path File path
    * @param count Total count of sorry/oops commands
    * @param positions List of sorry position metadata
    */
  final case class SorryPositionsResult(
      path: String,
      count: Int,
      positions: List[SorryPosition]
  )
}