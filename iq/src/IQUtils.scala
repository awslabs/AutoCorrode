/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

import org.gjt.sp.jedit.{View, jEdit}
import scala.util.{Try, Success, Failure}
import java.nio.file.Paths
import java.io.File

/**
 * Utilities for I/Q Explore functionality.
 * Contains pure functions that can be shared between GUI and MCP implementations.
 */
object IQUtils {

  /**
   * Strips the file extension from a path string.
   *
   * @param path The file path
   * @return Path without extension
   */
  def stripExtension(path: String): String = {
    val file = new File(path)
    val name = file.getName
    val dot = name.lastIndexOf('.')
    val nameWithoutExt = if (dot > 0) name.substring(0, dot) else name
    val parent = file.getParent
    if (parent == null || parent.isEmpty) nameWithoutExt
    else new File(parent, nameWithoutExt).getPath
  }

  /**
   * Gets all tracked/open files from Isabelle/jEdit.
   *
   * @return List of file paths as strings
   */
  def getAllTrackedFiles(): List[String] = {
    GUI_Thread.now {
      val models_map = Document_Model.get_models_map()
      models_map.keys.map(_.node).toList
    }
  }

  /**
   * Auto-completes a partial file path by finding exactly one match among provided candidates.
   *
   * @param partialPath The partial file path to match (e.g., "Foo/Bar.thy")
   * @param candidates Candidate full paths to match against
   * @return Either the full file path if exactly one match, or an error message
   */
  def autoCompleteFilePathFromCandidates(
    partialPath: String,
    candidates: List[String],
    trackedOnly: Boolean = true
  ): Either[String, String] = {
    val partialPathNoExt = stripExtension(partialPath).toLowerCase
    val matches = candidates
      .filter(fullPath => stripExtension(fullPath).toLowerCase.endsWith(partialPathNoExt))
      .distinct
      .sorted

    matches.size match {
      case 0 =>
        if (trackedOnly) Left(s"No file found matching '$partialPath'")
        else Right(partialPath)
      case 1 => Right(matches.head)
      case _ => Left(s"Multiple files found matching '$partialPath': ${matches.mkString(", ")}")
    }
  }

  /**
   * Auto-completes a partial file path by finding exactly one match among tracked/open files.
   *
   * @param partialPath The partial file path to match (e.g., "Foo/Bar.thy")
   * @return Either the full file path if exactly one match, or an error message
   */
  def autoCompleteFilePath(partialPath: String, trackedOnly: Boolean = true, allowNonexisting: Boolean = false): Either[String, String] = {
    try {
      // Get all tracked files
      val trackedFiles = getAllTrackedFiles()
      val resultPath = autoCompleteFilePathFromCandidates(partialPath, trackedFiles, trackedOnly) match {
        case Left(error) => return Left(error)
        case Right(path) => path
      }

      // Check if file exists (only if allowNonexisting is false)
      if (!allowNonexisting && !new java.io.File(resultPath).exists()) {
        Left(s"File does not exist: $resultPath")
      } else {
        Right(resultPath)
      }
    } catch {
      case ex: Exception => Left(s"Error during file path auto-completion: ${ex.getMessage}")
    }
  }

  /**
   * Finds a command at a specific file offset.
   *
   * @param filePath The path to the theory file
   * @param offset The character offset in the file
   * @return Try[Command] containing the command if found, or failure with error message
   */
  def findCommandAtFileOffset(filePath: String, offset: Int): Try[Command] = {
    Try {
      // Convert file path to node name
      val node_name = PIDE.resources.node_name(filePath)
      val snapshot = PIDE.session.snapshot()

      // Get the node from the snapshot
      val node = snapshot.get_node(node_name)

      if (node != null && node.commands.nonEmpty) {
        // Find the command that contains the given offset
        val targetRange = Text.Range(offset, offset + 1)
        val commandsAtOffset = node.command_iterator(targetRange).toList

        commandsAtOffset.headOption match {
          case Some((command, _)) => command
          case None => throw new RuntimeException(s"No command found at offset $offset in $filePath")
        }
      } else {
        throw new RuntimeException(s"Node not found or empty for $filePath")
      }
    }
  }

  /**
   * Error types for substring search operations
   */
  sealed trait SubstringSearchError
  case object SubstringNotFound extends SubstringSearchError
  case object SubstringNotUnique extends SubstringSearchError
  case object SubstringEmpty extends SubstringSearchError

  /**
   * Counts the number of leading spaces in a string.
   */
  private def countLeadingSpaces(str: String): Int = {
    str.takeWhile(_ == ' ').length
  }

  /**
   * Finds the offset of a substring within a multiline string.
   * Handles Unicode characters properly by normalizing both strings and mapping positions back.
   *
   * Relaxation: When input and output string start with exactly the same number of spaces,
   * TRIM those spaces from both input and output, and then proceed as before.
   * Do NOT trim spaces if their number is different.
   *
   * @param text The multiline string to search in
   * @param substring The substring to search for
   * @return Right(offset) if the substring appears exactly once, Left(error) otherwise
   */
  def findUniqueSubstringOffset(text: String, substring: String): Either[SubstringSearchError, Int] = {
    if (substring.isEmpty) return Left(SubstringEmpty)

    // Check if we can apply the leading space relaxation
    val textLeadingSpaces = countLeadingSpaces(text)
    val substringLeadingSpaces = countLeadingSpaces(substring)

    val (searchText, searchSubstring, offsetAdjustment) =
      if (textLeadingSpaces > 0 && textLeadingSpaces == substringLeadingSpaces) {
        // Apply relaxation: trim the same number of leading spaces from both
        val trimmedText = text.substring(textLeadingSpaces)
        val trimmedSubstring = substring.substring(substringLeadingSpaces)
        (trimmedText, trimmedSubstring, textLeadingSpaces)
      } else {
        // No relaxation: use original strings
        (text, substring, 0)
      }

    // First try direct matching (fast path for most cases)
    val directFirstIndex = searchText.indexOf(searchSubstring)
    if (directFirstIndex != -1) {
      val directSecondIndex = searchText.indexOf(searchSubstring, directFirstIndex + 1)
      if (directSecondIndex == -1) {
        // Direct match found and is unique
        return Right(directFirstIndex + offsetAdjustment)
      } else {
        // Direct match found but not unique
        return Left(SubstringNotUnique)
      }
    }

    // If direct matching failed or found multiple matches, try Unicode normalization
    import java.text.Normalizer
    val normalizedText = Normalizer.normalize(searchText, Normalizer.Form.NFC)
    val normalizedSubstring = Normalizer.normalize(searchSubstring, Normalizer.Form.NFC)

    val firstIndex = normalizedText.indexOf(normalizedSubstring)
    if (firstIndex == -1) {
      Output.writeln(s"I/Q Server: Substring not found in text")
      Output.writeln(s"I/Q Server: Original text length: ${text.length}")
      Output.writeln(s"I/Q Server: Original substring length: ${substring.length}")
      Output.writeln(s"I/Q Server: Search text length: ${searchText.length}")
      Output.writeln(s"I/Q Server: Search substring length: ${searchSubstring.length}")
      if (offsetAdjustment > 0) {
        Output.writeln(s"I/Q Server: Applied leading space relaxation: trimmed $offsetAdjustment spaces")
      }
      return Left(SubstringNotFound)
    }

    val secondIndex = normalizedText.indexOf(normalizedSubstring, firstIndex + 1)
    if (secondIndex != -1) {
      Output.writeln(s"I/Q Server: Substring found multiple times at normalized positions $firstIndex and $secondIndex")
      return Left(SubstringNotUnique)
    }

    // Convert the normalized offset back to search text offset, then add space adjustment
    val searchTextOffset = mapNormalizedOffsetToOriginal(searchText, normalizedText, firstIndex)
    Right(searchTextOffset + offsetAdjustment)
  }

  /**
   * Maps an offset in a normalized string back to the corresponding offset in the original string.
   * This handles cases where Unicode normalization changes character positions.
   */
  private def mapNormalizedOffsetToOriginal(originalText: String, normalizedText: String, normalizedOffset: Int): Int = {
    import java.text.Normalizer

    // If no normalization occurred, offsets are the same
    if (originalText == normalizedText) return normalizedOffset

    // Build a mapping by processing character by character
    var originalPos = 0
    var normalizedPos = 0

    while (normalizedPos < normalizedOffset && originalPos < originalText.length) {
      // Get the next character from original text
      val originalChar = originalText.charAt(originalPos)

      // Normalize just this character to see how many normalized characters it produces
      val normalizedChar = Normalizer.normalize(originalChar.toString, Normalizer.Form.NFC)

      // Advance positions
      originalPos += 1
      normalizedPos += normalizedChar.length

      // If we've gone past the target offset, we need to back up
      if (normalizedPos > normalizedOffset) {
        // The target offset falls within this character's normalization
        // Return the position of the start of this character in the original text
        return originalPos - 1
      }
    }

    originalPos
  }

  /**
   * Gets the full text content of a file from the buffer.
   *
   * @param filePath The path to the theory file
   * @return Try[String] containing the file content, or failure if file not found/opened
   */
  def getFileContent(filePath: String): Try[String] = {
    Try {
      // Convert file path to node name
      val node_name = PIDE.resources.node_name(filePath)

      // Try to get buffer model first (for open files)
      Document_Model.get_model(node_name) match {
        case Some(buffer_model: Buffer_Model) =>
          JEdit_Lib.buffer_text(buffer_model.buffer)
        case _ =>
          throw new RuntimeException(s"File $filePath is not opened in jEdit")
      }
    }
  }

  /**
   * Finds a command by unique substring pattern matching in a file.
   * Uses unique substring search in the full file text, then finds the command
   * at the last character of the match.
   *
   * @param filePath The path to the theory file
   * @param pattern The substring pattern to match (will be trimmed)
   * @return Try[Command] containing the unique matching command, or failure if not found/unique
   */
  def findCommandByPattern(filePath: String, pattern: String): Try[Command] = {
    Try {
      // Trim whitespace and newlines from the pattern
      val trimmedPattern = pattern.trim

      if (trimmedPattern.isEmpty) {
        throw new RuntimeException("Pattern cannot be empty after trimming")
      }

      // Get the full file content
      val fileContent = getFileContent(filePath) match {
        case Success(content) => content
        case Failure(ex) => throw ex
      }

      // Find unique substring offset
      val matchOffset = findUniqueSubstringOffset(fileContent, trimmedPattern) match {
        case Right(offset) => offset
        case Left(SubstringNotFound) => throw new RuntimeException(s"Pattern '$trimmedPattern' not found in $filePath")
        case Left(SubstringNotUnique) => throw new RuntimeException(s"Pattern '$trimmedPattern' is not unique in $filePath")
        case Left(SubstringEmpty) => throw new RuntimeException(s"Pattern cannot be empty")
      }

      // Calculate the offset of the last character of the match
      val lastCharOffset = matchOffset + trimmedPattern.length - 1

      // Find the command at that offset
      findCommandAtFileOffset(filePath, lastCharOffset) match {
        case Success(command) => command
        case Failure(ex) => throw new RuntimeException(s"No command found at calculated offset $lastCharOffset: ${ex.getMessage}")
      }
    }
  }

  /**
   * Gets the current command at the cursor position in the active view.
   *
   * @param view The jEdit view (can be null, will use active view)
   * @return Try[Command] containing the current command, or failure if none found
   */
  def getCurrentCommand(view: View = null): Try[Command] = {
    Try {
      // All GUI and document model operations in GUI thread
      GUI_Thread.now {
        val activeView = if (view != null) view else jEdit.getActiveView()
        if (activeView == null) {
          throw new RuntimeException("No active view available")
        }

        val buffer = activeView.getBuffer()
        if (buffer == null) {
          throw new RuntimeException("No buffer in active view")
        }

        // Get the document model
        val model = Document_Model.get_model(buffer) match {
          case Some(m) => m
          case None => throw new RuntimeException("No document model for current buffer")
        }

        val textArea = activeView.getTextArea()
        val caretPos = textArea.getCaretPosition()

        // Find command at caret position - all in GUI thread
        val snapshot = Document_Model.snapshot(model)
        val node = snapshot.get_node(model.node_name)

        if (node != null && node.commands.nonEmpty) {
          val targetRange = Text.Range(caretPos, caretPos + 1)
          val commandsAtCaret = node.command_iterator(targetRange).toList

          commandsAtCaret.headOption match {
            case Some((command, _)) => command
            case None => throw new RuntimeException("No command found at current cursor position")
          }
        } else {
          throw new RuntimeException("No commands available in current document")
        }
      }
    }
  }

  /**
   * Formats query arguments based on the query type.
   *
   * @param queryType The type of query (isar_explore, sledgehammer, find_theorems)
   * @param args The argument string
   * @return List of formatted arguments for the query
   */
  def formatQueryArguments(queryType: String, args: String): List[String] = {
    queryType match {
      case "sledgehammer" =>
        // Sledgehammer expects 3 arguments: provers, isar_proofs, try0
        List(args, "false", "true")
      case "find_theorems" =>
        // find_theorems expects 3 arguments: limit, allow_dups, query
        List("20", "false", args)
      case "isar_explore" =>
        // isar_explore expects a single argument (the method)
        List(args)
      case _ =>
        // Other queries expect a single argument
        List(args)
    }
  }

  /**
   * Gets default arguments for a query type.
   *
   * @param queryType The type of query
   * @return Default arguments string, or empty string if no defaults
   */
  def getDefaultArguments(queryType: String): String = {
    queryType match {
      case "sledgehammer" =>
        try {
          PIDE.options.value.check_name("sledgehammer_provers").default_value
        } catch {
          case _: Exception => "z3 cvc4 e spass" // Fallback default
        }
      case "isar_explore" => "by simp"
      case "find_theorems" => "\"_ :: nat\" = \"_ :: nat\""
      case _ => ""
    }
  }

  /**
   * Validates target parameters for exploration.
   *
   * @param target The target type (current, file_offset, file_pattern)
   * @param filePath Optional file path
   * @param offset Optional offset
   * @param pattern Optional pattern
   * @return Try[Unit] indicating success or failure with error message
   */
  def validateTarget(
    target: String,
    filePath: Option[String],
    offset: Option[Int],
    pattern: Option[String]
  ): Try[Unit] = {
    Try {
      target match {
        case "current" =>
          // No additional parameters needed
          ()
        case "file_offset" =>
          if (filePath.isEmpty) {
            throw new IllegalArgumentException("file_offset target requires file_path parameter")
          }
          if (offset.isEmpty) {
            throw new IllegalArgumentException("file_offset target requires offset parameter")
          }
          ()
        case "file_pattern" =>
          if (filePath.isEmpty) {
            throw new IllegalArgumentException("file_pattern target requires file_path parameter")
          }
          if (pattern.isEmpty || pattern.get.trim.isEmpty) {
            throw new IllegalArgumentException("file_pattern target requires non-empty pattern parameter")
          }
          ()
        case _ =>
          throw new IllegalArgumentException(s"Invalid target: $target. Must be 'current', 'file_offset', or 'file_pattern'")
      }
    }
  }

  /**
   * Validates a query type.
   *
   * @param queryType The query type to validate
   * @return True if valid, false otherwise
   */
  def validateQuery(queryType: String): Boolean = {
    List("isar_explore", "sledgehammer", "find_theorems").contains(queryType)
  }

  /**
   * Converts a query type from external format to internal format.
   *
   * @param externalQuery The external query type (proof, sledgehammer, find_theorems)
   * @return The internal query type
   */
  def externalToInternalQuery(externalQuery: String): String = {
    externalQuery match {
      case "proof" => "isar_explore"
      case "sledgehammer" => "sledgehammer"
      case "find_theorems" => "find_theorems"
      case _ => externalQuery
    }
  }

  /**
   * Replace text in a buffer using atomic operations.
   * This is a utility function that can be used by both the server and dockable.
   *
   * @param model The buffer model to modify
   * @param textToInsert The text to insert
   * @param startOffset The start offset for replacement
   * @param endOffset The end offset for replacement
   */
  def replaceTextInBuffer(model: Buffer_Model, textToInsert: String, startOffset: Int, endOffset: Int): Unit = {
    val buffer = model.buffer
    // Perform the buffer modification using jEdit's atomic operations
    buffer.writeLock()
    try {
      // Use jEdit's compound edit for atomic operation
      buffer.beginCompoundEdit()

      try {
        // Remove the target range (always remove first, even if we're adding content)
        buffer.remove(startOffset, endOffset - startOffset)
        buffer.insert(startOffset, textToInsert)
        // Mark buffer as modified but don't save automatically
        buffer.setDirty(true)

        val bytesRemoved = endOffset - startOffset
        val bytesAdded = textToInsert.length
        val netChange = bytesAdded - bytesRemoved

        val node_name = model.node_name
        Output.writeln(s"IQUtils: Successfully performed edit on node $node_name")
        Output.writeln(s"IQUtils:   Removed: $bytesRemoved chars, Added: $bytesAdded chars, Net: ${if (netChange >= 0) "+" else ""}$netChange chars")
      } finally {
        buffer.endCompoundEdit()
      }

    } finally {
      buffer.writeUnlock()
    }
  }

  /**
   * Block until a document model has a stable snapshot (no pending edits).
   * This is a utility function that can be used by both the server and dockable.
   *
   * @param model The document model to wait for
   * @return A tuple containing (stable snapshot, whether the original snapshot was outdated)
   */
  def blockOnStableSnapshot(model: Document_Model): (Document.Snapshot, Boolean) = {
    val initial_snapshot = GUI_Thread.now { Document_Model.snapshot(model) }
    val was_outdated = initial_snapshot.is_outdated

    if (!was_outdated) {
      (initial_snapshot, false)
    } else {
      var current_snapshot = initial_snapshot
      while (current_snapshot.is_outdated) {
        // Sleep briefly to avoid tight loop
        Thread.sleep(50)
        current_snapshot = GUI_Thread.now { Document_Model.snapshot(model) }
      }
      (current_snapshot, true)
    }
  }
}
