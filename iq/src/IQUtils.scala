/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

import org.gjt.sp.jedit.{View, jEdit}
import java.io.File
import scala.util.{Failure, Success, Try}

/**
 * Utilities for I/Q Explore functionality.
 * Contains pure functions that can be shared between GUI and MCP implementations.
 */
object IQUtils {

  sealed trait CommandSelection
  case object CurrentSelection extends CommandSelection
  final case class FileOffsetSelection(
      path: String,
      requestedOffset: Int,
      normalizedOffset: Int
  ) extends CommandSelection
  final case class FilePatternSelection(path: String, pattern: String)
      extends CommandSelection

  final case class TargetResolution(
      selection: CommandSelection,
      command: Command
  )

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
   * @return Either error message or the matching command
   */
  def findCommandAtFileOffset(
      filePath: String,
      offset: Int
  ): Either[String, Command] = {
    val nodeName = PIDE.resources.node_name(filePath)
    val snapshot = PIDE.session.snapshot()
    val node = snapshot.get_node(nodeName)

    if (node == null || node.commands.isEmpty) {
      Left(s"Node not found or empty for $filePath")
    } else {
      val targetRange = Text.Range(offset, offset + 1)
      val commandsAtOffset = node.command_iterator(targetRange).toList
      commandsAtOffset.headOption match {
        case Some((command, _)) => Right(command)
        case None => Left(s"No command found at offset $offset in $filePath")
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
   * @return Either error message or the file content
   */
  def getFileContent(filePath: String): Either[String, String] = {
    val nodeName = PIDE.resources.node_name(filePath)
    Document_Model.get_model(nodeName) match {
      case Some(bufferModel: Buffer_Model) =>
        Right(JEdit_Lib.buffer_text(bufferModel.buffer))
      case _ =>
        Left(s"File $filePath is not opened in jEdit")
    }
  }

  /**
   * Finds a command by unique substring pattern matching in a file.
   * Uses unique substring search in the full file text, then finds the command
   * at the last character of the match.
   *
   * @param filePath The path to the theory file
   * @param pattern The substring pattern to match (will be trimmed)
   * @return Either error message or the unique matching command
   */
  def findCommandByPattern(
      filePath: String,
      pattern: String
  ): Either[String, Command] = {
    val trimmedPattern = pattern.trim
    if (trimmedPattern.isEmpty) {
      Left("Pattern cannot be empty after trimming")
    } else {
      getFileContent(filePath).flatMap { fileContent =>
        val matchOffset = findUniqueSubstringOffset(fileContent, trimmedPattern) match {
          case Right(offset) => Right(offset)
          case Left(SubstringNotFound) =>
            Left(s"Pattern '$trimmedPattern' not found in $filePath")
          case Left(SubstringNotUnique) =>
            Left(s"Pattern '$trimmedPattern' is not unique in $filePath")
          case Left(SubstringEmpty) =>
            Left("Pattern cannot be empty")
        }

        matchOffset.flatMap { offset =>
          val lastCharOffset = offset + trimmedPattern.length - 1
          findCommandAtFileOffset(filePath, lastCharOffset).left.map { err =>
            s"No command found at calculated offset $lastCharOffset: $err"
          }
        }
      }
    }
  }

  /**
   * Gets the current command at the cursor position in the active view.
   *
   * @param viewOpt The jEdit view (if empty, uses active view)
   * @return Either error message or current command
   */
  def getCurrentCommand(viewOpt: Option[View] = None): Either[String, Command] = {
    GUI_Thread.now {
      val activeView = viewOpt.orElse(Option(jEdit.getActiveView()))
      activeView match {
        case None =>
          Left("No active view available")
        case Some(view) =>
          Option(view.getBuffer()) match {
            case None =>
              Left("No buffer in active view")
            case Some(buffer) =>
              Document_Model.get_model(buffer) match {
                case None =>
                  Left("No document model for current buffer")
                case Some(model) =>
                  val caretPos = view.getTextArea().getCaretPosition()
                  val snapshot = Document_Model.snapshot(model)
                  val node = snapshot.get_node(model.node_name)
                  if (node == null || node.commands.isEmpty) {
                    Left("No commands available in current document")
                  } else {
                    val targetRange = Text.Range(caretPos, caretPos + 1)
                    val commandsAtCaret = node.command_iterator(targetRange).toList
                    commandsAtCaret.headOption match {
                      case Some((command, _)) => Right(command)
                      case None =>
                        Left("No command found at current cursor position")
                    }
                  }
              }
          }
      }
    }
  }

  /**
   * Clamp a requested offset to the valid range for a file content length.
   *
   * For empty files, returns 0.
   */
  def normalizeRequestedOffset(requestedOffset: Int, contentLength: Int): Int = {
    if (contentLength <= 0) 0
    else math.max(0, math.min(requestedOffset, contentLength - 1))
  }

  /**
   * Resolve a command selection into an actual Isabelle command.
   *
   * This is the canonical selection semantics for MCP tools that operate on
   * command context.
   */
  def resolveCommandSelection(
      target: CommandSelectionTarget,
      filePath: Option[String],
      offset: Option[Int],
      pattern: Option[String],
      viewOpt: Option[View] = None
  ): Either[String, TargetResolution] = {
    target match {
      case CommandSelectionTarget.Current =>
        getCurrentCommand(viewOpt).map(cmd =>
          TargetResolution(CurrentSelection, cmd)
        )
      case CommandSelectionTarget.FileOffset =>
        (filePath, offset) match {
          case (Some(path), Some(requested)) =>
            getFileContent(path).flatMap { content =>
              val normalized = normalizeRequestedOffset(requested, content.length)
              findCommandAtFileOffset(path, normalized).map(cmd =>
                TargetResolution(
                  FileOffsetSelection(path, requested, normalized),
                  cmd
                )
              )
            }
          case (None, _) =>
            Left("file_offset target requires file_path parameter")
          case (_, None) =>
            Left("file_offset target requires offset parameter")
        }
      case CommandSelectionTarget.FilePattern =>
        (filePath, pattern.map(_.trim).filter(_.nonEmpty)) match {
          case (Some(path), Some(trimmedPattern)) =>
            findCommandByPattern(path, trimmedPattern).map(cmd =>
              TargetResolution(
                FilePatternSelection(path, trimmedPattern),
                cmd
              )
            )
          case (None, _) =>
            Left("file_pattern target requires file_path parameter")
          case (_, None) =>
            Left("file_pattern target requires non-empty pattern parameter")
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
   * Backwards-compatible target validation helper used by tests.
   */
  def validateTarget(
      target: String,
      filePath: Option[String],
      offset: Option[Int],
      pattern: Option[String]
  ): Try[Unit] = {
    CommandSelectionTarget.fromWire(target) match {
      case Left(raw) =>
        Failure(
          new IllegalArgumentException(
            s"Invalid target: $raw. Must be 'current', 'file_offset', or 'file_pattern'"
          )
        )
      case Right(CommandSelectionTarget.Current) =>
        Success(())
      case Right(CommandSelectionTarget.FileOffset) =>
        (filePath, offset) match {
          case (Some(_), Some(_)) => Success(())
          case (None, _) =>
            Failure(
              new IllegalArgumentException(
                "file_offset target requires file_path parameter"
              )
            )
          case (_, None) =>
            Failure(
              new IllegalArgumentException(
                "file_offset target requires offset parameter"
              )
            )
        }
      case Right(CommandSelectionTarget.FilePattern) =>
        (filePath, pattern.map(_.trim).filter(_.nonEmpty)) match {
          case (Some(_), Some(_)) => Success(())
          case (None, _) =>
            Failure(
              new IllegalArgumentException(
                "file_pattern target requires file_path parameter"
              )
            )
          case (_, None) =>
            Failure(
              new IllegalArgumentException(
                "file_pattern target requires non-empty pattern parameter"
              )
            )
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
    Set("isar_explore", "sledgehammer", "find_theorems").contains(queryType)
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
