/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.buffer.JEditBuffer

/** Extracts goal state and proof context status via typed I/Q MCP adapters.
  * Provides flat goal text extraction and structured analysis for prompts and
  * action heuristics.
  */
object GoalExtractor {

  /** Structured analysis of a proof goal, extracted from PIDE XML markup.
    * Provides typed access to variables, constants, and subgoal count without
    * regex parsing of rendered text.
    *
    * @param text
    *   The flat-text rendering of the goal state
    * @param freeVars
    *   Free (unbound) variables in the goal — candidates for induction
    * @param constants
    *   Constants referenced in the goal
    * @param numSubgoals
    *   Number of subgoals (parsed from PIDE output structure)
    */
  case class GoalAnalysis(
      text: String,
      freeVars: List[String],
      constants: List[String],
      numSubgoals: Int
  )

  private[assistant] val proofOpeners: Set[String] =
    IsabelleKeywords.proofOpeners ++
      IsabelleKeywords.definitionForms ++ IsabelleKeywords.inductiveKeywords

  private[assistant] val proofClosers: Set[String] = Set(
    "qed",
    "done",
    "end",
    "sorry",
    "oops",
    "\\<close>"
  )

  private val GoalLookupTimeoutMs =
    AssistantConstants.CONTEXT_FETCH_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS

  private def selectionArgs(buffer: JEditBuffer, offset: Int): Map[String, Any] = {
    val clamped = math.max(0, math.min(offset, buffer.getLength))
    MenuContext.bufferPath(buffer) match {
      case Some(path) =>
        Map(
          "command_selection" -> "file_offset",
          "path" -> path,
          "offset" -> clamped
        )
      case None =>
        Map("command_selection" -> "current")
    }
  }

  /** Get the goal state text at the given buffer offset. Returns None if no
   * goal is available (e.g., outside a proof context).
   */
  def getGoalState(buffer: JEditBuffer, offset: Int): Option[String] =
    IQMcpClient
      .callGetContextInfo(selectionArgs(buffer, offset), GoalLookupTimeoutMs)
      .toOption
      .map(_.goal)
      .filter(goal => goal.hasGoal && goal.goalText.trim.nonEmpty)
      .map(_.goalText)

  /** Get structured goal analysis at the given buffer offset. Extracts free
   * variables and constants from typed I/Q goal analysis.
   *
   * @param buffer
   *   The jEdit buffer
    * @param offset
    *   Character offset in the buffer
   * @return
   *   Structured goal analysis, or None if no goal at offset
   */
  def analyzeGoal(buffer: JEditBuffer, offset: Int): Option[GoalAnalysis] =
    IQMcpClient
      .callGetContextInfo(selectionArgs(buffer, offset), GoalLookupTimeoutMs)
      .toOption
      .map(_.goal)
      .filter(goal => goal.hasGoal && goal.goalText.trim.nonEmpty)
      .map(goal =>
        GoalAnalysis(
          text = goal.goalText,
          freeVars = goal.freeVars,
          constants = goal.constants.filterNot(isMetaConstant),
          numSubgoals = math.max(goal.numSubgoals, 1)
        )
      )

  private[assistant] def analyzeGoalFromMessages(
      messages: List[XML.Tree],
      fallbackFreeVars: List[String] = Nil
  ): Option[GoalAnalysis] = {
    if (messages.isEmpty) None
    else {
      val text = messages
        .map(elem => XML.content(elem).trim)
        .filter(_.nonEmpty)
        .mkString("\n\n")
      if (text.isEmpty) None
      else {
        val freeVars = scala.collection.mutable.LinkedHashSet[String]()
        val constants = scala.collection.mutable.LinkedHashSet[String]()
        var numSubgoals = 0

        def walk(tree: XML.Tree): Unit = tree match {
          case XML.Elem(Markup(Markup.FREE, props), body) =>
            Markup.Name.unapply(props).foreach(freeVars.add)
            body.foreach(walk)
          case XML.Elem(Markup("fixed", props), body) =>
            Markup.Name.unapply(props).foreach(freeVars.add)
            body.foreach(walk)
          case XML.Elem(Markup(Markup.CONSTANT, props), body) =>
            Markup.Name.unapply(props).foreach { name =>
              if (!isMetaConstant(name)) {
                val _ = constants.add(name)
              }
            }
            body.foreach(walk)
          case XML.Elem(Markup("subgoal", _), body) =>
            numSubgoals += 1
            body.foreach(walk)
          case XML.Elem(_, body) => body.foreach(walk)
          case XML.Text(_)       =>
        }

        messages.foreach(walk)
        val resolvedFreeVars =
          if (freeVars.nonEmpty) freeVars.toList else fallbackFreeVars

        Some(
          GoalAnalysis(
            text = text,
            freeVars = resolvedFreeVars,
            constants = constants.toList,
            numSubgoals = math.max(numSubgoals, 1)
          )
        )
      }
    }
  }

  /** Filter out meta-level constants that aren't useful for proof strategy. */
  private def isMetaConstant(name: String): Boolean =
    name.startsWith("Pure.") || name == "Trueprop" || name == "HOL.eq" ||
      name == "HOL.implies" || name == "HOL.conj" || name == "HOL.disj" ||
      name == "HOL.All" || name == "HOL.Ex" || name == "HOL.Not" ||
      name == "HOL.True" || name == "HOL.False"

  /** Check whether the given offset is inside a proof context by walking
   * commands backwards from the offset, tracking proof opener/closer depth.
   * Returns true if an unmatched proof opener is found before any closer.
   */
  def isInProofContext(buffer: JEditBuffer, offset: Int): Boolean =
    IQMcpClient
      .callGetContextInfo(selectionArgs(buffer, offset), GoalLookupTimeoutMs)
      .toOption
      .exists(_.inProofContext)

  private[assistant] def isInProofContextFromKeywords(
      keywords: Seq[String]
  ): Boolean = {
    import scala.util.boundary, boundary.break
    boundary {
      var depth = 0
      for (kw <- keywords.reverseIterator) {
        if (proofClosers.contains(kw)) depth += 1
        else if (proofOpeners.contains(kw)) {
          if (depth > 0) depth -= 1
          else break(true)
        }
      }
      false
    }
  }
}
