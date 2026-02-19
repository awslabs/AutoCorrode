/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.buffer.JEditBuffer

/** Extracts goal state and proof context status from PIDE editor output. Uses
  * PIDE.editor.output (same as the Output_Dockable) to retrieve the current
  * goal state at a given buffer offset.
  *
  * Provides both flat-text extraction (for LLM prompts) and structured analysis
  * (for programmatic use by the auto-prover).
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

  /** Get the goal state text at the given buffer offset. Returns None if no
    * goal is available (e.g., outside a proof context).
    */
  def getGoalState(buffer: JEditBuffer, offset: Int): Option[String] = {
    Document_Model.get_model(buffer).flatMap { model =>
      val snapshot = Document_Model.snapshot(model)
      val output = PIDE.editor.output(snapshot, offset)

      if (output.messages.nonEmpty) {
        val text =
          output.messages.map(elem => XML.content(elem).trim).filter(_.nonEmpty)
        val joined = text.mkString("\n\n")
        if (joined.nonEmpty) Some(joined) else None
      } else None
    }
  }

  /** Get structured goal analysis at the given buffer offset. Extracts free
    * variables and constants from PIDE XML markup rather than relying on regex
    * over rendered text.
    *
    * @param buffer
    *   The jEdit buffer
    * @param offset
    *   Character offset in the buffer
    * @return
    *   Structured goal analysis, or None if no goal at offset
    */
  def analyzeGoal(buffer: JEditBuffer, offset: Int): Option[GoalAnalysis] = {
    Document_Model.get_model(buffer).flatMap { model =>
      val snapshot = Document_Model.snapshot(model)
      val output = PIDE.editor.output(snapshot, offset)
      analyzeGoalFromMessages(
        output.messages,
        extractFreeVarsFromCommand(snapshot, offset)
      )
    }
  }

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
              if (!isMetaConstant(name)) constants.add(name)
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

  /** Extract free variables from the command at offset using PIDE entity
    * markup.
    */
  private def extractFreeVarsFromCommand(
      snapshot: Document.Snapshot,
      offset: Int
  ): List[String] = {
    val freeVars = scala.collection.mutable.LinkedHashSet[String]()
    try {
      val node = snapshot.get_node(snapshot.node_name)
      node
        .command_iterator(Text.Range(offset, offset + 1))
        .toList
        .headOption
        .foreach { case (cmd, cmdOffset) =>
          val range = Text.Range(cmdOffset, cmdOffset + cmd.length)
          val results = snapshot.cumulate(
            range,
            List.empty[String],
            Markup.Elements(Markup.FREE, "fixed"),
            _ => { case (acc, Text.Info(_, XML.Elem(Markup(_, props), _))) =>
              Markup.Name.unapply(props).map(name => acc :+ name)
            }
          )
          results.flatMap(_._2).distinct.foreach(freeVars.add)
        }
    } catch {
      case ex: Exception => ErrorHandler.logSilentError("GoalExtractor", ex)
    }
    freeVars.toList
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
  def isInProofContext(buffer: JEditBuffer, offset: Int): Boolean = {
    Document_Model.get_model(buffer).exists { model =>
      val snapshot = Document_Model.snapshot(model)
      val node = snapshot.get_node(model.node_name)
      if (node.commands.isEmpty) false
      else {
        val commands = node.command_iterator(Text.Range(0, offset + 1)).toList
        isInProofContextFromKeywords(commands.map(_._1.span.name))
      }
    }
  }

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
