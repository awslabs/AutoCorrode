/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer
import java.util.concurrent.{CountDownLatch, TimeUnit}
import javax.swing.SwingUtilities

/** Fetches definitions of constants/types referenced in code.
  * Uses I/Q typed MCP capabilities for goal-aware definition lookup.
  *
  * IMPORTANT: getContext must NOT be called from the GUI thread — it blocks waiting
  * for background work. All callers run on Isabelle_Thread or background threads.
  */
object ContextFetcher {

  /** Get context for code at cursor by extracting referenced constants from
    * goal analysis and looking up their definitions.
    */
  def getContext(view: View, timeoutMs: Long = 3000): Option[String] = {
    if (SwingUtilities.isEventDispatchThread) {
      Output.warning(
        "[Assistant] ContextFetcher.getContext called from GUI thread — returning None to avoid deadlock"
      )
      return None
    }

    if (!IQAvailable.isAvailable) return None

    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val names =
      GoalExtractor
        .analyzeGoal(buffer, offset)
        .map(_.constants.filterNot(isMetaLevel).distinct)
        .getOrElse(Nil)

    if (names.isEmpty) None
    else fetchDefinitionsForNames(view, names, timeoutMs)
  }

  /** Extract entity-like names near cursor via goal/context introspection. */
  def extractEntities(buffer: JEditBuffer, offset: Int): List[(String, String)] = {
    GoalExtractor
      .analyzeGoal(buffer, offset)
      .map { analysis =>
        val constants =
          analysis.constants
            .filterNot(isMetaLevel)
            .distinct
            .map(Markup.CONSTANT -> _)
        val free = analysis.freeVars.distinct.map(Markup.FREE -> _)
        (constants ++ free).distinct
      }
      .getOrElse(Nil)
  }

  /** Fetch definitions for a specific list of names via I/Q get_definitions.
    * Must NOT be called from the GUI thread.
    */
  def fetchDefinitionsForNames(
      view: View,
      names: List[String],
      timeoutMs: Long = 3000
  ): Option[String] = {
    if (SwingUtilities.isEventDispatchThread) {
      Output.warning(
        "[Assistant] fetchDefinitionsForNames called from GUI thread — returning None"
      )
      return None
    }
    if (names.isEmpty || !IQAvailable.isAvailable) return None

    val interesting = names.filterNot(isMetaLevel).distinct
    if (interesting.isEmpty) return None

    val resultLatch = new CountDownLatch(1)
    @volatile var result: Option[String] = None

    IQIntegration.getDefinitionsAsync(
      view,
      interesting,
      timeoutMs,
      response => {
        response match {
          case Right(defs)
              if defs.success &&
                defs.hasDefinitions &&
                defs.definitions.trim.nonEmpty &&
                !defs.definitions.contains("No additional context") &&
                !defs.definitions.startsWith("Error:") =>
            result = Some(defs.definitions.trim)
          case _ =>
        }
        resultLatch.countDown()
      }
    )

    val _ = resultLatch.await(timeoutMs + 1000, TimeUnit.MILLISECONDS)
    result
  }

  private def isMetaLevel(name: String): Boolean = {
    name.startsWith("Pure.") || name == "Trueprop" ||
    name == "Pure.imp" || name == "Pure.eq" || name == "Pure.all" ||
    name == "fun" || name == "itself"
  }
}
