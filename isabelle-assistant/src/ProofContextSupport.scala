/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

import java.util.concurrent.{CountDownLatch, TimeUnit}

/** Shared context collection for proof-facing actions.
  *
  * Combines:
  * - local proof facts (`print_context`)
  * - potentially relevant global facts from loaded theories (via
  *   `find_theorems` over goal-derived symbols, i.e. MePo-ranked results)
  * - optional definition context from PIDE entities.
  */
object ProofContextSupport {

  case class ContextBundle(
      localFacts: String = "",
      relevantTheorems: String = "",
      definitions: String = ""
  ) {
    def localFactsOpt: Option[String] =
      Option(localFacts).map(_.trim).filter(_.nonEmpty)
    def relevantTheoremsOpt: Option[String] =
      Option(relevantTheorems).map(_.trim).filter(_.nonEmpty)
    def definitionsOpt: Option[String] =
      Option(definitions).map(_.trim).filter(_.nonEmpty)
  }

  def collect(
      view: View,
      offset: Int,
      goalStateOpt: Option[String],
      includeDefinitions: Boolean = false
  ): ContextBundle = {
    // Dispatch the two I/Q-backed lookups concurrently so their timeouts
    // overlap instead of stacking serially (cuts worst-case wall time in
    // half on timeouts).
    val latch = new CountDownLatch(2)
    @volatile var localFacts = ""
    @volatile var relevantTheorems = ""

    dispatchLocalFacts(view, result => {
      localFacts = result
      latch.countDown()
    })
    dispatchRelevantTheorems(view, offset, goalStateOpt, result => {
      relevantTheorems = result
      latch.countDown()
    })

    val combinedTimeout = math.max(
      AssistantConstants.CONTEXT_FETCH_TIMEOUT,
      AssistantOptions.getFindTheoremsTimeout
    ) + AssistantConstants.TIMEOUT_BUFFER_MS
    val _ = latch.await(combinedTimeout, TimeUnit.MILLISECONDS)

    val definitions =
      if (includeDefinitions)
        ContextFetcher
          .getContext(view, AssistantConstants.CONTEXT_FETCH_TIMEOUT)
          .getOrElse("")
      else ""

    ContextBundle(
      localFacts = localFacts,
      relevantTheorems = relevantTheorems,
      definitions = definitions
    )
  }

  private def dispatchLocalFacts(view: View, onDone: String => Unit): Unit = {
    if (!IQAvailable.isAvailable) {
      onDone("")
    } else {
      GUI_Thread.later {
        PrintContextAction.runPrintContextAsync(
          view,
          AssistantConstants.CONTEXT_FETCH_TIMEOUT,
          { result =>
            val text = result match {
              case Right(output)
                  if output.trim.nonEmpty && !output.contains("No local facts") =>
                output.trim
              case _ => ""
            }
            onDone(text)
          }
        )
      }
    }
  }

  private def dispatchRelevantTheorems(
      view: View,
      offset: Int,
      goalStateOpt: Option[String],
      onDone: String => Unit
  ): Unit =
    goalStateOpt.filter(_.trim.nonEmpty) match {
      case Some(goalState) if IQAvailable.isAvailable =>
        val analysisOpt = GoalExtractor.analyzeGoal(view.getBuffer, offset)
        val symbols = extractNamesForFindTheorems(goalState, analysisOpt)
        if (symbols.isEmpty) onDone("")
        else {
          val pattern = symbols.map(s => s"""name: "$s"""").mkString(" ")
          val limit = AssistantOptions.getFindTheoremsLimit
          val timeout = AssistantOptions.getFindTheoremsTimeout

          GUI_Thread.later {
            IQIntegration.runFindTheoremsAsync(
              view,
              pattern,
              limit,
              timeout,
              {
                case Right(found) =>
                  onDone(found.take(limit).mkString("\n"))
                case Left(err) =>
                  Output.writeln(
                    s"[Assistant] find_theorems context lookup failed: $err"
                  )
                  onDone("")
              }
            )
          }
        }
      case _ => onDone("")
    }

  private[assistant] def extractNamesForFindTheorems(
      goalState: String,
      analysisOpt: Option[GoalExtractor.GoalAnalysis]
  ): List[String] = {
    val fromMarkup = analysisOpt
      .map(_.constants.filter(_.nonEmpty))
      .getOrElse(Nil)
      .take(AssistantConstants.MAX_CONSTANTS_FOR_FIND_THEOREMS)

    if (fromMarkup.nonEmpty) fromMarkup.distinct
    else extractNamesFromGoalText(goalState)
  }

  private def extractNamesFromGoalText(goalState: String): List[String] = {
    val skipWords = Set(
      "goal",
      "subgoal",
      "subgoals",
      "proof",
      "have",
      "show",
      "using",
      "by",
      "True",
      "False",
      "undefined",
      "THE",
      "SOME",
      "ALL",
      "EX",
      "if",
      "then",
      "else",
      "let",
      "in",
      "case",
      "of",
      "where",
      "and",
      "or",
      "not",
      "for",
      "assumes",
      "shows",
      "fixes",
      "obtains"
    )
    val identPattern = """[A-Za-z][A-Za-z0-9_'.]*""".r

    goalState.linesIterator
      .flatMap(line => identPattern.findAllIn(line.trim))
      .filter(w => w.length > 2 && !skipWords.contains(w))
      .filter(w =>
        w.contains("_") || w.head.isLower || w.head.isUpper && w
          .drop(1)
          .exists(_.isLower)
      )
      .toList
      .distinct
      .take(AssistantConstants.MAX_CONSTANTS_FOR_FIND_THEOREMS)
  }
}
