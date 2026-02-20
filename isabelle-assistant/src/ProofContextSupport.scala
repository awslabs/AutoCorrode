/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
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
      commandOpt: Option[Command],
      goalStateOpt: Option[String],
      includeDefinitions: Boolean = false
  ): ContextBundle = {
    val localFacts = fetchLocalFacts(view, commandOpt)
    val relevantTheorems =
      fetchRelevantTheorems(view, offset, commandOpt, goalStateOpt)
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

  private def fetchLocalFacts(view: View, commandOpt: Option[Command]): String =
    commandOpt match {
      case None if !IQAvailable.isAvailable => ""
      case None                             => ""
      case Some(command) =>
        val latch = new CountDownLatch(1)
        @volatile var contextResult = ""

        GUI_Thread.later {
          PrintContextAction.runPrintContextAsync(
            view,
            command,
            AssistantConstants.CONTEXT_FETCH_TIMEOUT,
            { result =>
              result match {
                case Right(output)
                    if output.trim.nonEmpty && !output
                      .contains("No local facts") =>
                  contextResult = output.trim
                case _ =>
              }
              latch.countDown()
            }
          )
        }

        latch.await(
          AssistantConstants.CONTEXT_FETCH_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS,
          TimeUnit.MILLISECONDS
        )
        contextResult
    }

  private def fetchRelevantTheorems(
      view: View,
      offset: Int,
      commandOpt: Option[Command],
      goalStateOpt: Option[String]
  ): String =
    (commandOpt, goalStateOpt.filter(_.trim.nonEmpty)) match {
      case (Some(command), Some(goalState)) if IQAvailable.isAvailable =>
        val analysisOpt = GoalExtractor.analyzeGoal(view.getBuffer, offset)
        val symbols = extractNamesForFindTheorems(goalState, analysisOpt)
        if (symbols.isEmpty) ""
        else {
          val pattern = symbols.map(s => s"""name: "$s"""").mkString(" ")
          val limit = AssistantOptions.getFindTheoremsLimit
          val timeout = AssistantOptions.getFindTheoremsTimeout
          val latch = new CountDownLatch(1)
          @volatile var results: List[String] = Nil

          GUI_Thread.later {
            IQIntegration.runFindTheoremsAsync(
              view,
              command,
              pattern,
              limit,
              timeout,
              {
                case Right(found) =>
                  results = found.take(limit)
                  latch.countDown()
                case Left(err) =>
                  Output.writeln(
                    s"[Assistant] find_theorems context lookup failed: $err"
                  )
                  latch.countDown()
              }
            )
          }

          latch.await(timeout + AssistantConstants.TIMEOUT_BUFFER_MS, TimeUnit.MILLISECONDS)
          results.mkString("\n")
        }
      case _ => ""
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

