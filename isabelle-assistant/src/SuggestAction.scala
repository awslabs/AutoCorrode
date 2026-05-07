/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer
import java.util.concurrent.CountDownLatch
import scala.annotation.unused

/** Proof suggestion pipeline combining LLM suggestions with optional
  * Sledgehammer results. Candidates are collected in parallel, optionally
  * verified via I/Q, ranked by verification status and timing, then displayed
  * with insert links.
  */
object SuggestAction {
  private val suggestSchema = StructuredResponseSchema(
    "return_suggestions", "Return proof method suggestions",
    """{"type":"object","properties":{"suggestions":{"type":"array","items":{"type":"string"}}},"required":["suggestions"]}"""
  )

  sealed trait CandidateSource
  case object LLM extends CandidateSource
  case object Sledgehammer extends CandidateSource

  case class Candidate(
      proof: String,
      source: CandidateSource,
      badge: VerificationBadge.BadgeType = VerificationBadge.Unverified,
      timeMs: Option[Long] = None
  )

  def suggest(view: View, buffer: JEditBuffer, offset: Int): Unit = {
    // Emit command to chat
    val target = getCurrentTarget(view, buffer, offset)
    val commandStr = s":suggest ${TargetParser.formatTarget(target)}"
    ChatAction.addMessage(ChatAction.User, commandStr)
    AssistantDockable.showConversation(ChatAction.getHistory)

    suggestInternal(view, buffer, offset)
  }

  /** Called from ChatAction when the user message is already echoed. */
  def suggestFromChat(view: View, buffer: JEditBuffer, offset: Int): Unit =
    suggestInternal(view, buffer, offset)

  private def suggestInternal(
      view: View,
      buffer: JEditBuffer,
      offset: Int
  ): Unit = {
    // Fork immediately to avoid blocking EDT on I/Q MCP calls
    val _ = Isabelle_Thread.fork(name = "assistant-suggest") {
      val _ = ErrorHandler
        .withErrorHandling("suggest operation") {
          // Check goal state first - this is what matters for proof suggestions
          val goalState = GoalExtractor.getGoalState(buffer, offset)
          
          goalState match {
            case None =>
              GUI_Thread.later {
                GUI.warning_dialog(
                  view,
                  "Isabelle Assistant",
                  AssistantConstants.UIText.NO_GOAL_AT_CURSOR
                )
              }
            case Some(goal) =>
              // Command text is optional context - best effort
              val commandText = CommandExtractor.getCommandAtOffset(buffer, offset)
              val cmd = commandText.getOrElse("(cursor context)")
              val canVerify =
                IQAvailable.isAvailable && AssistantOptions.getVerifySuggestions
              val useSledgehammer =
                AssistantOptions.getUseSledgehammer && IQAvailable.isAvailable

              GUI_Thread.later {
                AssistantDockable.setStatus("Generating suggestions…")
              }

              val _ = ErrorHandler
                .withErrorHandling("suggestion generation") {
                  Output.writeln(
                    s"[Assistant] Starting suggestion collection..."
                  )
                  val candidates = collectCandidates(
                    view,
                    cmd,
                    goal,
                    useSledgehammer
                  )
                  Output.writeln(
                    s"[Assistant] Collected ${candidates.length} candidates"
                  )

                  val verified =
                    if (canVerify) {
                      Output.writeln(s"[Assistant] Starting verification...")
                      verifyCandidates(view, candidates)
                    } else candidates

                  Output.writeln(
                    s"[Assistant] After verification: ${verified.length} candidates"
                  )
                  val ranked = rankCandidates(verified)
                  Output.writeln(
                    s"[Assistant] Displaying ${ranked.length} ranked candidates"
                  )

                  GUI_Thread.later {
                    displayResults(view, ranked)
                    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                  }
                }
                .recover { case ex =>
                  GUI_Thread.later {
                    AssistantDockable.setStatus("Error: " + ex.getMessage)
                    GUI.error_dialog(view, "Suggest Error", ex.getMessage)
                  }
                }
          }
        }
        .recover { case ex =>
          GUI_Thread.later {
            GUI.error_dialog(view, "Suggest Error", ex.getMessage)
          }
        }
    }
  }

  private def collectCandidates(
      view: View,
      commandText: String,
      goalState: String,
      useSledgehammer: Boolean
  ): List[Candidate] = {
    import java.util.concurrent.{
      ConcurrentLinkedQueue,
      CountDownLatch,
      TimeUnit
    }
    import java.util.concurrent.atomic.AtomicBoolean
    import scala.jdk.CollectionConverters._

    val results = new ConcurrentLinkedQueue[Candidate]()
    val useIQ = IQAvailable.isAvailable
    val sledgeCompleted = new AtomicBoolean(false)

    // Prepare context information
    val contextInfo = prepareContextInfo(view, goalState, useIQ)

    val taskCount = if (useSledgehammer) 2 else 1
    val latch = new CountDownLatch(taskCount)
    Output.writeln(
      s"[Assistant] Starting $taskCount tasks, sledgehammer=$useSledgehammer"
    )

    // Start LLM task
    startLLMTask(commandText, goalState, contextInfo, results, latch)

    // Start Sledgehammer task if enabled
    if (useSledgehammer) {
      startSledgehammerTask(
        view,
        results,
        latch,
        sledgeCompleted
      )
    }

    // Wait for completion
    val waited = latch.await(
      AssistantConstants.SUGGESTION_COLLECTION_TIMEOUT,
      TimeUnit.MILLISECONDS
    )
    Output.writeln(
      s"[Assistant] Latch done, waited=$waited, results count: ${results.size}"
    )
    // Deduplicate by proof text, preferring Sledgehammer (verified) over LLM (unverified)
    deduplicateCandidates(results.asScala.toList)
  }

  private[assistant] def deduplicateCandidates(
      candidates: List[Candidate]
  ): List[Candidate] =
    candidates
      .groupBy(_.proof)
      .values
      .map { dupes =>
        dupes.find(_.source == Sledgehammer).getOrElse(dupes.head)
      }
      .toList

  private def getCurrentTarget(
      view: View,
      @unused buffer: JEditBuffer,
      @unused offset: Int
  ): TargetParser.Target = {
    val textArea = view.getTextArea
    val selection = Option(textArea.getSelectedText).filter(_.trim.nonEmpty)
    if (selection.isDefined) {
      TargetParser.CurrentSelection
    } else {
      // Use cursor target for now - theory name resolution can be improved later
      TargetParser.CurrentCursor
    }
  }

  private def prepareContextInfo(
      view: View,
      goalState: String,
      useIQ: Boolean
  ): String = {
    if (!useIQ) ""
    else {
      val offset = view.getTextArea.getCaretPosition
      
      // Use shared ProofContextSupport to collect facts and theorems in parallel
      val bundle = ProofContextSupport.collect(
        view,
        offset,
        Some(goalState),
        includeDefinitions = false
      )
      
      List(bundle.localFacts, bundle.relevantTheorems).filter(_.nonEmpty).mkString("\n\n")
    }
  }

  private def startLLMTask(
      commandText: String,
      goalState: String,
      contextInfo: String,
      results: java.util.concurrent.ConcurrentLinkedQueue[Candidate],
      latch: CountDownLatch
  ): Unit = {
    val _ = Isabelle_Thread.fork(name = "suggest-llm") {
      try {
        val subs = buildPromptSubstitutions(commandText, goalState, contextInfo)

        Output.writeln(s"[Assistant] Suggest - Goal state:\n$goalState")
        Output.writeln(s"[Assistant] Suggest - Context:\n$contextInfo")

        val prompt = PromptLoader.load("suggest_proof_step.md", subs)
        Output.writeln(s"[Assistant] Suggest - Prompt length: ${prompt.length}")

        val args = BedrockClient.invokeInContextStructured(prompt, suggestSchema)
        Output.writeln(s"[Assistant] Suggest - Structured response: $args")

        val suggestions = parseStructuredSuggestions(args)
        Output.writeln(
          s"[Assistant] Suggest - Parsed ${suggestions.length} suggestions: $suggestions"
        )

        suggestions.foreach(s => results.add(Candidate(s, LLM)))
        Output.writeln(
          s"[Assistant] Added ${suggestions.length} LLM candidates, total now: ${results.size}"
        )
      } catch {
        case ex: Exception =>
          Output.writeln(s"[Assistant] Suggest - LLM error: ${ex.getMessage}")
      } finally {
        latch.countDown()
        Output.writeln(
          s"[Assistant] LLM task done, latch count: ${latch.getCount}"
        )
      }
    }
  }

  private def startSledgehammerTask(
      view: View,
      results: java.util.concurrent.ConcurrentLinkedQueue[Candidate],
      latch: CountDownLatch,
      sledgeCompleted: java.util.concurrent.atomic.AtomicBoolean
  ): Unit = {
    GUI_Thread.later {
      IQIntegration.runSledgehammerAsync(
        view,
        AssistantOptions.getSledgehammerTimeout,
        {
          case Right(sledgeResults) =>
            if (sledgeCompleted.compareAndSet(false, true)) {
              sledgeResults.foreach(r =>
                results.add(
                  Candidate(
                    r.proofMethod,
                    Sledgehammer,
                    VerificationBadge.Sledgehammer(Some(r.timeMs)),
                    Some(r.timeMs)
                  )
                )
              )
              latch.countDown()
            }
          case Left(_) =>
            if (sledgeCompleted.compareAndSet(false, true)) {
              latch.countDown()
            }
        }
      )
    }

    // Async timeout guard — ensures latch completes even if sledgehammer hangs
    val _ = TimeoutGuard.scheduleAction(
      AssistantOptions.getSledgehammerTimeout + AssistantConstants.SLEDGEHAMMER_GUARD_TIMEOUT
    ) {
      if (sledgeCompleted.compareAndSet(false, true)) {
        latch.countDown()
      }
    }
  }


  /** Parse suggestions from structured tool_choice response (ToolArgs). */
  private[assistant] def parseStructuredSuggestions(args: ResponseParser.ToolArgs): List[String] = {
    val suggestions = args.get("suggestions") match {
      case Some(ResponseParser.JsonValue(arrayJson)) =>
        ResponseParser.parseStringList(arrayJson)
      case _ => Nil
    }

    suggestions
      .map(_.trim)
      .filter(_.nonEmpty)
      .filter(s =>
        CommandMatcher
          .findMatchingKeyword(s, IsabelleKeywords.proofMethods)
          .isDefined
      )
      .distinct
      .take(AssistantOptions.getMaxVerifyCandidates)
  }

  private[assistant] def buildPromptSubstitutions(
      commandText: String,
      goalState: String,
      contextInfo: String
  ): Map[String, String] =
    Map(
      "command" -> commandText,
      "goal_state" -> goalState
    ) ++ (if (contextInfo.nonEmpty) Map("relevant_theorems" -> contextInfo)
          else Map.empty)

  private def verifyCandidates(
      view: View,
      candidates: List[Candidate]
  ): List[Candidate] = {
    val timeout = AssistantOptions.getVerificationTimeout
    val maxCandidates = AssistantOptions.getMaxVerifyCandidates
    val (alreadyVerified, toVerify) =
      candidates.partition(_.source == Sledgehammer)

    // Verify candidates in parallel
    val verifyList = toVerify.take(maxCandidates)
    val latch = new CountDownLatch(verifyList.length)
    val results =
      new java.util.concurrent.ConcurrentHashMap[String, Candidate]()

    for (candidate <- verifyList) {
      GUI_Thread.later {
        if (AssistantDockable.isCancelled) {
          results.put(candidate.proof, candidate)
          latch.countDown()
        } else {
          IQIntegration.verifyProofAsync(
            view,
            candidate.proof,
            timeout,
            {
              case IQIntegration.ProofSuccess(timeMs, _) =>
                results.put(
                  candidate.proof,
                  candidate.copy(
                    badge = VerificationBadge.Verified(Some(timeMs)),
                    timeMs = Some(timeMs)
                  )
                )
                latch.countDown()
              case IQIntegration.ProofFailure(error) =>
                results.put(
                  candidate.proof,
                  candidate.copy(badge =
                    VerificationBadge.Failed(error.take(30))
                  )
                )
                latch.countDown()
              case IQIntegration.ProofTimeout =>
                results.put(
                  candidate.proof,
                  candidate.copy(badge = VerificationBadge.Failed("timeout"))
                )
                latch.countDown()
              case _ =>
                results.put(candidate.proof, candidate)
                latch.countDown()
            }
          )
        }
      }
    }

    latch.await(timeout + 2000, java.util.concurrent.TimeUnit.MILLISECONDS)
    alreadyVerified ++ verifyList.map(c =>
      Option(results.get(c.proof)).getOrElse(c)
    )
  }

  def rankCandidates(candidates: List[Candidate]): List[Candidate] = {
    def priority(c: Candidate): Int = c.badge match {
      case VerificationBadge.Verified(_)     => 0
      case VerificationBadge.Sledgehammer(_) => 1
      case VerificationBadge.Unverified      => 2
      case VerificationBadge.Verifying       => 3
      case VerificationBadge.Failed(_)       => 4
      case VerificationBadge.EisbachMissing  => 5
    }
    candidates.sortBy(c => (priority(c), c.timeMs.getOrElse(Long.MaxValue)))
  }

  private def displayResults(view: View, candidates: List[Candidate]): Unit = {
    if (candidates.isEmpty) {
      AssistantDockable.respondInChat(AssistantConstants.UIText.NO_SUGGESTIONS)
    } else {

      val verifiedCount =
        candidates.count(_.badge.isInstanceOf[VerificationBadge.Verified])
      val sledgeCount =
        candidates.count(_.badge.isInstanceOf[VerificationBadge.Sledgehammer])

      val sb = new StringBuilder(
        s"Found ${candidates.length} suggestions ($verifiedCount verified, $sledgeCount sledgehammer):\n\n"
      )
      for (c <- candidates) {
        val (icon, timing, tag) = c.badge match {
          case VerificationBadge.Verified(t) =>
            ("[ok]", t.map(ms => s" (${ms}ms)").getOrElse(""), "")
          case VerificationBadge.Sledgehammer(t) =>
            (
              "[sledgehammer]",
              t.map(ms => s" (${ms}ms)").getOrElse(""),
              " [sledgehammer]"
            )
          case VerificationBadge.Unverified => ("?", "", " [unverified]")
          case VerificationBadge.Failed(r)  =>
            ("[FAIL]", "", if (r.nonEmpty) s" ($r)" else "")
          case _ => ("?", "", "")
        }
        val id = InsertHelper.registerInsertAction(view, c.proof)
        sb.append(s"$icon `${c.proof}`$timing$tag {{INSERT:$id}}\n")
      }
      ChatAction.addMessage(ChatAction.Assistant, sb.toString)
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
  }
}
