/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import java.util.concurrent.{ConcurrentLinkedQueue, CountDownLatch, TimeUnit}
import scala.jdk.CollectionConverters._

/** Autonomous proof via sketch-and-fill:
  *
  * 0. Try simple one-liner methods (by simp, by auto, by (induction x) auto, etc.)
  * 1. Sketch: N parallel LLMs generate maximally-sorry proof skeletons
  * 2. Fill: for each sorry, get actual subgoal via I/Q prefix execution,
  *    try simple methods first, then call LLM if needed
  * 3. Every intermediate state is a valid proof — no unverified claims
  *
  * Uses PIDE XML markup for structured goal analysis (free variables,
  * constants) rather than regex parsing of rendered text.
  */
object ProofLoop {
  private def maxRetries: Int = AssistantOptions.getProveRetriesPerStep
  private def stepTimeoutMs: Long = AssistantOptions.getProveStepTimeout
  private def numBranches: Int = AssistantOptions.getProveBranches
  private def maxFillAttempts: Int = AssistantOptions.getProveMaxSteps

  /** Display a transient message in the chat (not sent to LLM). Thread-safe. */
  private def chat(msg: String): Unit =
    GUI_Thread.later { ChatAction.addTransient(msg) }

  // Use shared utilities from ProofTextUtil
  private def extractCode(response: String): String =
    ProofTextUtil.extractCode(response)
  private def countSorries(proof: String): Int =
    ProofTextUtil.countSorries(proof)
  private def countUnfilled(proof: String): Int =
    ProofTextUtil.countUnfilled(proof)
  private def splitAtSorry(proof: String, n: Int): Option[(String, String)] =
    ProofTextUtil.splitAtSorry(proof, n)
  private def replaceSorry(
      proof: String,
      n: Int,
      replacement: String
  ): Option[String] = ProofTextUtil.replaceSorry(proof, n, replacement)
  private def markSorry(proof: String, n: Int): String =
    ProofTextUtil.markSorry(proof, n)

  // --- Context fetching ---

  // Delegate to ProofPlanner module
  private def fetchRichContext(
      view: View,
      command: Command,
      goalState: String,
      goalAnalysis: Option[GoalExtractor.GoalAnalysis]
  ): String =
    ProofPlanner.fetchRichContext(view, command, goalState, goalAnalysis)

  // --- I/Q interaction --- Delegate to IQExecutor for standardized latch-wait operations
  private def executeStep(
      view: View,
      command: Command,
      proofText: String
  ): Either[String, IQIntegration.ProofStepResult] = {
    Output.writeln(s"[Assistant] executeStep sending:\n$proofText")
    val result = IQExecutor.executeStep(view, command, proofText)
    Output.writeln(s"[Assistant] executeStep result: $result")
    result
  }

  private def initialGoalState(view: View): String =
    IQExecutor.getGoalState(view)
  private def analyzeGoalAtCursor(
      view: View
  ): Option[GoalExtractor.GoalAnalysis] = IQExecutor.analyzeGoalAtCursor(view)

  // Use shared sorryify and structural checks from ProofTextUtil
  private def sorryify(proof: String): String = ProofTextUtil.sorryify(proof)
  private def isStructurallyComplete(proof: String): Boolean =
    ProofTextUtil.isStructurallyComplete(proof)
  private val unfilledPattern = ProofTextUtil.unfilledPattern
  private val sorryPattern = ProofTextUtil.sorryPattern

  // --- LLM interaction ---

  private val llmCallTimeoutMs = AssistantConstants.PROVE_LLM_CALL_TIMEOUT

  /** Invoke LLM with a timeout guard. Throws on timeout or LLM error. Uses
    * invokeNoCache to avoid polluting chat history with auto-prover prompts.
    */
  private def invokeLLMWithTimeout(prompt: String): String = {
    val latch = new CountDownLatch(1)
    @volatile var result: Either[Exception, String] = Left(
      new RuntimeException("LLM call timed out")
    )
    Isabelle_Thread.fork(name = "prove-llm-call") {
      try {
        // Use invokeNoCache (stateless) — NOT invokeInContext which pollutes with chat history
        val response = BedrockClient.invokeNoCache(prompt)
        result = Right(response)
      } catch { case ex: Exception => result = Left(ex) }
      finally { latch.countDown() }
    }
    latch.await(llmCallTimeoutMs, TimeUnit.MILLISECONDS)
    result match {
      case Right(response) => response
      case Left(ex)        => throw ex
    }
  }

  // --- Simple method candidates ---

  /** Common one-liner proof methods ordered by likelihood and speed. */
  private val simpleMethods: List[String] = List(
    "by simp",
    "by auto",
    "by blast",
    "by force",
    "by fastforce",
    "by simp_all",
    "by argo",
    "by arith",
    "by linarith",
    "by presburger",
    "by meson",
    "by metis",
    "by smt"
  )

  /** Build induction/cases candidates from actual free variables (from PIDE
    * markup).
    */
  private def inductionCandidates(freeVars: List[String]): List[String] =
    freeVars.flatMap { v =>
      List(
        s"by (induction $v) auto",
        s"by (induction $v) simp_all",
        s"by (induction $v) simp",
        s"by (cases $v) auto"
      )
    }

  private[assistant] def inductionCandidatesForTest(
      freeVars: List[String]
  ): List[String] =
    inductionCandidates(freeVars)

  /** Try a list of proof methods via I/Q, returning the first that succeeds.
    * Used in Phase 0 to test simple one-liner proofs before resorting to
    * sketch-and-fill.
    */
  private def tryMethodsViaIQ(
      view: View,
      command: Command,
      methods: List[String],
      label: String
  ): Option[String] = {
    import scala.util.boundary, boundary.break

    chat(s"Trying ${methods.length} $label methods...")
    boundary {
      for (method <- methods) {
        if (AssistantDockable.isCancelled) break(None)
        val latch = new CountDownLatch(1)
        @volatile var result: Option[IQIntegration.VerificationResult] = None
        GUI_Thread.later {
          IQIntegration.verifyProofAsync(
            view,
            command,
            method,
            stepTimeoutMs,
            { r =>
              result = Some(r)
              latch.countDown()
            }
          )
        }
        latch.await(stepTimeoutMs + 2000, TimeUnit.MILLISECONDS)
        result match {
          case Some(IQIntegration.ProofSuccess(ms, _)) =>
            chat(s"  [ok] `$method` verified (${ms}ms)")
            break(Some(method))
          case _ => // try next
        }
      }
      None
    }
  }

  /** Try simple methods as actual replacements in the proof skeleton. Each
    * method is substituted for the first sorry and verified via I/Q. Returns
    * Some(newProof) with the sorry replaced, or None.
    */
  private def trySimpleReplacements(
      view: View,
      command: Command,
      proof: String
  ): Option[String] = {
    import scala.util.boundary, boundary.break

    chat(s"Trying ${simpleMethods.length} simple replacements...")
    boundary {
      for (method <- simpleMethods) {
        if (AssistantDockable.isCancelled) break(None)
        replaceSorry(proof, 0, method).foreach { newProof =>
          executeStep(view, command, newProof) match {
            case Right(_) =>
              chat(s"  [ok] `$method` verified as replacement")
              break(Some(newProof))
            case _ => // try next
          }
        }
      }
      None
    }
  }

  /** Determine what replacement was made between two proof strings (for
    * display). Extracts the text that replaced the first sorry by diffing
    * prefix/suffix.
    */
  private def findReplacement(oldProof: String, newProof: String): String = {
    splitAtSorry(oldProof, 0) match {
      case Some((prefix, suffix)) =>
        val replacement = newProof.stripPrefix(prefix).stripSuffix(suffix).trim
        if (replacement.nonEmpty) replacement else "(unknown method)"
      case None => "(unknown method)"
    }
  }

  private[assistant] def findReplacementForTest(
      oldProof: String,
      newProof: String
  ): String =
    findReplacement(oldProof, newProof)

  // --- Proof planning ---

  /** Create an informal proof plan by analyzing the goal, definitions, and
    * available lemmas. The plan is fed into all subsequent phases to guide
    * skeleton generation, fill, and refinement.
    */
  // Delegate to ProofPlanner module
  private def createProofPlan(
      commandText: String,
      goalState: String,
      context: String
  ): String =
    ProofPlanner.createProofPlan(commandText, goalState, context)

  // --- Phase 0: Simple methods ---

  /** Try simple one-liner proofs using PIDE-extracted free variables for
    * induction. Also runs sledgehammer in parallel since we're at the command
    * level where it works correctly.
    */
  private def trySimpleMethods(
      view: View,
      command: Command,
      analysis: GoalExtractor.GoalAnalysis
  ): Option[String] = {
    val candidates = simpleMethods ++ inductionCandidates(analysis.freeVars)
    chat(
      s"## Phase 0: Simple Methods\nFree variables from PIDE: ${analysis.freeVars.mkString(", ")}"
    )

    // Run sledgehammer in parallel with simple methods (only at command level, not during fill)
    val sledgeLatch = new CountDownLatch(1)
    @volatile var sledgeResults: List[IQIntegration.SledgehammerResult] = Nil
    if (IQAvailable.isAvailable && AssistantOptions.getUseSledgehammer) {
      chat("Running sledgehammer in parallel...")
      val timeout = AssistantOptions.getSledgehammerTimeout
      GUI_Thread.later {
        IQIntegration.runSledgehammerAsync(
          view,
          command,
          timeout,
          {
            case Right(results) =>
              sledgeResults = results; sledgeLatch.countDown()
            case Left(_) => sledgeLatch.countDown()
          }
        )
      }
    } else {
      sledgeLatch.countDown()
    }

    // Try simple methods first
    val simpleResult = tryMethodsViaIQ(view, command, candidates, "simple")
    if (simpleResult.isDefined) {
      sledgeLatch.countDown() // Cancel waiting for sledgehammer
      return simpleResult
    }

    // Wait for sledgehammer to complete
    val sledgeTimeout = AssistantOptions.getSledgehammerTimeout
    sledgeLatch.await(sledgeTimeout + 5000, TimeUnit.MILLISECONDS)

    if (sledgeResults.nonEmpty) {
      chat(s"Sledgehammer found ${sledgeResults.length} methods")
      // Try each sledgehammer result
      import scala.util.boundary, boundary.break
      val sledgeResult = boundary {
        for (result <- sledgeResults) {
          if (AssistantDockable.isCancelled) break(None)
          val method = result.proofMethod
          val latch = new CountDownLatch(1)
          @volatile var verifyResult: Option[IQIntegration.VerificationResult] =
            None
          GUI_Thread.later {
            IQIntegration.verifyProofAsync(
              view,
              command,
              method,
              stepTimeoutMs,
              { r =>
                verifyResult = Some(r)
                latch.countDown()
              }
            )
          }
          latch.await(stepTimeoutMs + 2000, TimeUnit.MILLISECONDS)
          verifyResult match {
            case Some(IQIntegration.ProofSuccess(ms, _)) =>
              chat(s"  [ok] Sledgehammer: `$method` (${result.timeMs}ms)")
              break(Some(method))
            case _ => // try next
          }
        }
        None
      }
      if (sledgeResult.isDefined) return sledgeResult
    }

    chat(
      "No simple method or sledgehammer worked, proceeding to sketch-and-fill..."
    )
    None
  }

  // --- Phase 1: Skeleton generation ---

  /** Delegate to SketchGenerator module for cleaner separation of concerns. */
  private def sketchPhase(
      view: View,
      command: Command,
      commandText: String,
      goalState: String,
      context: String,
      plan: String,
      deadline: Long
  ): Option[String] = {
    SketchGenerator.generateSkeleton(
      view,
      command,
      commandText,
      goalState,
      context,
      plan,
      deadline
    )
  }

  // --- Phase 2: Fill sorries ---

  /** Maximum number of refinement rounds per original sorry position. */
  private val maxRefinementDepth = 2

  /** Fill phase: iteratively replace sorries with verified proof steps. Tries
    * simple methods first, then LLM, diagnosis-driven retry, refinement, and
    * lemma speculation. Each filled sorry is verified by I/Q before proceeding
    * to the next.
    */
  private def fillPhase(
      view: View,
      command: Command,
      commandText: String,
      initialSketch: String,
      context: String,
      plan: String,
      deadline: Long
  ): String = {
    var proof = initialSketch
    Output.writeln(
      s"[Assistant] fillPhase initial sketch (${proof.length} chars):\n---\n$proof\n---"
    )
    var step = 0
    var refinementCount = 0 // Track total refinements to prevent runaway

    while (
      countSorries(
        proof
      ) > 0 && step < maxFillAttempts && !AssistantDockable.isCancelled && System
        .currentTimeMillis() < deadline
    ) {
      val remaining = countSorries(proof)
      step += 1
      AssistantDockable.setStatus(
        s"Proving... step $step ($remaining sorries remaining)"
      )

      chat(
        s"## Fill step $step ($remaining remaining)\n```isabelle\n${markSorry(proof, 0).linesIterator.take(15).mkString("\n")}\n```"
      )

      // Get the actual subgoal by sending the proof prefix to I/Q
      val goalForFill = getSubgoalAtSorry(view, command, proof)

      // Phase 2a: Try simple methods as replacements in the skeleton (no LLM needed)
      val simpleResult = trySimpleReplacements(view, command, proof)
      val filledSimple = simpleResult.map { newProof =>
        val method = findReplacement(proof, newProof)
        chat(s"Filled with `$method` (simple method, no LLM needed)")
        newProof
      }

      // Collect errors from simple method attempts (done once, reused by diagnosis/speculation)
      val failedErrors: List[(String, String)] =
        if (filledSimple.isDefined) Nil
        else {
          simpleMethods.take(5).flatMap { method =>
            replaceSorry(proof, 0, method).flatMap { newProof =>
              executeStep(view, command, newProof) match {
                case Left(err) => Some((method, err))
                case Right(_)  => None // shouldn't happen, already tried
              }
            }
          }
        }

      val filled = filledSimple
        .orElse {
          // Phase 2a.5 removed - sledgehammer only runs in Phase 0 on the top-level goal
          // We can't run it on intermediate sorry positions without creating synthetic commands
          // Phase 2b: Call LLM for this subgoal (one-liner methods)
          fillViaLLM(
            view,
            command,
            commandText,
            proof,
            goalForFill,
            context,
            plan
          )
        }
        .orElse {
          // Phase 2c: Diagnosis-driven retry — ask LLM what went wrong and get specific methods
          if (
            !AssistantDockable.isCancelled && System
              .currentTimeMillis() < deadline && failedErrors.nonEmpty
          ) {
            chat("Phase 2c: Diagnosis-driven retry...")
            diagnosisRetry(
              view,
              command,
              commandText,
              proof,
              goalForFill,
              context,
              plan,
              failedErrors
            )
          } else None
        }
        .orElse {
          // Phase 2d: Refinement — decompose the sorry into a sub-proof with simpler sorries
          if (
            !AssistantDockable.isCancelled && System
              .currentTimeMillis() < deadline &&
            refinementCount < maxRefinementDepth * 3
          ) {
            chat("Phase 2d: Refining sorry into sub-proof...")
            refineSorry(
              view,
              command,
              commandText,
              proof,
              goalForFill,
              context,
              plan
            ).map { newProof =>
              refinementCount += 1
              newProof
            }
          } else None
        }

      val finalFilled = filled.orElse {
        // Phase 2e: Lemma speculation — speculate and prove a missing auxiliary lemma,
        // insert it before the main lemma, then retry.
        if (
          !AssistantDockable.isCancelled && System
            .currentTimeMillis() < deadline &&
          refinementCount < maxRefinementDepth * 3
        ) {
          chat("Phase 2e: Speculating auxiliary lemma...")
          speculateLemma(
            view,
            command,
            commandText,
            proof,
            goalForFill,
            context,
            plan,
            failedErrors
          )
        } else None
      }

      finalFilled match {
        case Some(newProof) =>
          proof = newProof
          chat(s"${countSorries(proof)} sorries remaining")
        case None =>
          chat("Could not fill or refine this sorry, marking as unfilled")
          proof =
            replaceSorry(proof, 0, "sorry (* unfilled *)").getOrElse(proof)
      }
    }
    proof
  }

  // --- Phase 2c: Diagnosis-driven retry ---

  /** Ask LLM for alternative methods based on previously collected errors. */
  private def diagnosisRetry(
      view: View,
      command: Command,
      commandText: String,
      proof: String,
      goalForFill: String,
      context: String,
      plan: String = "",
      failedErrors: List[(String, String)] = Nil
  ): Option[String] = {
    try {
      val failedMethods = failedErrors.map(_._1)
      val errorMessages = failedErrors.map { case (m, e) => s"- `$m`: $e" }

      if (failedMethods.isEmpty) None
      else {

        val subs = Map(
          "goal_state" -> goalForFill,
          "command" -> commandText,
          "proof_context" -> markSorry(proof, 0),
          "failed_methods" -> failedMethods.mkString(", "),
          "error_messages" -> errorMessages.mkString("\n")
        ) ++ (if (context.nonEmpty) Map("relevant_theorems" -> context)
              else Map.empty)
          ++ (if (plan.nonEmpty) Map("proof_plan" -> plan) else Map.empty)

        val response = invokeLLMWithTimeout(
          PromptLoader.load("prove_diagnose_retry.md", subs)
        )
        val suggestions = SuggestAction.parseLLMSuggestions(response)
        chat(
          s"Diagnosis suggests ${suggestions.length} methods: ${suggestions.map(s => s"`$s`").mkString(", ")}"
        )

        // Verify each suggestion as a replacement
        import scala.util.boundary, boundary.break
        boundary {
          for (method <- suggestions) {
            if (AssistantDockable.isCancelled) break(None)
            replaceSorry(proof, 0, method).foreach { newProof =>
              executeStep(view, command, newProof) match {
                case Right(_) =>
                  chat(s"  [ok] Diagnosis suggestion `$method` verified!")
                  break(Some(newProof))
                case Left(err) =>
                  chat(s"  [FAIL] `$method`: $err")
              }
            }
          }
          None
        }
      } // end if failedMethods.nonEmpty
    } catch {
      case _: Exception => None
    }
  }

  // --- Phase 2d: Sorry refinement ---

  /** Replace a sorry with a multi-step sub-proof, each step ending in sorry.
    * Tries multiple LLM branches (like the sketch phase) to increase chances of
    * generating valid Isabelle syntax.
    */
  private def refineSorry(
      view: View,
      command: Command,
      commandText: String,
      proof: String,
      goalForFill: String,
      context: String,
      plan: String = ""
  ): Option[String] = {
    val failedList = simpleMethods.take(5).mkString(", ")
    val subs = Map(
      "goal_state" -> goalForFill,
      "command" -> commandText,
      "proof_context" -> markSorry(proof, 0),
      "failed_methods" -> failedList
    ) ++ (if (context.nonEmpty) Map("relevant_theorems" -> context)
          else Map.empty) ++
      (if (plan.nonEmpty) Map("proof_plan" -> plan) else Map.empty)

    // Generate multiple refinement candidates in parallel
    val candidates = new ConcurrentLinkedQueue[String]()
    val latch = new CountDownLatch(numBranches)
    for (i <- 1 to numBranches) {
      Isabelle_Thread.fork(name = s"prove-refine-$i") {
        try {
          val refinement = extractCode(
            invokeLLMWithTimeout(PromptLoader.load("prove_refine.md", subs))
          )
          if (refinement.nonEmpty) candidates.add(refinement)
        } catch {
          case ex: Exception => ErrorHandler.logSilentError("ProofLoop", ex)
        }
        latch.countDown()
      }
    }
    latch.await(llmCallTimeoutMs, TimeUnit.MILLISECONDS)

    val all = candidates.asScala.toList.distinct
    if (all.isEmpty) { chat("No refinement candidates generated"); None }
    else {
      chat(
        s"Generated ${all.length} refinement candidates, checking via I/Q..."
      )

      import scala.util.boundary, boundary.break
      boundary {
        for (refinement <- all) {
          if (AssistantDockable.isCancelled) break(None)
          chat(
            s"Refinement candidate:\n```isabelle\n${refinement.linesIterator.take(8).mkString("\n")}\n```"
          )

          replaceSorry(proof, 0, refinement) match {
            case None           => chat("  Could not substitute refinement")
            case Some(newProof) =>
              val newSorries = countSorries(newProof)
              val oldSorries = countSorries(proof)

              if (newSorries <= oldSorries) {
                chat(
                  s"  Refinement didn't add new sorries ($newSorries ≤ $oldSorries), skipping"
                )
              } else {
                executeStep(view, command, newProof) match {
                  case Right(_) =>
                    chat(
                      s"  [ok] Refinement verified ($newSorries sorries, was $oldSorries)"
                    )
                    break(Some(newProof))
                  case Left(err) =>
                    chat(s"  [FAIL] I/Q rejected: $err")
                }
              }
          }
        }
        None
      }
    }
  }

  // --- Phase 2e: Lemma speculation ---

  /** Speculate an auxiliary lemma that the current sorry needs, prove it
    * recursively using the same proof machinery, insert it before the main
    * lemma in the buffer, and retry the sorry. This handles cases like missing
    * left-distributivity lemmas.
    */
  private def speculateLemma(
      view: View,
      command: Command,
      commandText: String,
      proof: String,
      goalForFill: String,
      context: String,
      plan: String = "",
      failedErrors: List[(String, String)] = Nil
  ): Option[String] = {
    try {
      // Use pre-collected errors if available, otherwise collect fresh
      val errorMessages = if (failedErrors.nonEmpty) {
        failedErrors.map { case (m, e) => s"- `$m`: $e" }
      } else {
        simpleMethods.take(5).flatMap { method =>
          replaceSorry(proof, 0, method).flatMap { newProof =>
            executeStep(view, command, newProof) match {
              case Left(err) => Some(s"- `$method`: $err")
              case Right(_)  => None
            }
          }
        }
      }
      val failedMethodNames =
        if (failedErrors.nonEmpty) failedErrors.map(_._1)
        else simpleMethods.take(5)

      val subs = Map(
        "goal_state" -> goalForFill,
        "command" -> commandText,
        "proof_context" -> markSorry(proof, 0),
        "failed_methods" -> failedMethodNames.mkString(", "),
        "error_messages" -> errorMessages.mkString("\n")
      ) ++ (if (context.nonEmpty) Map("relevant_theorems" -> context)
            else Map.empty)
        ++ (if (plan.nonEmpty) Map("proof_plan" -> plan) else Map.empty)

      // Ask LLM to speculate an auxiliary lemma STATEMENT (no proof)
      val response = invokeLLMWithTimeout(
        PromptLoader.load("prove_speculate_lemma.md", subs.toMap)
      )
      val lemmaStatement = extractLemmaStatement(response)

      if (lemmaStatement.isEmpty) {
        chat("  No lemma statement generated")
        return None
      }

      val lemmaName = extractLemmaName(lemmaStatement)
      chat(s"Speculated lemma `$lemmaName`:\n```isabelle\n$lemmaStatement\n```")

      // Insert the lemma statement with `sorry` as placeholder proof
      val lemmaWithSorry = lemmaStatement.trim + "\n  sorry"
      val insertedLength =
        insertLemmaBeforeCommand(view, command, lemmaWithSorry)
      if (insertedLength <= 0) {
        chat("  Could not insert lemma into buffer")
        return None
      }

      chat(s"Inserted `$lemmaName` (with sorry) before main lemma")

      // Wait for PIDE to process and check for errors
      if (awaitAndCheckErrorsAtOffset(view, insertedLength)) {
        chat("  PIDE rejected speculated lemma statement, undoing...")
        undoLemmaInsertion(view)
        return None
      }

      // Now try to prove the speculated lemma using our proof machinery.
      // First, try simple one-liner methods on it.
      chat(s"## Proving speculated lemma `$lemmaName`...")

      // Get the command object for the newly inserted lemma
      val lemmaCmd = getLemmaCommandAtOffset(view)
      if (lemmaCmd.isEmpty) {
        chat("  Could not find speculated lemma command, undoing...")
        undoLemmaInsertion(view)
        return None
      }

      // Use the FULL proof pipeline to prove the speculated lemma — same
      // machinery as the main lemma (Phase 0 → 1 → 2 with all sub-phases).
      val lemmaGoalState = initialGoalState(view)
      val lemmaProof = proveLemmaFull(
        view,
        lemmaCmd.get,
        lemmaStatement.trim,
        lemmaGoalState,
        context
      )

      if (lemmaProof.isEmpty) {
        chat(s"  Could not prove speculated lemma `$lemmaName`, undoing...")
        undoLemmaInsertion(view)
        return None
      }

      // Replace the sorry in the buffer with the actual proof
      val proofText = lemmaProof.get
      replaceSorryInBuffer(
        view,
        lemmaWithSorry,
        lemmaStatement.trim + "\n" + proofText
      )

      // Wait for PIDE to re-process the proven lemma and check for errors
      val hasErrors =
        awaitAndCheckErrorsAtOffset(view, insertedLength + proofText.length)
      if (hasErrors) {
        chat(s"  PIDE rejected proved lemma, undoing...")
        undoLemmaInsertion(view)
        return None
      }

      chat(s"  **Speculated lemma `$lemmaName` proved and verified by PIDE!**")

      // Now retry the original sorry — the new lemma should be in the simpset
      val methodsToTry = List(
        "by simp",
        "by auto",
        s"by (simp add: $lemmaName)",
        s"by (auto simp add: $lemmaName)",
        s"by (metis $lemmaName)",
        "by argo"
      )

      import scala.util.boundary, boundary.break
      val result = boundary {
        for (method <- methodsToTry) {
          if (AssistantDockable.isCancelled) break(None)
          replaceSorry(proof, 0, method).foreach { newProof =>
            executeStep(view, command, newProof) match {
              case Right(_) =>
                chat(
                  s"  [ok] Sorry filled with `$method` using speculated lemma!"
                )
                break(Some(newProof))
              case Left(err) =>
                chat(s"  [FAIL] `$method`: $err")
            }
          }
        }
        None
      }

      if (result.isEmpty) {
        chat(
          "  Speculated lemma didn't help close the sorry, undoing insertion..."
        )
        undoLemmaInsertion(view)
      }
      result
    } catch {
      case ex: Exception =>
        Output.writeln(
          s"[Assistant] Lemma speculation failed: ${ex.getMessage}"
        )
        None
    }
  }

  /** Prove a speculated lemma using the full proof pipeline (Phase 0 → 1 → 2).
    * This is a simplified version of `run` that operates on the speculated
    * lemma instead of the main goal. Does NOT call Phase 2e (no recursive
    * speculation). Returns Some(proofText) or None.
    */
  private def proveLemmaFull(
      view: View,
      lemmaCmd: Command,
      lemmaText: String,
      goalState: String,
      context: String
  ): Option[String] = {
    val deadline =
      System.currentTimeMillis() + AssistantConstants.PROVE_LEMMA_SUB_DEADLINE

    // Get PIDE analysis for the speculated lemma — must analyze at lemma's offset,
    // not the cursor (which is still at the main lemma)
    val lemmaOffset = findCommandOffset(view, lemmaCmd)
    val goalAnalysis =
      lemmaOffset.flatMap(off => analyzeGoalAtOffset(view, off))
    val freeVars = goalAnalysis.map(_.freeVars).getOrElse(Nil)

    // If PIDE didn't give us vars, extract them from the lemma statement text
    val effectiveVars =
      if (freeVars.nonEmpty) freeVars
      else extractVarsFromStatement(lemmaText)
    chat(s"  Lemma free vars: ${effectiveVars.mkString(", ")}")

    // Phase 0: Simple methods + induction candidates
    val candidates = simpleMethods ++ inductionCandidates(effectiveVars)
    chat(
      s"  Phase 0: Trying ${candidates.length} methods on speculated lemma..."
    )
    val phase0 = tryMethodsViaIQ(view, lemmaCmd, candidates, "lemma")
    if (phase0.isDefined) return phase0

    // Phase 0.5: Sledgehammer on the speculated lemma
    if (IQAvailable.isAvailable && !AssistantDockable.isCancelled) {
      chat(s"  Running sledgehammer on speculated lemma...")
      val timeout = AssistantOptions.getSledgehammerTimeout
      val sledgeLatch = new CountDownLatch(1)
      @volatile var sledgeResults: List[IQIntegration.SledgehammerResult] = Nil
      GUI_Thread.later {
        IQIntegration.runSledgehammerAsync(
          view,
          lemmaCmd,
          timeout,
          {
            case Right(results) =>
              sledgeResults = results; sledgeLatch.countDown()
            case Left(_) => sledgeLatch.countDown()
          }
        )
      }
      sledgeLatch.await(timeout + 5000, TimeUnit.MILLISECONDS)
      if (sledgeResults.nonEmpty) {
        val method = sledgeResults.head.proofMethod
        chat(s"  [ok] Sledgehammer: `$method`")
        return Some(method)
      }
    }

    if (AssistantDockable.isCancelled || System.currentTimeMillis() > deadline)
      return None

    // Phase 1: Skeleton generation for the speculated lemma
    chat(s"  Phase 1: Generating skeleton for speculated lemma...")
    val skeleton =
      sketchPhase(view, lemmaCmd, lemmaText, goalState, context, "", deadline)
    if (skeleton.isEmpty || AssistantDockable.isCancelled) return None

    // Phase 2: Fill sorries (limited — no Phase 2e to prevent infinite recursion)
    chat(s"  Phase 2: Filling sorries in speculated lemma skeleton...")
    val filledProof = fillPhaseLimited(
      view,
      lemmaCmd,
      lemmaText,
      skeleton.get,
      context,
      deadline
    )
    val remaining = countSorries(filledProof) + countUnfilled(filledProof)

    if (remaining == 0) {
      chat(s"  **Speculated lemma proof complete!**")
      Some(filledProof)
    } else {
      chat(s"  Speculated lemma has $remaining unfilled sorries")
      None
    }
  }

  /** Limited fill phase for speculated lemmas — runs 2a/2b/2c/2d but NOT 2e (no
    * recursive lemma speculation to prevent infinite recursion).
    */
  private def fillPhaseLimited(
      view: View,
      command: Command,
      commandText: String,
      initialSketch: String,
      context: String,
      deadline: Long
  ): String = {
    var proof = initialSketch
    var step = 0
    val maxSteps = AssistantConstants.PROVE_LEMMA_MAX_STEPS

    while (
      countSorries(
        proof
      ) > 0 && step < maxSteps && !AssistantDockable.isCancelled && System
        .currentTimeMillis() < deadline
    ) {
      val remaining = countSorries(proof)
      step += 1
      chat(s"  Lemma fill step $step ($remaining remaining)")

      val goalForFill = getSubgoalAtSorry(view, command, proof)

      // 2a: Simple replacements (sledgehammer removed from fill phase - only runs in Phase 0)
      val filled = trySimpleReplacements(view, command, proof)
        .orElse {
          // 2b: LLM
          fillViaLLM(
            view,
            command,
            commandText,
            proof,
            goalForFill,
            context,
            ""
          )
        }
        .orElse {
          // 2c: Diagnosis retry
          if (
            !AssistantDockable.isCancelled && System
              .currentTimeMillis() < deadline
          )
            diagnosisRetry(
              view,
              command,
              commandText,
              proof,
              goalForFill,
              context,
              ""
            )
          else None
        }
        .orElse {
          // 2d: Refinement
          if (
            !AssistantDockable.isCancelled && System
              .currentTimeMillis() < deadline
          )
            refineSorry(
              view,
              command,
              commandText,
              proof,
              goalForFill,
              context,
              ""
            )
          else None
        }
      // NOTE: No Phase 2e here — no recursive speculation

      filled match {
        case Some(newProof) => proof = newProof
        case None           =>
          proof =
            replaceSorry(proof, 0, "sorry (* unfilled *)").getOrElse(proof)
      }
    }
    proof
  }

  // Delegate to IQExecutor
  private def findCommandOffset(view: View, cmd: Command): Option[Int] =
    IQExecutor.findCommandOffset(view, cmd)

  private def analyzeGoalAtOffset(
      view: View,
      offset: Int
  ): Option[GoalExtractor.GoalAnalysis] =
    IQExecutor.analyzeGoalAtOffset(view, offset)

  // Use shared extraction methods from ProofTextUtil
  private def extractVarsFromStatement(statement: String): List[String] =
    ProofTextUtil.extractVarsFromStatement(statement)
  private def extractLemmaStatement(response: String): String =
    ProofTextUtil.extractLemmaStatement(response)
  private def extractLemmaName(code: String): String =
    ProofTextUtil.extractLemmaName(code)

  /** Get the PIDE Command object for the lemma at the current cursor position.
    */
  private def getLemmaCommandAtOffset(view: View): Option[Command] =
    IQExecutor.getCommandAtCursor(view)

  /** Replace text in the buffer (used to swap sorry for actual proof in
    * speculated lemma).
    */
  private def replaceSorryInBuffer(
      view: View,
      oldText: String,
      newText: String
  ): Unit = {
    GUIThreadUtil.awaitOnGUIThread(5000) {
      val buffer = view.getBuffer
      val content = buffer.getText(0, buffer.getLength)
      val idx = content.indexOf(oldText)
      if (idx >= 0) {
        buffer.beginCompoundEdit()
        try {
          buffer.remove(idx, oldText.length)
          buffer.insert(idx, newText)
        } finally {
          buffer.endCompoundEdit()
        }
      }
    }
  }

  /** Insert lemma text before the current command in the buffer. Finds the
    * start of the current top-level command (lemma/theorem) using PIDE command
    * structure, and inserts the new lemma before it. Must dispatch buffer edits
    * to the GUI thread. Returns the length of inserted text (>0 on success, 0
    * on failure).
    */
  private def insertLemmaBeforeCommand(
      view: View,
      command: Command,
      lemmaCode: String
  ): Int = {
    val latch = new CountDownLatch(1)
    @volatile var insertedLength = 0
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        val caretPos = view.getTextArea.getCaretPosition
        Document_Model.get_model(buffer).foreach { model =>
          val snapshot = Document_Model.snapshot(model)
          val node = snapshot.get_node(model.node_name)
          // Find the command at cursor position — this is the main lemma being proved
          val targetCmd = node
            .command_iterator(Text.Range(caretPos, caretPos + 1))
            .toList
            .headOption
          // Walk backwards to find the outermost lemma/theorem command
          val allCmds = node.command_iterator().toList
          val topLevelStarters = IsabelleKeywords.proofStarters
          val insertOffset = targetCmd match {
            case Some((cmd, cmdOff)) =>
              // Find this command's index and walk back to the nearest top-level starter
              val idx = allCmds.indexWhere { case (c, _) => c.id == cmd.id }
              if (idx >= 0) {
                var i = idx
                while (
                  i >= 0 && !topLevelStarters.contains(allCmds(i)._1.span.name)
                ) i -= 1
                if (i >= 0) allCmds(i)._2 else cmdOff
              } else cmdOff
            case None => caretPos
          }
          // Insert the lemma + blank line before the top-level command
          val insertText = "\n" + lemmaCode.trim + "\n\n"
          buffer.beginCompoundEdit()
          try {
            buffer.insert(insertOffset, insertText)
            insertedLength = insertText.length
          } finally {
            buffer.endCompoundEdit()
          }
        }
      } catch {
        case ex: Exception => ErrorHandler.logSilentError("ProofLoop", ex)
      }
      latch.countDown()
    }
    latch.await(
      AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC,
      TimeUnit.SECONDS
    )
    insertedLength
  }

  /** Await PIDE processing then check if the PIDE document has errors in the
    * region starting at the cursor. Used to verify speculated lemmas after
    * insertion.
    */
  private def awaitAndCheckErrorsAtOffset(
      view: View,
      regionLength: Int
  ): Boolean = {
    import scala.concurrent.{Await, Promise, Future}
    import scala.concurrent.duration._

    val p = Promise[Boolean]()
    val timeoutGuard = TimeoutGuard.scheduleTimeout(
      p,
      AssistantConstants.PIDE_PROCESSING_DELAY * 2,
      "PIDE check timeout"
    )

    // We register a transient subscription to Commands_Changed.
    // If the snapshot implies our region is fully evaluated, we remove the sub and complete the promise.
    var subscription: AssistantStatusSubscription[Session.Commands_Changed] =
      null
    subscription = AssistantStatusSubscription.create(
      PIDE.session,
      "proof-loop-error-check",
      _ => {
        GUI_Thread.later {
          try {
            val buffer = view.getBuffer
            val caretPos = view.getTextArea.getCaretPosition
            val checkStart = math.max(0, caretPos - regionLength - 100)
            val checkEnd = caretPos

            Document_Model.get_model(buffer).foreach { model =>
              val snapshot = Document_Model.snapshot(model)
              // Only evaluate errors once the snapshot is fully updated for this node
              if (!snapshot.is_outdated) {
                val range = Text.Range(checkStart, checkEnd)
                val errors = snapshot.cumulate(
                  range,
                  false,
                  Markup
                    .Elements(Markup.ERROR_MESSAGE, Markup.ERROR, Markup.BAD),
                  _ => { case _ =>
                    Some(true)
                  }
                )

                val hasErrors = errors.exists(_._2)
                p.trySuccess(hasErrors)
              }
            }
          } catch {
            case ex: Exception => ErrorHandler.logSilentError("ProofLoop", ex)
          }
        }
      }
    )

    subscription.start()

    // Force one initial check in case the snapshot is already fully evaluated
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        Document_Model.get_model(buffer).foreach { model =>
          val snapshot = Document_Model.snapshot(model)
          if (!snapshot.is_outdated && !p.isCompleted) {
            val caretPos = view.getTextArea.getCaretPosition
            val checkStart = math.max(0, caretPos - regionLength - 100)
            val checkEnd = caretPos
            val range = Text.Range(checkStart, checkEnd)
            val errors = snapshot.cumulate(
              range,
              false,
              Markup.Elements(Markup.ERROR_MESSAGE, Markup.ERROR, Markup.BAD),
              _ => { case _ =>
                Some(true)
              }
            )
            p.trySuccess(errors.exists(_._2))
          }
        }
      } catch {
        case ex: Exception => ErrorHandler.logSilentError("ProofLoop", ex)
      }
    }

    try {
      // We block here, but it's guaranteed to be bounded by the semantic timeout
      val hasErrors = Await.result(p.future, Duration.Inf)
      hasErrors
    } catch {
      case _: java.util.concurrent.TimeoutException =>
        // If PIDE is exceptionally slow, fallback to assuming errors to be safe
        chat("  (Warning: PIDE check timed out, assuming errors)")
        true
      case _: Exception => true
    } finally {
      timeoutGuard()
      if (subscription != null) subscription.stop()
    }
  }

  /** Undo the last buffer edit (the lemma insertion). Uses jEdit's compound
    * edit mechanism — the insertion was wrapped in
    * beginCompoundEdit/endCompoundEdit.
    */
  private def undoLemmaInsertion(view: View): Unit = {
    val latch = new CountDownLatch(1)
    GUI_Thread.later {
      try {
        view.getBuffer.undo(view.getTextArea)
      } catch {
        case ex: Exception => ErrorHandler.logSilentError("ProofLoop", ex)
      }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
  }

  /** Get the actual subgoal at the first sorry position by executing the proof
    * prefix. This is critical for ensuring the LLM sees the correct goal
    * context when filling sorries.
    */
  private def getSubgoalAtSorry(
      view: View,
      command: Command,
      proof: String
  ): String = {
    splitAtSorry(proof, 0) match {
      case Some((prefix, _)) if prefix.trim.nonEmpty =>
        val stepResult = executeStep(view, command, prefix.trim)
        stepResult match {
          case Right(result)
              if result.stateText.trim.nonEmpty
                && !result.stateText.contains("PROOF_COMPLETE")
                && !result.stateText.contains("No subgoals") =>
            Output.writeln(
              s"[Assistant] Got actual subgoal from prefix: ${result.stateText.take(200)}"
            )
            chat(
              s"Subgoal:\n```\n${result.stateText.linesIterator.take(8).mkString("\n")}\n```"
            )
            result.stateText
          case Right(result) =>
            Output.writeln(
              s"[Assistant] Prefix returned complete/empty state, falling back"
            )
            initialGoalState(view)
          case Left(err) =>
            Output.writeln(
              s"[Assistant] Prefix execution failed ($err), falling back"
            )
            initialGoalState(view)
        }
      case _ =>
        Output.writeln(
          "[Assistant] No prefix before sorry, using original goal"
        )
        initialGoalState(view)
    }
  }

  /** Try to fill the first sorry via LLM candidates. Generates N parallel LLM
    * suggestions and verifies each via I/Q. Returns Some(newProof) with the
    * sorry replaced, or None.
    */
  private def fillViaLLM(
      view: View,
      command: Command,
      commandText: String,
      proof: String,
      goalForFill: String,
      context: String,
      plan: String = ""
  ): Option[String] = {
    chat(s"Generating $numBranches LLM candidates...")
    val fills = new ConcurrentLinkedQueue[String]()
    val fillLatch = new CountDownLatch(numBranches)
    for (i <- 1 to numBranches) {
      Isabelle_Thread.fork(name = s"prove-fill-$i") {
        try {
          val subs = Map(
            "goal_state" -> goalForFill,
            "command" -> commandText,
            "proof_context" -> markSorry(proof, 0)
          ) ++ (if (context.nonEmpty) Map("relevant_theorems" -> context)
                else Map.empty) ++
            (if (plan.nonEmpty) Map("proof_plan" -> plan) else Map.empty)
          val code = extractCode(
            invokeLLMWithTimeout(PromptLoader.load("prove_fill.md", subs))
          )
          if (code.nonEmpty) fills.add(code)
        } catch {
          case ex: Exception => ErrorHandler.logSilentError("ProofLoop", ex)
        }
        fillLatch.countDown()
      }
    }
    fillLatch.await(60, TimeUnit.SECONDS)
    val candidates = fills.asScala.toList.distinct

    if (candidates.isEmpty) {
      chat("No LLM candidates generated")
      None
    } else {
      for ((c, i) <- candidates.zipWithIndex)
        chat(s"  ${i + 1}. `${c.linesIterator.next().take(60)}`")

      chat(s"Verifying ${candidates.length} candidates...")
      var result: Option[String] = None
      for (
        fill <- candidates if result.isEmpty && !AssistantDockable.isCancelled
      ) {
        replaceSorry(proof, 0, fill).foreach { newProof =>
          executeStep(view, command, newProof) match {
            case Right(_) =>
              chat(s"  [ok] `${fill.linesIterator.next().take(50)}`")
              result = Some(newProof)
            case Left(err) =>
              chat(s"  [FAIL] `${fill.linesIterator.next()}`: $err")
          }
        }
      }
      result
    }
  }

  /** Collect the actual subgoals at each unfilled sorry position by executing
    * prefixes. Used for diagnosis output when proof completion fails. Note:
    * This re-executes prefixes for each sorry, which can be slow for many
    * sorries.
    */
  private def collectUnfilledSubgoals(
      view: View,
      command: Command,
      proof: String
  ): String = {
    // Find all sorry (* unfilled *) positions and get their subgoals
    val unfilledPositions = unfilledPattern.findAllMatchIn(proof).toList
    val subgoals = scala.collection.mutable.ListBuffer[String]()

    for ((m, idx) <- unfilledPositions.zipWithIndex) {
      val prefix = proof.substring(0, m.start).trim
      if (prefix.nonEmpty) {
        val stepResult = executeStep(view, command, prefix)
        stepResult match {
          case Right(result)
              if result.stateText.trim.nonEmpty
                && !result.stateText.contains("PROOF_COMPLETE")
                && !result.stateText.contains("No subgoals") =>
            subgoals += s"Sorry ${idx + 1}:\n${result.stateText.trim}"
          case Left(err) =>
            subgoals += s"Sorry ${idx + 1}: (could not retrieve subgoal: $err)"
          case _ =>
            subgoals += s"Sorry ${idx + 1}: (subgoal not available)"
        }
      }
    }

    // Also check regular (non-marked) sorries
    val regularPositions = sorryPattern.findAllMatchIn(proof).toList
    for ((m, idx) <- regularPositions.zipWithIndex) {
      val prefix = proof.substring(0, m.start).trim
      if (prefix.nonEmpty) {
        val stepResult = executeStep(view, command, prefix)
        stepResult match {
          case Right(result)
              if result.stateText.trim.nonEmpty
                && !result.stateText.contains("PROOF_COMPLETE")
                && !result.stateText.contains("No subgoals") =>
            subgoals += s"Sorry ${unfilledPositions.length + idx + 1}:\n${result.stateText.trim}"
          case _ =>
        }
      }
    }

    subgoals.mkString("\n\n")
  }

  // --- Main entry point ---

  /** Main entry point. Called from a background thread. */
  def run(
      view: View,
      command: Command,
      commandText: String,
      initialGoalState: String
  ): Unit = {
    val startTime = System.currentTimeMillis()
    val deadline = startTime + AssistantOptions.getProveTimeout
    AssistantDockable.setStatus("Proving...")
    chat(
      s"**Auto-prove** starting (branches=$numBranches, max fills=$maxFillAttempts, timeout=${AssistantOptions.getProveTimeout / 1000}s)"
    )

    // Get structured goal analysis from PIDE markup
    val goalAnalysis = analyzeGoalAtCursor(view)
    val freeVars = goalAnalysis.map(_.freeVars).getOrElse(Nil)
    if (freeVars.nonEmpty)
      Output.writeln(
        s"[Assistant] Free variables from PIDE: ${freeVars.mkString(", ")}"
      )

    // Fetch context: local facts + definitions + relevant theorems for goal terms
    val context =
      fetchRichContext(view, command, initialGoalState, goalAnalysis)
    if (context.nonEmpty)
      chat(s"Fetched ${context.linesIterator.size} lines of context")

    // Proof planning phase: analyze goal, available lemmas, and produce informal plan
    val plan = createProofPlan(commandText, initialGoalState, context)
    if (plan.nonEmpty) chat(s"## Proof Plan\n$plan")

    // Phase 0: Try simple one-liner methods
    val phase0Analysis = goalAnalysis.getOrElse(
      GoalExtractor.GoalAnalysis(initialGoalState, Nil, Nil, 1)
    )
    trySimpleMethods(view, command, phase0Analysis) match {
      case Some(proof) =>
        val elapsed = (System.currentTimeMillis() - startTime) / 1000
        reportResult(
          view,
          Some(proof),
          s"complete in ${elapsed}s (simple method)",
          commandText
        )
        return
      case None =>
    }

    if (
      AssistantDockable.isCancelled || System.currentTimeMillis() > deadline
    ) {
      reportResult(view, None, "cancelled or timed out", commandText)
      return
    }

    // Phase 1: Skeleton (guided by proof plan)
    val skeleton = sketchPhase(
      view,
      command,
      commandText,
      initialGoalState,
      context,
      plan,
      deadline
    )
    if (
      skeleton.isEmpty || AssistantDockable.isCancelled || System
        .currentTimeMillis() > deadline
    ) {
      val reason =
        if (System.currentTimeMillis() > deadline) "overall timeout exceeded"
        else "no valid skeleton generated"
      reportResult(view, None, reason, commandText)
      return
    }

    // Phase 2: Fill sorries (guided by proof plan)
    val finalProof = fillPhase(
      view,
      command,
      commandText,
      skeleton.get,
      context,
      plan,
      deadline
    )
    val openSorries = countSorries(finalProof)
    val unfilled = countUnfilled(finalProof)
    val totalRemaining = openSorries + unfilled
    val elapsed = (System.currentTimeMillis() - startTime) / 1000

    if (totalRemaining == 0) {
      chat("**Proof complete — all sorries filled!**")
      reportResult(
        view,
        Some(finalProof),
        s"complete in ${elapsed}s",
        commandText
      )
    } else {
      chat(s"## Result\n$totalRemaining sorry${
          if (totalRemaining != 1) "s" else ""
        } could not be filled")
      // Diagnose unfilled obligations — collect actual subgoals at each sorry position
      if (!AssistantDockable.isCancelled) {
        chat("## Diagnosis\nAnalyzing unfilled obligations...")
        try {
          // Get subgoals at each unfilled sorry by executing prefixes
          val subgoals = collectUnfilledSubgoals(view, command, finalProof)
          val subs = Map(
            "command" -> commandText,
            "proof" -> finalProof,
            "num_sorries" -> totalRemaining.toString
          ) ++ (if (totalRemaining != 1) Map("plural" -> "true")
                else Map.empty) ++
            (if (subgoals.nonEmpty) Map("subgoals" -> subgoals)
             else Map.empty) ++
            (if (context.nonEmpty) Map("context" -> context) else Map.empty)
          chat(
            BedrockClient.invokeNoCache(
              PromptLoader.load("prove_diagnose.md", subs)
            )
          )
        } catch {
          case ex: Exception => ErrorHandler.logSilentError("ProofLoop", ex)
        }
      }
      reportResult(
        view,
        Some(finalProof),
        s"$totalRemaining unfilled sorries, ${elapsed}s",
        commandText
      )
    }
  }

  /** Report the final proof result to the user with appropriate badge and
    * insert link. Dispatches to GUI thread for all UI updates.
    */
  private def reportResult(
      view: View,
      proof: Option[String],
      reason: String,
      commandText: String
  ): Unit = {
    GUI_Thread.later {
      val totalRemaining =
        proof.map(p => countSorries(p) + countUnfilled(p)).getOrElse(1)
      proof match {
        case Some(code) if totalRemaining == 0 =>
          AssistantDockable.respondInChat(
            s"[ok] **Proof found** ($reason):",
            Some((code, InsertHelper.createInsertAction(view, code)))
          )
          AssistantDockable.setBadge(VerificationBadge.Verified(None))
        case Some(code) =>
          AssistantDockable.respondInChat(
            s"**Partial proof** ($reason):",
            Some((code, InsertHelper.createInsertAction(view, code)))
          )
          AssistantDockable.setBadge(VerificationBadge.Failed(reason.take(30)))
        case None =>
          AssistantDockable.respondInChat(s"No proof found: $reason")
          AssistantDockable.setBadge(VerificationBadge.Failed(reason.take(30)))
      }
      AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
    }
  }
}
