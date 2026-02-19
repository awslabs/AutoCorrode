/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.util.concurrent.CountDownLatch
import java.util.concurrent.TimeUnit
import scala.jdk.CollectionConverters._

/** Central command dispatcher and chat history manager for the Assistant
  * dockable. Handles 30+ colon-prefixed commands (`:help`, `:suggest`, etc.)
  * and free-form LLM chat. Maintains conversation history with size limits.
  *
  * The dispatch table is the single source of truth for both command execution
  * and help text, preventing drift between the two.
  */
object ChatAction {
  enum ChatRole(val wireValue: String) {
    case User extends ChatRole("user")
    case Assistant extends ChatRole("assistant")
    case Tool extends ChatRole("tool")
    case Widget extends ChatRole("widget")
  }
  object ChatRole {
    def fromWire(value: String): Option[ChatRole] = value match {
      case "user"      => Some(User)
      case "assistant" => Some(Assistant)
      case "tool"      => Some(Tool)
      case "widget"    => Some(Widget)
      case _           => None
    }
  }
  export ChatRole._

  case class Message(
      role: ChatRole,
      content: String,
      timestamp: LocalDateTime,
      rawHtml: Boolean = false,
      transient: Boolean = false
  )

  // Bounded history using immutable List with lock for thread-safety
  private val maxHistory = AssistantConstants.MAX_ACCUMULATED_MESSAGES
  private val historyLock = new Object()
  @volatile private var history: List[Message] = Nil
  private val timeFmt = DateTimeFormatter.ofPattern("HH:mm")

  /** Command dispatch entry: description for help, handler function, whether
    * I/Q is required.
    */
  private case class CommandEntry(
      description: String,
      handler: (View, String) => Unit,
      needsIQ: Boolean = false
  )

  /** Expose command names for auto-completion. */
  def commandNames: List[String] = dispatch.keys.toList

  /** Single dispatch table — source of truth for both execution and help. */
  private lazy val dispatch: Map[String, CommandEntry] = Map(
    "analyze" -> CommandEntry(
      "Analyze proof patterns and suggest improvements for proof structure",
      (v, _) => AnalyzePatternsAction.analyze(v)
    ),
    "deps" -> CommandEntry(
      "Display theory dependencies and imports for a specified theory file",
      (v, a) => TheoryBrowserAction.deps(v, a)
    ),
    "explain" -> CommandEntry(
      "Provide detailed explanation of Isabelle code at specified location",
      (v, a) => runExplain(v, a)
    ),
    "explain-counterexample" -> CommandEntry(
      "Explain why a counterexample was generated and what it means",
      (v, _) => ExplainCounterexampleAction.chatCommand(v)
    ),
    "explain-error" -> CommandEntry(
      "Analyze and explain error messages at the current cursor position",
      (v, _) => runExplainError(v)
    ),
    "extract" -> CommandEntry(
      "Extract selected proof text into a separate reusable lemma",
      (v, _) => ExtractLemmaAction.chatExtract(v)
    ),
    "find" -> CommandEntry(
      "Search for theorems matching a given pattern or keyword",
      (v, a) => runFind(v, a),
      needsIQ = true
    ),
    "generate-doc" -> CommandEntry(
      "Generate documentation for definitions and theorems",
      (v, _) => GenerateDocAction.chatGenerate(v)
    ),
    "generate-elim" -> CommandEntry(
      "Generate elimination rules for datatypes and definitions",
      (v, _) => GenerateRulesAction.chatGenerateElim(v)
    ),
    "generate-intro" -> CommandEntry(
      "Generate introduction rules for datatypes and definitions",
      (v, _) => GenerateRulesAction.chatGenerateIntro(v)
    ),
    "generate-tests" -> CommandEntry(
      "Generate test cases and examples for definitions",
      (v, _) => GenerateTestsAction.chatGenerate(v)
    ),
    "help" -> CommandEntry(
      "Display this table of available commands and their descriptions",
      (_, _) => showHelp()
    ),
    "models" -> CommandEntry(
      "Refresh the list of available AI models from AWS Bedrock",
      (_, _) => runModels()
    ),
    "nitpick" -> CommandEntry(
      "Run Nitpick model finder to search for counterexamples",
      (v, _) =>
        CounterexampleFinderAction.run(v, CounterexampleFinderAction.Nitpick),
      needsIQ = true
    ),
    "print-context" -> CommandEntry(
      "Display current proof context including assumptions and goals",
      (v, _) => PrintContextAction.run(v),
      needsIQ = true
    ),
    "prove" -> CommandEntry(
      "Automatically prove the goal at cursor using LLM-guided proof search",
      (v, _) => runProve(v),
      needsIQ = true
    ),
    "quickcheck" -> CommandEntry(
      "Run QuickCheck to test conjectures with random examples",
      (v, _) =>
        CounterexampleFinderAction
          .run(v, CounterexampleFinderAction.Quickcheck),
      needsIQ = true
    ),
    "read" -> CommandEntry(
      "Display the content of a specified theory file (optional: line count)",
      (v, a) => TheoryBrowserAction.read(v, a)
    ),
    "refactor" -> CommandEntry(
      "Convert proof text to structured Isar proof style",
      (v, _) => RefactorAction.chatRefactor(v)
    ),
    "search" -> CommandEntry(
      "Search for specific text patterns within a theory file",
      (v, a) => TheoryBrowserAction.search(v, a)
    ),
    "set" -> CommandEntry(
      "View or modify Assistant configuration settings",
      (_, a) => runSet(a)
    ),
    "show-type" -> CommandEntry(
      "Display type information for the symbol at cursor position",
      (v, _) => ShowTypeAction.showType(v)
    ),
    "sledgehammer" -> CommandEntry(
      "Run Sledgehammer to find automatic proofs using external provers",
      (v, _) => runSledgehammer(v),
      needsIQ = true
    ),
    "suggest" -> CommandEntry(
      "Generate proof step suggestions for the current proof state",
      (v, a) => runSuggest(v, a)
    ),
    "suggest-name" -> CommandEntry(
      "Suggest a descriptive name for the lemma, theorem, or definition at cursor",
      (v, _) => SuggestNameAction.chatSuggestName(v)
    ),
    "suggest-strategy" -> CommandEntry(
      "Recommend high-level proof strategies for the current goal",
      (v, _) => SuggestStrategyAction.suggest(v)
    ),
    "suggest-tactic" -> CommandEntry(
      "Suggest specific tactics to apply at the current proof step",
      (v, _) => SuggestTacticAction.chatSuggest(v)
    ),
    "summarize" -> CommandEntry(
      "Generate a summary of theory content including key definitions",
      (v, _) => SummarizeTheoryAction.summarize(v)
    ),
    "theories" -> CommandEntry(
      "List all currently loaded theory files in the session",
      (_, _) => TheoryBrowserAction.theories()
    ),
    "tidy" -> CommandEntry(
      "Clean up and format proof text for better readability",
      (v, _) => TidyAction.tidy(v)
    ),
    "trace" -> CommandEntry(
      "Trace simplifier operations to understand rewriting steps",
      (v, _) => TraceSimplifierAction.trace(v),
      needsIQ = true
    ),
    "try-methods" -> CommandEntry(
      "Attempt various proof methods automatically on current goal",
      (v, _) => TryMethodsAction.run(v),
      needsIQ = true
    ),
    "verify" -> CommandEntry(
      "Verify that a given proof text is correct and complete",
      (v, a) => runVerify(v, a),
      needsIQ = true
    )
  )

  def addMessage(message: Message): Unit = historyLock.synchronized {
    history = (history :+ message).takeRight(maxHistory)
  }

  def addMessage(role: ChatRole, content: String): Unit =
    addMessage(Message(role, content, LocalDateTime.now()))

  def clearHistory(): Unit = historyLock.synchronized {
    history = Nil
  }

  /** Get the current history as an immutable snapshot. Thread-safe. */
  def getHistory: List[Message] = history

  /** Get an atomic snapshot of the current history. This method name makes it
    * explicit that we're taking a consistent view.
    */
  def getHistorySnapshot: List[Message] = history

  def formatTime(ts: LocalDateTime): String = ts.format(timeFmt)

  /** Start a chat conversation with the LLM.
    *
    * @param view
    *   The current jEdit view
    * @param userMessage
    *   The user's message
    */
  def chat(view: View, userMessage: String): Unit = {
    AssistantDockable.resetCancel()
    if (userMessage.startsWith(":")) {
      handleCommand(view, userMessage)
    } else {
      val context = getContext(view)
      val systemPromptOpt = try {
        Some(
          PromptLoader.load(
            "chat_system.md",
            if (context.nonEmpty) Map("context" -> context) else Map.empty
          )
        )
      } catch {
        case ex: Exception =>
          GUI.error_dialog(
            view,
            "Isabelle Assistant",
            s"Failed to load prompt: ${ex.getMessage}"
          )
          None
      }

      systemPromptOpt.foreach { systemPrompt =>
        addMessage(Message(User, userMessage, LocalDateTime.now()))
        AssistantDockable.showConversation(getHistory)
        AssistantDockable.setStatus(AssistantConstants.STATUS_THINKING)

        val messagesForApi = getHistory
          .filterNot(_.transient)
          .map(m => (m.role.wireValue, m.content))

        Isabelle_Thread.fork(name = "assistant-chat") {
          try {
            BedrockClient.setCurrentView(view)
            val response =
              BedrockClient.invokeChat(systemPrompt, messagesForApi)
            GUI_Thread.later {
              addMessage(Message(Assistant, response, LocalDateTime.now()))
              AssistantDockable.showConversation(getHistory)
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            }
          } catch {
            case ex: Exception =>
              GUI_Thread.later {
                val errorMsg =
                  ErrorHandler.makeUserFriendly(ex.getMessage, "chat")
                AssistantDockable.setStatus(s"Error: $errorMsg")

                val retryAction = () => {
                  AssistantDockable.setStatus("Retrying...")
                  retryChatInternal(view, systemPrompt, messagesForApi)
                }
                val retryId = AssistantDockable.registerAction(retryAction)
                ChatAction.addMessage(
                  Assistant,
                  s"Error: $errorMsg\n\n{{ACTION:$retryId:Retry}}"
                )
                AssistantDockable.showConversation(ChatAction.getHistory)
              }
          }
        }
      }
    }
  }

  /** Retry a chat without re-adding the user message to history. */
  private def retryChatInternal(
      view: View,
      systemPrompt: String,
      messagesForApi: List[(String, String)]
  ): Unit = {
    Isabelle_Thread.fork(name = "assistant-chat-retry") {
      try {
        BedrockClient.setCurrentView(view)
        val response = BedrockClient.invokeChat(systemPrompt, messagesForApi)
        GUI_Thread.later {
          addMessage(Message(Assistant, response, LocalDateTime.now()))
          AssistantDockable.showConversation(getHistory)
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            val errorMsg = ErrorHandler.makeUserFriendly(ex.getMessage, "chat")
            AssistantDockable.setStatus(s"Error: $errorMsg")
            addResponse(s"Error: $errorMsg")
          }
      }
    }
  }

  private def handleCommand(view: View, input: String): Unit = {
    val parts = input.drop(1).split("\\s+", 2)
    val cmd = parts(0).toLowerCase
    val arg = if (parts.length > 1) parts(1) else ""

    addMessage(Message(User, input, LocalDateTime.now()))
    AssistantDockable.showConversation(getHistory)

    dispatch.get(cmd) match {
      case Some(entry) if entry.needsIQ && !IQAvailable.isAvailable =>
        addResponse(
          "I/Q plugin not available. Install I/Q to use this command."
        )
      case Some(entry) => entry.handler(view, arg)
      case None        =>
        addResponse(
          s"Unknown command `:$cmd`. Type `:help` for available commands."
        )
    }
  }

  private def showHelp(): Unit = {
    val headerBg = UIColors.HelpTable.headerBackground
    val borderColor = UIColors.HelpTable.borderColor
    val rowBorder = UIColors.HelpTable.rowBorder
    val accentColor = UIColors.HelpTable.accentColor
    val infoBg = UIColors.InfoBox.background
    val infoBorder = UIColors.InfoBox.border

    val sortedCommands = dispatch.toList.sortBy(_._1)
    val header =
      s"<tr><th style='padding:4px 8px;border-bottom:2px solid $borderColor;text-align:left;font-size:11pt;background:$headerBg;'>Command</th><th style='padding:4px 8px;border-bottom:2px solid $borderColor;text-align:left;font-size:11pt;background:$headerBg;'>Description</th><th style='padding:4px 8px;border-bottom:2px solid $borderColor;text-align:center;font-size:11pt;background:$headerBg;'>I/Q</th></tr>"
    val rows = sortedCommands.map { case (cmd, entry) =>
      val iq = if (entry.needsIQ) "yes" else ""
      s"<tr><td style='padding:4px 8px;border-bottom:1px solid $rowBorder;font-family:${MarkdownRenderer.codeFont};font-size:11pt;white-space:nowrap;color:$accentColor;'>:$cmd</td><td style='padding:4px 8px;border-bottom:1px solid $rowBorder;font-size:11pt;'>${entry.description}</td><td style='padding:4px 8px;border-bottom:1px solid $rowBorder;font-size:11pt;text-align:center;'>$iq</td></tr>"
    }.mkString
    val table =
      s"<table style='width:100%;border-collapse:collapse;'>$header$rows</table>"
    val targetHelp =
      s"""<div style='margin-top:10px;padding:8px 10px;background:$infoBg;border:1px solid $infoBorder;border-radius:3px;'>
      |<div style='font-weight:bold;margin-bottom:4px;'>Target Syntax</div>
      |<div style='font-size:11pt;'>Commands like <code>:explain</code> and <code>:suggest</code> accept optional targets:</div>
      |<div style='font-size:11pt;padding-left:12px;margin-top:4px;'>
      |• <code>cursor</code> — current cursor position (default)<br/>
      |• <code>selection</code> — current text selection<br/>
      |• <code>Theory.thy:42</code> — specific line<br/>
      |• <code>Theory.thy:10-20</code> — line range<br/>
      |• <code>Theory.thy:lemma_name</code> — named element<br/>
      |• <code>cursor+5</code>, <code>cursor-3</code> — relative offset
      |</div></div>""".stripMargin
    addMessage(
      Message(
        Assistant,
        table + targetHelp,
        LocalDateTime.now(),
        rawHtml = true
      )
    )
    AssistantDockable.showConversation(getHistory)
  }

  private def runModels(): Unit = {
    AssistantDockable.setStatus("Refreshing models...")

    Isabelle_Thread.fork(name = "chat-models") {
      try {
        val region = AssistantOptions.getRegion
        val models = BedrockModels.refreshModels(region)
        GUI_Thread.later {
          val modelList = models.map(m => s"* `$m`").mkString("\n")
          addResponse(
            s"**Available Models** (${models.length} total)\n\n$modelList"
          )
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            addResponse(s"Error refreshing models: ${ex.getMessage}")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
      }
    }
  }

  private def runSet(arg: String): Unit = {
    import org.gjt.sp.jedit.jEdit
    val parts = arg.trim.split("\\s+", 2)

    if (arg.trim.isEmpty) {
      addResponse(s"**Current Settings**\n\n${AssistantOptions.listSettings}")
    } else if (parts.length == 1) {
      AssistantOptions.getSetting(parts(0)) match {
        case Some(value) => addResponse(s"`${parts(0)}` = `$value`")
        case None        =>
          addResponse(
            s"Unknown setting: `${parts(0)}`. Type `:set` to see all settings."
          )
      }
    } else {
      AssistantOptions.setSetting(parts(0), parts(1)) match {
        case Some(msg) =>
          if (parts(0).toLowerCase == "model")
            AssistantDockable.refreshModelLabel()
          addResponse(msg)
        case None =>
          addResponse(
            s"Unknown setting: `${parts(0)}`. Type `:set` to see all settings."
          )
      }
    }
  }

  private def runExplain(view: View, targetSpec: String): Unit = {
    val targetOpt =
      if (targetSpec.trim.isEmpty) Some(TargetParser.CurrentCursor)
      else {
        TargetParser.parseTarget(targetSpec, view) match {
          case Some(target) => Some(target)
          case None         =>
            addResponse(
              s"Invalid target: $targetSpec. Use 'cursor', 'selection', or 'Theory.thy:line'"
            )
            None
        }
      }

    targetOpt.foreach { target =>
      TargetParser.resolveTarget(target, view) match {
        case Some((buffer, start, end)) =>
          val textOpt = if (start == end) {
            CommandExtractor.getCommandAtOffset(buffer, start) match {
              case Some(text) => Some(text)
              case None       =>
                addResponse("No command found at target location")
                None
            }
          } else {
            Some(buffer.getText(start, end - start))
          }

          textOpt.foreach { text =>
            ActionHelper.runAndRespond("chat-explain", "Explaining code...") {
              val context = ContextFetcher.getContext(view, 3000)
              val subs = Map("theorem" -> text) ++
                context.map(c => Map("context" -> c)).getOrElse(Map.empty)
              val prompt = PromptLoader.load("explain_with_context.md", subs)
              BedrockClient.invokeInContext(prompt)
            }
          }
        case None =>
          addResponse(
            s"Could not resolve target: ${TargetParser.formatTarget(target)}"
          )
      }
    }
  }

  private def runSuggest(view: View, targetSpec: String): Unit = {
    val targetOpt =
      if (targetSpec.trim.isEmpty) Some(TargetParser.CurrentCursor)
      else {
        TargetParser.parseTarget(targetSpec, view) match {
          case Some(target) => Some(target)
          case None         =>
            addResponse(
              s"Invalid target: $targetSpec. Use 'cursor', 'selection', or 'Theory.thy:line'"
            )
            None
        }
      }

    targetOpt.foreach { target =>
      TargetParser.resolveTarget(target, view) match {
        case Some((buffer, offset, _)) =>
          AssistantDockable.setStatus("Generating suggestions...")
          Isabelle_Thread.fork(name = "chat-suggest") {
            try {
              SuggestAction.suggestFromChat(view, buffer, offset)
              GUI_Thread.later {
                AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
              }
            } catch {
              case ex: Exception =>
                GUI_Thread.later {
                  addResponse(s"Error: ${ex.getMessage}")
                  AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                }
            }
          }
        case None =>
          addResponse(
            s"Could not resolve target: ${TargetParser.formatTarget(target)}"
          )
      }
    }
  }

  private def runExplainError(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val error = ExplainErrorAction.extractErrorAtOffset(buffer, offset)

    if (error.isEmpty) {
      addResponse("No error at cursor position.")
    } else {
      val context =
        CommandExtractor.getCommandAtOffset(buffer, offset).getOrElse("")
      val goalState = GoalExtractor.getGoalState(buffer, offset)

      ActionHelper.runAndRespond("chat-explain-error", "Explaining error...") {
        val subs = Map(
          "error" -> error.get,
          "context" -> context
        ) ++ goalState.map(g => Map("goal_state" -> g)).getOrElse(Map.empty)

        val prompt = PromptLoader.load("explain_error.md", subs)
        BedrockClient.invokeInContext(prompt)
      }
    }
  }

  private def runProve(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
    val goalState = GoalExtractor.getGoalState(buffer, offset)
    val commandText = CommandExtractor.getCommandAtOffset(buffer, offset)

    (commandOpt, goalState, commandText) match {
      case (None, _, _) =>
        addResponse("No Isabelle command at cursor position.")
      case (_, None, _) =>
        addResponse(
          "No goal state at cursor position. Place cursor inside a proof."
        )
      case (_, _, None) => addResponse("No command text at cursor position.")
      case (Some(command), Some(goal), Some(cmdText)) =>
        AssistantDockable.setStatus("Proving...")
        Isabelle_Thread.fork(name = "assistant-prove") {
          ProofLoop.run(view, command, cmdText, goal)
        }
    }
  }

  private def runVerify(view: View, proof: String): Unit = {
    if (proof.trim.isEmpty)
      addResponse("Usage: `:verify <proof>`\n\nExample: `:verify by simp`")
    else {
      val buffer = view.getBuffer
      val offset = view.getTextArea.getCaretPosition
      IQIntegration.getCommandAtOffset(buffer, offset) match {
        case None => addResponse("No Isabelle command at cursor position.")
        case Some(command) =>
          AssistantDockable.setStatus(AssistantConstants.STATUS_VERIFYING)
          val timeout = AssistantOptions.getVerificationTimeout
          val latch = new CountDownLatch(1)
          @volatile var result: String = ""

          GUI_Thread.later {
            IQIntegration.verifyProofAsync(
              view,
              command,
              proof,
              timeout,
              {
                case IQIntegration.ProofSuccess(timeMs, _) =>
                  result = s"[ok] Proof verified successfully (${timeMs}ms)"
                  latch.countDown()
                case IQIntegration.ProofFailure(error) =>
                  result = s"[FAIL] Verification failed: $error"
                  latch.countDown()
                case IQIntegration.ProofTimeout =>
                  result = "[FAIL] Verification timed out"
                  latch.countDown()
                case _ =>
                  result = "[FAIL] Verification unavailable"
                  latch.countDown()
              }
            )
          }

          Isabelle_Thread.fork(name = "chat-verify") {
            latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
            val finalResult =
              if (result.isEmpty) "[FAIL] Verification timed out (no response)"
              else result
            GUI_Thread.later {
              addResponse(finalResult)
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            }
            // On failure, diagnose using LLM
            if (finalResult.startsWith("[FAIL]")) {
              val error = finalResult
                .stripPrefix("[FAIL] Verification failed: ")
                .stripPrefix("[FAIL] ")
              val goalState = GoalExtractor.getGoalState(buffer, offset)
              val context = CommandExtractor.getCommandAtOffset(buffer, offset)
              try {
                val subs = Map("proof" -> proof, "error" -> error) ++
                  goalState
                    .map(g => Map("goal_state" -> g))
                    .getOrElse(Map.empty) ++
                  context.map(c => Map("context" -> c)).getOrElse(Map.empty)
                val diagPrompt =
                  PromptLoader.load("diagnose_verification.md", subs)
                // Use invokeNoCache (stateless) to avoid polluting chat history
                val diagnosis = BedrockClient.invokeNoCache(diagPrompt)
                GUI_Thread.later { addResponse(diagnosis) }
              } catch {
                case ex: Exception =>
                  Output.writeln(
                    s"[Assistant] Post-verification diagnosis failed: ${ex.getMessage}"
                  )
              }
            }
          }
      }
    }
  }

  private def runSledgehammer(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    IQIntegration.getCommandAtOffset(buffer, offset) match {
      case None => addResponse("No Isabelle command at cursor position.")
      case Some(command) =>
        AssistantDockable.setStatus("Running sledgehammer...")
        val timeout = AssistantOptions.getSledgehammerTimeout

        GUI_Thread.later {
          IQIntegration.runSledgehammerAsync(
            view,
            command,
            timeout,
            {
              case Right(results) if results.nonEmpty =>
                GUI_Thread.later {
                  val lines = results
                    .map(r =>
                      s"[sledgehammer] `${r.proofMethod}` (${r.timeMs}ms)"
                    )
                    .mkString("\n\n")
                  addResponse(
                    s"**Sledgehammer found ${results.length} proofs:**\n\n$lines"
                  )
                  AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                }
              case Right(_) =>
                GUI_Thread.later {
                  addResponse("Sledgehammer found no proofs.")
                  AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                }
              case Left(error) =>
                GUI_Thread.later {
                  addResponse(s"Sledgehammer error: $error")
                  AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                }
            }
          )
        }
    }
  }

  private def runFind(view: View, pattern: String): Unit = {
    if (pattern.trim.isEmpty)
      addResponse(
        "Usage: `:find <pattern>`\n\nExample: `:find \"_ + _ = _ + _\"`"
      )
    else {
      val buffer = view.getBuffer
      val offset = view.getTextArea.getCaretPosition
      IQIntegration.getCommandAtOffset(buffer, offset) match {
        case None => addResponse("No Isabelle command at cursor position.")
        case Some(command) =>
          AssistantDockable.setStatus("Searching theorems...")
          val limit = AssistantOptions.getFindTheoremsLimit
          val timeout = AssistantOptions.getFindTheoremsTimeout
          val quotedPattern =
            if (pattern.startsWith("\"")) pattern else s"\"$pattern\""

          GUI_Thread.later {
            IQIntegration.runFindTheoremsAsync(
              view,
              command,
              quotedPattern,
              limit,
              timeout,
              {
                case Right(results) if results.nonEmpty =>
                  GUI_Thread.later {
                    val lines = results.map(r => s"* $r").mkString("\n\n")
                    addResponse(
                      s"**Found ${results.length} theorems:**\n\n$lines"
                    )
                    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                  }
                case Right(_) =>
                  GUI_Thread.later {
                    addResponse(s"No theorems found matching: $pattern")
                    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                  }
                case Left(error) =>
                  GUI_Thread.later {
                    addResponse(s"Find theorems error: $error")
                    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                  }
              }
            )
          }
      }
    }
  }

  def addResponse(content: String): Unit = {
    addMessage(Message(Assistant, content, LocalDateTime.now()))
    AssistantDockable.showConversation(getHistory)
  }

  /** Add a display-only message that appears in chat but is NOT sent to the
    * LLM.
    */
  def addTransient(content: String): Unit = {
    addMessage(
      Message(Assistant, content, LocalDateTime.now(), transient = true)
    )
    AssistantDockable.showConversation(getHistory)
  }

  /** Add a tool-use message showing which tool is being called with what
    * parameters. Format: "toolName|||{json params}" - transient so it doesn't
    * get sent to LLM.
    */
  def addToolMessage(
      toolName: String,
      params: ResponseParser.ToolArgs
  ): Unit = {
    val jsonParams = ResponseParser.toolArgsToJson(params)
    val content = s"$toolName|||$jsonParams"
    addMessage(Message(Tool, content, LocalDateTime.now(), transient = true))
    AssistantDockable.showConversation(getHistory)
  }

  private def getContext(view: View): String = {
    val textArea = view.getTextArea
    val selected = Option(textArea.getSelectedText).filter(_.trim.nonEmpty)
    selected.getOrElse {
      CommandExtractor
        .getCommandAtOffset(view.getBuffer, textArea.getCaretPosition)
        .getOrElse("")
    }
  }
}
