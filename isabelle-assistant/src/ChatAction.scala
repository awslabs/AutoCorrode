/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter

/** Central command dispatcher and chat history manager for the Assistant
  * dockable. Handles 30+ colon-prefixed commands (`:help`, `:suggest`, etc.)
  * and free-form LLM chat. Maintains conversation history with size limits.
  *
  * The dispatch table is the single source of truth for both command execution
  * and help text, preventing drift between the two.
  */
object ChatAction {
  private final case class ChatContextSeed(
      selectedText: Option[String],
      path: Option[String],
      caretOffset: Int
  )

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

  /** Semantic tag for an assistant message. The renderer uses this to pick
    * bubble chrome (colour, icon) instead of sniffing for `Error:` / `[FAIL]`
    * string prefixes in content. `Normal` is the default for free-form
    * assistant text. `Error` / `Success` / `Info` are used by the typed
    * wrappers (`addErrorResponse`, etc.). `Summary` marks the transient
    * notice that auto-summarisation produced. */
  enum ResponseKind {
    case Normal, Error, Success, Info, Summary
  }

  case class Message(
      role: ChatRole,
      content: String,
      timestamp: LocalDateTime,
      rawHtml: Boolean = false,
      transient: Boolean = false,
      kind: ResponseKind = ResponseKind.Normal
  )

  // Bounded history backed by ArrayDeque; all reads/writes serialized by
  // historyLock. getHistory publishes a snapshot so callers iterate safely.
  private val maxHistory = AssistantConstants.MAX_ACCUMULATED_MESSAGES
  private val historyLock = new Object()
  private val history: java.util.ArrayDeque[Message] =
    new java.util.ArrayDeque[Message](maxHistory)
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
  def commandNames: List[String] =
    dispatch.keysIterator.map(_.wireName).toList.sorted

  /** Single dispatch table — source of truth for both execution and help. */
  private lazy val dispatch: Map[CommandId, CommandEntry] = Map(
    CommandId.Analyze -> CommandEntry(
      "Analyze proof patterns and suggest improvements for proof structure",
      (v, _) => AnalyzePatternsAction.analyze(v)
    ),
    CommandId.Deps -> CommandEntry(
      "Display theory dependencies and imports for a specified theory file",
      (v, a) => TheoryBrowserAction.deps(v, a)
    ),
    CommandId.Explain -> CommandEntry(
      "Provide detailed explanation of Isabelle code at specified location",
      (v, a) => runExplain(v, a)
    ),
    CommandId.ExplainCounterexample -> CommandEntry(
      "Explain why a counterexample was generated and what it means",
      (v, _) => ExplainCounterexampleAction.chatCommand(v)
    ),
    CommandId.ExplainError -> CommandEntry(
      "Analyze and explain error messages at the current cursor position",
      (v, _) => runExplainError(v)
    ),
    CommandId.Extract -> CommandEntry(
      "Extract selected proof text into a separate reusable lemma",
      (v, _) => ExtractLemmaAction.chatExtract(v)
    ),
    CommandId.Find -> CommandEntry(
      "Search for theorems matching a given pattern or keyword",
      (v, a) => runFind(v, a),
      needsIQ = true
    ),
    CommandId.GenerateDoc -> CommandEntry(
      "Generate documentation for definitions and theorems",
      (v, _) => GenerateDocAction.chatGenerate(v)
    ),
    CommandId.GenerateElim -> CommandEntry(
      "Generate elimination rules for datatypes and definitions",
      (v, _) => GenerateRulesAction.chatGenerateElim(v)
    ),
    CommandId.GenerateIntro -> CommandEntry(
      "Generate introduction rules for datatypes and definitions",
      (v, _) => GenerateRulesAction.chatGenerateIntro(v)
    ),
    CommandId.GenerateTests -> CommandEntry(
      "Generate test cases and examples for definitions",
      (v, _) => GenerateTestsAction.chatGenerate(v)
    ),
    CommandId.Help -> CommandEntry(
      "Display this table of available commands and their descriptions",
      (_, a) => showHelp(a.trim)
    ),
    CommandId.Models -> CommandEntry(
      "Refresh the list of available Anthropic models from AWS Bedrock",
      (_, _) => runModels()
    ),
    CommandId.Nitpick -> CommandEntry(
      "Run Nitpick model finder to search for counterexamples",
      (v, _) =>
        CounterexampleFinderAction.run(v, CounterexampleFinderAction.Nitpick),
      needsIQ = true
    ),
    CommandId.PrintContext -> CommandEntry(
      "Display current proof context including assumptions and goals",
      (v, _) => PrintContextAction.run(v),
      needsIQ = true
    ),
    CommandId.Quickcheck -> CommandEntry(
      "Run QuickCheck to test conjectures with random examples",
      (v, _) =>
        CounterexampleFinderAction
          .run(v, CounterexampleFinderAction.Quickcheck),
      needsIQ = true
    ),
    CommandId.Read -> CommandEntry(
      "Display the content of a specified theory file (optional: line count)",
      (v, a) => TheoryBrowserAction.read(v, a)
    ),
    CommandId.Refactor -> CommandEntry(
      "Convert proof text to structured Isar proof style",
      (v, _) => RefactorAction.chatRefactor(v)
    ),
    CommandId.Search -> CommandEntry(
      "Search for specific text patterns within a theory file",
      (v, a) => TheoryBrowserAction.search(v, a)
    ),
    CommandId.Set -> CommandEntry(
      "View or modify Assistant configuration settings",
      (_, a) => runSet(a)
    ),
    CommandId.ShowType -> CommandEntry(
      "Display type information for the symbol at cursor position",
      (v, _) => ShowTypeAction.showType(v)
    ),
    CommandId.Sledgehammer -> CommandEntry(
      "Run Sledgehammer to find automatic proofs using external provers",
      (v, _) => runSledgehammer(v),
      needsIQ = true
    ),
    CommandId.Suggest -> CommandEntry(
      "Generate proof step suggestions for the current proof state",
      (v, a) => runSuggest(v, a)
    ),
    CommandId.SuggestName -> CommandEntry(
      "Suggest a descriptive name for the lemma, theorem, or definition at cursor",
      (v, _) => SuggestNameAction.chatSuggestName(v)
    ),
    CommandId.SuggestStrategy -> CommandEntry(
      "Recommend high-level proof strategies for the current goal",
      (v, _) => SuggestStrategyAction.suggest(v)
    ),
    CommandId.SuggestTactic -> CommandEntry(
      "Suggest specific tactics to apply at the current proof step",
      (v, _) => SuggestTacticAction.chatSuggest(v)
    ),
    CommandId.Summarize -> CommandEntry(
      "Generate a summary of theory content including key definitions",
      (v, _) => SummarizeTheoryAction.summarize(v)
    ),
    CommandId.Theories -> CommandEntry(
      "List all currently loaded theory files in the session",
      (_, _) => TheoryBrowserAction.theories()
    ),
    CommandId.Tidy -> CommandEntry(
      "Clean up and format proof text for better readability",
      (v, _) => TidyAction.tidy(v)
    ),
    CommandId.Trace -> CommandEntry(
      "Trace simplifier operations to understand rewriting steps",
      (v, _) => TraceSimplifierAction.trace(v),
      needsIQ = true
    ),
    CommandId.TryMethods -> CommandEntry(
      "Attempt various proof methods automatically on current goal",
      (v, _) => TryMethodsAction.run(v),
      needsIQ = true
    ),
    CommandId.Verify -> CommandEntry(
      "Verify that a given proof text is correct and complete",
      (v, a) => runVerify(v, a),
      needsIQ = true
    ),
    CommandId.Version -> CommandEntry(
      "Show the Isabelle Assistant plugin name and version",
      (_, _) => runVersion()
    )
  )
  require(
    dispatch.keySet == CommandId.values.toSet,
    "ChatAction dispatch must cover all CommandId values."
  )

  def addMessage(message: Message): Unit = historyLock.synchronized {
    history.addLast(capMessageSize(sanitizeIfRawHtml(message)))
    while (history.size > maxHistory) {
      val _ = history.pollFirst()
    }
  }

  /** Defense-in-depth: rawHtml widget messages bypass MarkdownRenderer's
    * escape path. Widget producers are supposed to escape user/LLM text
    * before interpolation, but a future producer that forgets must not
    * open a JEditorPane injection surface. Strip `<script>`/`<iframe>`
    * elements, `javascript:` URL schemes, and inline event handlers. */
  private def sanitizeIfRawHtml(message: Message): Message =
    if (message.rawHtml && message.content != null)
      message.copy(content = HtmlUtil.sanitizeWidgetHtml(message.content))
    else message

  /** Truncate an individual message's content to `MAX_MESSAGE_SIZE_CHARS`.
    * Count-based history trimming alone is not enough: one pathological
    * message (runaway tool output, huge pasted file) can still blow through
    * any token budget. Truncate in the middle so both the opening context
    * and the final summary remain visible. */
  private def capMessageSize(message: Message): Message = {
    val limit = AssistantConstants.MAX_MESSAGE_SIZE_CHARS
    val content = message.content
    if (content == null || content.length <= limit) message
    else {
      val head = content.substring(0, limit / 2)
      val tail = content.substring(content.length - limit / 2)
      val omitted = content.length - limit
      val truncated = head +
        s"\n\n*— truncated $omitted characters —*\n\n" +
        tail
      message.copy(content = truncated)
    }
  }

  def addMessage(role: ChatRole, content: String): Unit =
    addMessage(Message(role, content, LocalDateTime.now()))

  def clearHistory(): Unit = historyLock.synchronized {
    history.clear()
    ToolPermissions.clearSession()
  }

  /**
   * Atomically replace the entire conversation history with a summary message.
   * Used by ContextSummarizer when context budget is exceeded.
   *
   * @param summaryContent The formatted summary text to use as the new seed message
   */
  def replaceHistoryWithSummary(summaryContent: String): Unit = historyLock.synchronized {
    history.clear()
    history.addLast(Message(Assistant, summaryContent, LocalDateTime.now()))
  }

  /**
   * Add a transient notification that context was summarized.
   * Shows the user that old messages were compressed to save space.
   * The distinguishing chrome (border tint / icon) comes from
   * `ResponseKind.Summary`, so no bracket-tag prefix is needed.
   */
  def addSummarizationNotice(): Unit = {
    val notice = "Context was automatically summarized to stay within limits. Your task progress has been preserved."
    addMessage(Message(Assistant, notice, LocalDateTime.now(), transient = true, kind = ResponseKind.Summary))
    AssistantDockable.showConversation(getHistory)
  }

  /** Get the current history as an immutable snapshot. Copy is taken under
    * historyLock so the returned List is safe to iterate from any thread.
    */
  def getHistory: List[Message] = historyLock.synchronized {
    val arr = new Array[Message](history.size)
    val _ = history.toArray(arr)
    arr.toList
  }

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
      val contextSeed = captureContextSeed(view)
      addMessage(Message(User, userMessage, LocalDateTime.now()))
      AssistantDockable.showConversation(getHistory)
      AssistantDockable.setStatus(AssistantConstants.STATUS_THINKING)

      val messagesForApi = getHistory
        .filterNot(_.transient)
        .map(m => (m.role.wireValue, m.content))

      val _ = Isabelle_Thread.fork(name = "assistant-chat") {
        val context = getContext(contextSeed)
        val systemPromptEither =
          try {
            Right(
              PromptLoader.load(
                "chat_system.md",
                if (context.nonEmpty) Map("context" -> context) else Map.empty
              )
            )
          } catch {
            case ex: Exception => Left(ex)
          }

        systemPromptEither match {
          case Left(ex) =>
            GUI_Thread.later {
              val errorMsg =
                ErrorHandler.makeUserFriendly(
                  s"Failed to load prompt: ${ex.getMessage}",
                  "chat"
                )
              AssistantDockable.setStatus(s"Error: $errorMsg")
              addErrorResponse(errorMsg, "chat")
            }
          case Right(systemPrompt) =>
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
                    AssistantDockable.setStatus("Retrying…")
                    retryChatInternal(view, systemPrompt, messagesForApi)
                  }
                  val retryId = AssistantDockable.registerAction(retryAction)
                  // Compose error + retry action as one bubble. The ACTION
                  // marker is rendered as a clickable link by
                  // ConversationRenderer; we build the full content first
                  // and emit it with ResponseKind.Error so the bubble gets
                  // the error border.
                  addMessage(Message(
                    Assistant,
                    s"$errorMsg\n\n{{ACTION:$retryId:Retry}}",
                    LocalDateTime.now(),
                    kind = ResponseKind.Error
                  ))
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
    val _ = Isabelle_Thread.fork(name = "assistant-chat-retry") {
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
            addErrorResponse(errorMsg, "chat")
          }
      }
    }
  }

  private def handleCommand(view: View, input: String): Unit = {
    val parts = input.drop(1).split("\\s+", 2)
    val rawCmd = parts(0).toLowerCase
    val arg = if (parts.length > 1) parts(1) else ""

    addMessage(Message(User, input, LocalDateTime.now()))
    AssistantDockable.showConversation(getHistory)

    CommandId.fromWire(rawCmd) match {
      case Some(commandId) =>
        dispatch(commandId) match {
          case entry if entry.needsIQ && !IQAvailable.isAvailable =>
            addResponse(
              "Proof verification plugin (I/Q) is not installed. I/Q provides proof state, verification, and ATP integration. " +
                "Install via `make install` or see the README for setup."
            )
          case entry => entry.handler(view, arg)
        }
      case None =>
        val suggestion = closestCommand(rawCmd)
        val hint = suggestion.map(s => s" Did you mean `:$s`?").getOrElse("")
        addResponse(
          s"Unknown command `:$rawCmd`.$hint Type `:help` for available commands."
        )
    }
  }

  /** Find the closest command name within Levenshtein distance 2, or None. */
  private def closestCommand(input: String): Option[String] = {
    if (input.isEmpty) None
    else {
      val candidates = commandNames.map(n => (n, levenshtein(input, n)))
      candidates.filter(_._2 <= 2).sortBy(_._2).headOption.map(_._1)
    }
  }

  /** Classic iterative Levenshtein with two rolling rows. O(m*n) time, O(n) space. */
  private def levenshtein(a: String, b: String): Int = {
    if (a == b) return 0
    if (a.isEmpty) return b.length
    if (b.isEmpty) return a.length
    val n = b.length
    val prev = (0 to n).toArray
    val curr = new Array[Int](n + 1)
    var i = 1
    while (i <= a.length) {
      curr(0) = i
      var j = 1
      while (j <= n) {
        val cost = if (a.charAt(i - 1) == b.charAt(j - 1)) 0 else 1
        curr(j) = math.min(
          math.min(curr(j - 1) + 1, prev(j) + 1),
          prev(j - 1) + cost
        )
        j += 1
      }
      System.arraycopy(curr, 0, prev, 0, n + 1)
      i += 1
    }
    prev(n)
  }

  private def showHelp(target: String = ""): Unit = {
    if (target.nonEmpty) {
      showHelpForCommand(target.stripPrefix(":").toLowerCase)
      return
    }
    val headerBg = UIColors.HelpTable.headerBackground
    val borderColor = UIColors.HelpTable.borderColor
    val rowBorder = UIColors.HelpTable.rowBorder
    val accentColor = UIColors.HelpTable.accentColor
    val infoBg = UIColors.InfoBox.background
    val infoBorder = UIColors.InfoBox.border

    val intro =
      s"<div style='margin-bottom:${UIDesign.Space.md};font-size:${UIDesign.FontSize.base};'>" +
        "Tip: type <code>:help &lt;command&gt;</code> for details on any command. " +
        "Example: <code>:help suggest</code>." +
        "</div>"

    val sortedCommands = dispatch.toList.sortBy(_._1.wireName)
    val cellBase =
      s"padding:${UIDesign.Space.sm} ${UIDesign.Space.md};font-size:${UIDesign.FontSize.base};"
    val header =
      s"<tr>" +
        s"<th style='${cellBase}border-bottom:2px solid $borderColor;text-align:left;background:$headerBg;'>Command</th>" +
        s"<th style='${cellBase}border-bottom:2px solid $borderColor;text-align:left;background:$headerBg;'>Description</th>" +
        s"<th style='${cellBase}border-bottom:2px solid $borderColor;text-align:center;background:$headerBg;'>I/Q</th>" +
        "</tr>"
    val rows = sortedCommands.map { case (commandId, entry) =>
      val iq = if (entry.needsIQ) "yes" else ""
      s"<tr>" +
        s"<td style='${cellBase}border-bottom:1px solid $rowBorder;font-family:${MarkdownRenderer.codeFont};" +
        s"white-space:nowrap;color:$accentColor;'>:${commandId.wireName}</td>" +
        s"<td style='${cellBase}border-bottom:1px solid $rowBorder;'>${entry.description}</td>" +
        s"<td style='${cellBase}border-bottom:1px solid $rowBorder;text-align:center;'>$iq</td>" +
        "</tr>"
    }.mkString
    val table =
      s"<table style='width:100%;border-collapse:collapse;'>$header$rows</table>"
    val targetHelp =
      s"<div style='margin-top:${UIDesign.Space.md};padding:${UIDesign.Space.md} ${UIDesign.Space.md};" +
        s"background:$infoBg;border:1px solid $infoBorder;border-radius:${UIDesign.Radius.sm};'>" +
        s"<div style='font-weight:bold;margin-bottom:${UIDesign.Space.sm};'>Target Syntax</div>" +
        s"<div style='font-size:${UIDesign.FontSize.base};'>" +
        "Commands like <code>:explain</code> and <code>:suggest</code> accept optional targets:" +
        "</div>" +
        s"<div style='font-size:${UIDesign.FontSize.base};padding-left:${UIDesign.Space.lg};margin-top:${UIDesign.Space.sm};'>" +
        "• <code>cursor</code> — current cursor position (default)<br/>" +
        "• <code>selection</code> — current text selection<br/>" +
        "• <code>Theory.thy:42</code> — specific line<br/>" +
        "• <code>Theory.thy:10-20</code> — line range<br/>" +
        "• <code>Theory.thy:lemma_name</code> — named element<br/>" +
        "• <code>cursor+5</code>, <code>cursor-3</code> — relative offset" +
        "</div></div>"
    addMessage(
      Message(
        Assistant,
        intro + table + targetHelp,
        LocalDateTime.now(),
        rawHtml = true
      )
    )
    AssistantDockable.showConversation(getHistory)
  }

  /** Per-command help card. Invoked via `:help COMMAND`; falls back to a
    * did-you-mean suggestion when COMMAND is unknown.
    */
  private def showHelpForCommand(rawName: String): Unit = {
    CommandId.fromWire(rawName) match {
      case None =>
        val suggestion = closestCommand(rawName)
        val hint = suggestion.map(s => s" Did you mean `:$s`?").getOrElse("")
        addResponse(s"Unknown command `:$rawName`.$hint Type `:help` to see all commands.")
      case Some(id) =>
        val entry = dispatch(id)
        val name = id.wireName
        val iqNote =
          if (entry.needsIQ) s"<div style='font-size:${UIDesign.FontSize.sm};color:${UIColors.HelpTable.accentColor};margin-top:${UIDesign.Space.sm};'>Requires I/Q plugin.</div>"
          else ""
        val usageLine = usageExample(id)
        val acceptsTarget = commandAcceptsTarget(id)
        val targetNote =
          if (acceptsTarget)
            s"<div style='font-size:${UIDesign.FontSize.sm};margin-top:${UIDesign.Space.sm};'>" +
              "Accepts an optional target: <code>cursor</code> (default), <code>selection</code>, " +
              "<code>Theory.thy:42</code>, <code>Theory.thy:10-20</code>, <code>Theory.thy:lemma_name</code>, or <code>cursor±N</code>." +
              "</div>"
          else ""
        val related = relatedCommands.getOrElse(id, Nil)
        val seeAlso =
          if (related.isEmpty) ""
          else {
            val links = related
              .map(r => s"<code>:${r.wireName}</code>")
              .mkString(", ")
            s"<div style='font-size:${UIDesign.FontSize.sm};margin-top:${UIDesign.Space.sm};color:${UIColors.Muted.text};'>" +
              s"See also: $links" +
              "</div>"
          }
        val body =
          s"<div style='font-family:${MarkdownRenderer.codeFont};font-weight:bold;color:${UIColors.HelpTable.accentColor};" +
            s"font-size:${UIDesign.FontSize.md};margin-bottom:${UIDesign.Space.sm};'>:$name</div>" +
            s"<div style='font-size:${UIDesign.FontSize.base};'>${entry.description}.</div>" +
            s"<div style='font-size:${UIDesign.FontSize.sm};margin-top:${UIDesign.Space.sm};color:${UIColors.HelpTable.accentColor};'>" +
            s"Usage: <code>$usageLine</code></div>" +
            targetNote + iqNote + seeAlso
        val html = UIDesign.infoCard(
          "",
          body,
          UIColors.HelpTable.accentColor,
          UIColors.InfoBox.background,
          UIColors.InfoBox.border
        )
        addMessage(Message(Assistant, html, LocalDateTime.now(), rawHtml = true))
        AssistantDockable.showConversation(getHistory)
    }
  }

  /** Cross-links surfaced in the per-command `:help <command>` card.
    * The listing is deliberately curated rather than computed: "related"
    * is a user-facing judgement (what would the user want to try next?),
    * not a code-graph query. Order matters — the first entry is the most
    * obvious next thing to try.
    */
  private[assistant] val relatedCommands: Map[CommandId, List[CommandId]] = Map(
    CommandId.Suggest        -> List(CommandId.SuggestStrategy, CommandId.SuggestTactic, CommandId.Sledgehammer),
    CommandId.SuggestStrategy -> List(CommandId.Suggest, CommandId.SuggestTactic),
    CommandId.SuggestTactic   -> List(CommandId.Suggest, CommandId.SuggestStrategy),
    CommandId.Sledgehammer    -> List(CommandId.Suggest, CommandId.TryMethods, CommandId.Verify),
    CommandId.Verify          -> List(CommandId.Sledgehammer, CommandId.TryMethods, CommandId.Suggest),
    CommandId.TryMethods      -> List(CommandId.Sledgehammer, CommandId.Verify),
    CommandId.Explain         -> List(CommandId.ExplainError, CommandId.ShowType, CommandId.PrintContext),
    CommandId.ExplainError    -> List(CommandId.Explain, CommandId.PrintContext),
    CommandId.ShowType        -> List(CommandId.Explain),
    CommandId.Nitpick         -> List(CommandId.Quickcheck, CommandId.ExplainCounterexample),
    CommandId.Quickcheck      -> List(CommandId.Nitpick, CommandId.ExplainCounterexample),
    CommandId.ExplainCounterexample -> List(CommandId.Nitpick, CommandId.Quickcheck),
    CommandId.Find            -> List(CommandId.Search, CommandId.Theories),
    CommandId.Search          -> List(CommandId.Find, CommandId.Read),
    CommandId.Theories        -> List(CommandId.Read, CommandId.Deps, CommandId.Search),
    CommandId.Read            -> List(CommandId.Theories, CommandId.Deps, CommandId.Search),
    CommandId.Deps            -> List(CommandId.Theories, CommandId.Read),
    CommandId.GenerateIntro   -> List(CommandId.GenerateElim, CommandId.GenerateTests),
    CommandId.GenerateElim    -> List(CommandId.GenerateIntro, CommandId.GenerateTests),
    CommandId.GenerateTests   -> List(CommandId.GenerateIntro, CommandId.GenerateElim),
    CommandId.Set             -> List(CommandId.Models, CommandId.Version)
  )

  /** Commands that forward their argument through TargetParser. */
  private def commandAcceptsTarget(id: CommandId): Boolean = id match {
    case CommandId.Explain | CommandId.Suggest => true
    case _                                     => false
  }

  /** Canonical usage example per command, rendered in the per-command help card. */
  private def usageExample(id: CommandId): String = id match {
    case CommandId.Explain     => ":explain [target]"
    case CommandId.Suggest     => ":suggest [target]"
    case CommandId.Verify      => ":verify <proof>"
    case CommandId.Find        => ":find <pattern>"
    case CommandId.Search      => ":search <pattern>"
    case CommandId.Read        => ":read <theory> [lines]"
    case CommandId.Deps        => ":deps <theory>"
    case CommandId.Set         => ":set [key] [value]"
    case CommandId.Help        => ":help [command]"
    case other                 => s":${other.wireName}"
  }

  /** Display the plugin name and version. Reads from the packaged
    * plugin.props via [[BuildInfo]]; falls back to "Isabelle Assistant
    * dev" when the resource is not on the classpath. */
  private def runVersion(): Unit = {
    addInfoResponse(BuildInfo.identity)
  }

  /** Refresh available Bedrock models and display in chat.
    * 
    * Queries AWS Bedrock for available Anthropic models in the configured region.
    * Updates the model cache and displays the list in chat. Runs asynchronously on
    * background thread to avoid blocking the UI.
    */
  private def runModels(): Unit = {
    AssistantDockable.setStatus("Refreshing models…")

    val _ = Isabelle_Thread.fork(name = "chat-models") {
      try {
        val region = AssistantOptions.getRegion
        val models = BedrockModels.refreshModels(region)
        GUI_Thread.later {
          val modelList = models.map(m => s"* `$m`").mkString("\n")
          addResponse(
            s"**Available Anthropic Models** (${models.length} total)\n\n$modelList\n\n" +
              "Use `:set model <id>` to select one."
          )
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            addErrorResponse(ex.getMessage, "refresh models")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
      }
    }
  }

  /** View or modify Assistant configuration settings.
    * 
    * Handles three forms:
    * - `:set` - List all settings with their current values
    * - `:set key` - Show value of specific setting
    * - `:set key value` - Update setting to new value
    * 
    * Settings changes take effect immediately and persist across sessions.
    * 
    * @param arg Arguments after `:set` command (empty, key only, or key + value)
    */
  private def runSet(arg: String): Unit = {
    val parts = arg.trim.split("\\s+", 2)

    if (arg.trim.isEmpty) {
      addResponse(
        "**Current Settings**\n\n" +
          "Tip: use `:set <key> <value>` to change a setting.\n\n" +
          AssistantOptions.listSettings
      )
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

  /** Explain Isabelle code at specified target location.
    * 
    * Resolves the target (cursor, selection, or explicit location), fetches surrounding context,
    * and invokes the LLM with the explain_with_context prompt template. Displays result in chat.
    * 
    * @param view The current jEdit view
    * @param targetSpec Target specification (empty for cursor, or TargetParser syntax)
    */
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
                addResponse(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
                None
            }
          } else {
            Some(buffer.getText(start, end - start))
          }

          textOpt.foreach { text =>
            ActionHelper.runAndRespond("chat-explain", "Explaining code…") {
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

  /** Generate proof step suggestions for target location.
    * 
    * Delegates to SuggestAction which combines LLM suggestions with optional Sledgehammer results,
    * verifies candidates in parallel when I/Q is available, and displays ranked results with badges.
    * 
    * @param view The current jEdit view
    * @param targetSpec Target specification (empty for cursor, or TargetParser syntax)
    */
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
          AssistantDockable.setStatus("Generating suggestions…")
          val _ = Isabelle_Thread.fork(name = "chat-suggest") {
            try {
              SuggestAction.suggestFromChat(view, buffer, offset)
              GUI_Thread.later {
                AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
              }
            } catch {
              case ex: Exception =>
                GUI_Thread.later {
                  addErrorResponse(ex.getMessage, "suggest")
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

  /** Explain error message at cursor position.
    * 
    * Extracts the error message from PIDE at the current cursor position, gathers surrounding
    * command text and goal state as context, then invokes the LLM with the explain_error prompt.
    * 
    * @param view The current jEdit view
    */
  private def runExplainError(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    
    // Extract error first (this is local to PIDE, not I/Q MCP)
    ExplainErrorAction.extractErrorAtOffset(buffer, offset) match {
      case None =>
        addResponse(AssistantConstants.UIText.NO_ERROR_AT_CURSOR)
      case Some(error) =>
        // Fork immediately to avoid blocking EDT on I/Q MCP calls
        ActionHelper.runAndRespond(
          "chat-explain-error",
          "Explaining error…"
        ) {
          // These I/Q MCP calls are now on background thread
          val context =
            CommandExtractor.getCommandAtOffset(buffer, offset).getOrElse("")
          val goalState = GoalExtractor.getGoalState(buffer, offset)

          val subs = Map(
            "error" -> error,
            "context" -> context
          ) ++ goalState.map(g => Map("goal_state" -> g)).getOrElse(Map.empty)

          val prompt = PromptLoader.load("explain_error.md", subs)
          BedrockClient.invokeInContext(prompt)
        }
    }
  }

  /** Verify proof method via I/Q and optionally diagnose failures with LLM.
    * 
    * Runs I/Q proof verification on the provided proof text. On success, displays timing.
    * On failure, automatically diagnoses the error using the LLM with the diagnose_verification
    * prompt template.
    * 
    * @param view The current jEdit view
    * @param proof The proof text to verify (e.g., "by simp", "by (induction xs) auto")
    */
  private def runVerify(view: View, proof: String): Unit = {
    if (proof.trim.isEmpty)
      addResponse("Usage: `:verify <proof>`\n\nExample: `:verify by simp`")
    else {
      ActionHelper.runIQCommand("chat-verify", AssistantConstants.STATUS_VERIFYING) { v =>
        val buffer = v.getBuffer
        val offset = v.getTextArea.getCaretPosition
        val timeout = AssistantOptions.getVerificationTimeout
        
        IQIntegration.verifyProofAsync(v, proof, timeout, {
          case IQIntegration.ProofSuccess(timeMs, _) =>
            addSuccessResponse(s"Proof verified successfully (${timeMs}ms).")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          case IQIntegration.ProofFailure(error) =>
            addErrorResponse(s"Verification failed: $error", "verify")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            // Diagnose failure using LLM on background thread
            val _ = Isabelle_Thread.fork(name = "chat-verify-diagnose") {
              val goalState = GoalExtractor.getGoalState(buffer, offset)
              val context = CommandExtractor.getCommandAtOffset(buffer, offset)
              try {
                val subs = Map("proof" -> proof, "error" -> error) ++
                  goalState.map(g => Map("goal_state" -> g)).getOrElse(Map.empty) ++
                  context.map(c => Map("context" -> c)).getOrElse(Map.empty)
                val diagPrompt = PromptLoader.load("diagnose_verification.md", subs)
                val diagnosis = BedrockClient.invokeNoCache(diagPrompt)
                GUI_Thread.later { addResponse(diagnosis) }
              } catch {
                case ex: Exception =>
                  Output.writeln(s"[Assistant] Post-verification diagnosis failed: ${ex.getMessage}")
              }
            }
          case IQIntegration.ProofTimeout =>
            addErrorResponse("Verification timed out.", "verify")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          case _ =>
            addErrorResponse("Verification unavailable.", "verify")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        })
      }(view)
    }
  }

  private def runSledgehammer(view: View): Unit = {
    ActionHelper.runIQCommand("chat-sledgehammer", "Running sledgehammer…") { v =>
      val timeout = AssistantOptions.getSledgehammerTimeout
      IQIntegration.runSledgehammerAsync(v, timeout, {
        case Right(results) if results.nonEmpty =>
          val lines = results
            .map(r => s"[sledgehammer] `${r.proofMethod}` (${r.timeMs}ms)")
            .mkString("\n\n")
          addResponse(s"**Sledgehammer found ${results.length} proofs:**\n\n$lines")
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        case Right(_) =>
          addResponse("Sledgehammer found no proofs.")
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        case Left(error) =>
          addErrorResponse(error, "sledgehammer")
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      })
    }(view)
  }

  private def runFind(view: View, pattern: String): Unit = {
    if (pattern.trim.isEmpty)
      addResponse(
        "Usage: `:find <pattern>`\n\nExample: `:find \"_ + _ = _ + _\"`"
      )
    else {
      ActionHelper.runIQCommand("chat-find", "Searching theorems…") { v =>
        val limit = AssistantOptions.getFindTheoremsLimit
        val timeout = AssistantOptions.getFindTheoremsTimeout
        val quotedPattern =
          if (pattern.startsWith("\"")) pattern else s"\"$pattern\""
        
        IQIntegration.runFindTheoremsAsync(v, quotedPattern, limit, timeout, {
          case Right(results) if results.nonEmpty =>
            val lines = results.map(r => s"* $r").mkString("\n\n")
            addResponse(s"**Found ${results.length} theorems:**\n\n$lines")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          case Right(_) =>
            addResponse(s"No theorems found matching: $pattern")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          case Left(error) =>
            addErrorResponse(error, "find theorems")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        })
      }(view)
    }
  }

  def addResponse(content: String): Unit = {
    addMessage(Message(Assistant, content, LocalDateTime.now()))
    AssistantDockable.showConversation(getHistory)
  }

  /** Post an assistant-authored error to the chat. The bubble is rendered
    * with the error border via `ResponseKind.Error`, so callers must not
    * prepend their own `"Error: "` tag — the renderer owns the visual
    * distinction. The `operation` label passes through
    * [[ErrorHandler.makeUserFriendly]] so the user sees remediation hints
    * instead of raw technical text (network errors → credentials hint;
    * timeouts → `:set verify_timeout` hint; etc.). */
  def addErrorResponse(content: String, operation: String = "operation"): Unit = {
    val friendly = ErrorHandler.makeUserFriendly(content, operation)
    addMessage(Message(Assistant, friendly, LocalDateTime.now(), kind = ResponseKind.Error))
    AssistantDockable.showConversation(getHistory)
  }

  /** Post an assistant-authored success message. Rendered with a green
    * bubble border. */
  def addSuccessResponse(content: String): Unit = {
    addMessage(Message(Assistant, content, LocalDateTime.now(), kind = ResponseKind.Success))
    AssistantDockable.showConversation(getHistory)
  }

  /** Post an assistant-authored informational message. Rendered with a
    * neutral (info-tinted) bubble border. */
  def addInfoResponse(content: String): Unit = {
    addMessage(Message(Assistant, content, LocalDateTime.now(), kind = ResponseKind.Info))
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

  private def captureContextSeed(view: View): ChatContextSeed =
    try {
      GUI_Thread.now {
        val textArea = view.getTextArea
        val selected =
          Option(textArea.getSelectedText).map(_.trim).filter(_.nonEmpty)
        val buffer = view.getBuffer
        val path = MenuContext.bufferPath(buffer)
        val caret =
          Option(textArea).map(_.getCaretPosition).getOrElse(0)
        ChatContextSeed(
          selectedText = selected,
          path = path,
          caretOffset = math.max(0, caret)
        )
      }
    } catch {
      case ex: Exception =>
        // The fallback seed drops the user's selection and file path. A
        // silent swallow used to hide why the follow-up chat lost
        // context; log so the cause surfaces in the Isabelle messages
        // panel.
        ErrorHandler.safeLog(
          s"[Assistant] captureContextSeed fallback: ${ex.getMessage}"
        )
        ChatContextSeed(selectedText = None, path = None, caretOffset = 0)
    }

  private def getContext(seed: ChatContextSeed): String =
    // If the user already selected text we pass that through verbatim —
    // no I/Q round-trip needed. This is the common case and used to be
    // masked behind a 3-second CONTEXT_FETCH_TIMEOUT wait when the
    // lookup path was reached for edge cases.
    seed.selectedText.getOrElse {
      seed.path
        .flatMap { path =>
          IQMcpClient
            .callResolveCommandTarget(
              selectionArgs = Map(
                "command_selection" -> "file_offset",
                "path" -> path,
                "offset" -> seed.caretOffset
              ),
              timeoutMs = AssistantConstants.CHAT_CONTEXT_FETCH_TIMEOUT
            )
            .toOption
            .map(_.command.source)
            .map(_.trim)
            .filter(_.nonEmpty)
        }
        .getOrElse("")
    }
}
