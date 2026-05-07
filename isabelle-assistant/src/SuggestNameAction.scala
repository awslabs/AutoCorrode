/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer

/** Suggests descriptive names for Isabelle definitions, lemmas, and theorems.
  * Uses LLM with context including command body, type, existing names in scope,
  * and surrounding definitions to propose names that follow Isabelle
  * conventions and avoid clashes with existing identifiers.
  */
object SuggestNameAction {

  private val nameableKeywords = IsabelleKeywords.entityKeywords

  /** Chat command handler: suggest name for command at cursor. */
  def chatSuggestName(view: View): Unit = suggestNameInternal(view)

  /** Context menu handler: suggest name for command at cursor. */
  def suggestName(view: View): Unit = {
    ChatAction.addMessage(ChatAction.User, ":suggest-name")
    AssistantDockable.showConversation(ChatAction.getHistory)
    suggestNameInternal(view)
  }

  private def suggestNameInternal(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    AssistantDockable.setStatus("Gathering context…")

    val _ = Isabelle_Thread.fork(name = "assistant-suggest-name") {
      try {
        // Command resolution goes through I/Q MCP, so it must live on this
        // background thread — never call it from the EDT or jEdit freezes.
        val commandTextOpt = CommandExtractor.getCommandAtOffset(buffer, offset)
        val keywordOpt = CommandExtractor.getCommandKeyword(buffer, offset)

        (commandTextOpt, keywordOpt) match {
          case (None, _) =>
            GUI_Thread.later {
              AssistantDockable.respondInChat(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            }
          case (_, None) =>
            GUI_Thread.later {
              AssistantDockable.respondInChat("Could not determine command type.")
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            }
          case (Some(_), Some(keyword)) if !nameableKeywords.contains(keyword) =>
            GUI_Thread.later {
              AssistantDockable.respondInChat(
                s"Command type '$keyword' does not require naming."
              )
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            }
          case (Some(commandText), Some(keyword)) =>
            val context = gatherContext(buffer, offset, commandText)
            val subs = buildPromptSubstitutions(commandText, keyword, context)
            val prompt = PromptLoader.load("suggest_name.md", subs)

            AssistantDockable.setStatus("Generating name suggestions…")
            val response = BedrockClient.invokeInContext(prompt)
            val suggestions = parseNameSuggestions(response)

            GUI_Thread.later {
              if (suggestions.isEmpty) {
                AssistantDockable.respondInChat("No name suggestions generated.")
              } else {
                displaySuggestions(view, keyword, suggestions)
              }
              AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            }
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            AssistantDockable.respondInChat(
              s"Error: ${ErrorHandler.makeUserFriendly(ex.getMessage, "suggest-name")}"
            )
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
      }
    }
  }

  private case class NameContext(
      currentName: Option[String],
      existingNames: List[String],
      theoryName: Option[String],
      surroundingContext: Option[String]
  )

  private def gatherContext(
      buffer: JEditBuffer,
      offset: Int,
      commandText: String
  ): NameContext = {
    // Extract current name if present
    val currentName = ExplainAction.extractName(commandText)

    // extractEntities calls the I/Q MCP backplane synchronously, so it
    // must stay on this background thread. Dispatching via GUI_Thread.later
    // used to freeze jEdit for several seconds while waiting on the HTTP
    // response — the other context-menu actions (e.g. Generate Tests)
    // avoid this by calling ContextFetcher directly on the fork, same as
    // we do here.
    val existingNames =
      if (javax.swing.SwingUtilities.isEventDispatchThread) {
        Output.warning(
          "[Assistant] gatherContext called from GUI thread — skipping entity extraction"
        )
        List.empty[String]
      } else {
        ContextFetcher
          .extractEntities(buffer, offset)
          .map(_._2)
          .distinct
          .filter(n =>
            !n.startsWith("Pure.") && !n.startsWith("HOL.") &&
              n != "Trueprop" && !n.contains(".")
          )
          .sorted
      }

    // Get theory name from buffer header parsing
    val theoryName = TheoryMetadata.theoryName(buffer)

    // Get surrounding context (commands near cursor) - optional for now
    val surroundingContext: Option[String] = None

    NameContext(currentName, existingNames, theoryName, surroundingContext)
  }

  private def buildPromptSubstitutions(
      commandText: String,
      keyword: String,
      context: NameContext
  ): Map[String, String] = {
    var subs = Map(
      "command" -> commandText,
      "command_type" -> keyword
    )

    context.currentName.foreach { name =>
      subs = subs + ("current_name" -> name)
    }

    if (context.existingNames.nonEmpty) {
      val namesList =
        context.existingNames.take(50).map(n => s"- `$n`").mkString("\n")
      subs = subs + ("existing_names" -> namesList)
    }

    context.theoryName.foreach { name =>
      subs = subs + ("theory_name" -> name)
    }

    context.surroundingContext.foreach { ctx =>
      subs = subs + ("context" -> ctx)
    }

    subs
  }

  private[assistant] def parseNameSuggestions(response: String): List[String] = {
    val namePattern = """NAME:\s*([a-zA-Z][a-zA-Z0-9_']*)""".r
    namePattern
      .findAllMatchIn(response)
      .map(_.group(1).trim)
      .filter(_.nonEmpty)
      .toList
      .distinct
      .take(5)
  }

  private def displaySuggestions(
      view: View,
      keyword: String,
      suggestions: List[String]
  ): Unit = {
    val sb = new StringBuilder()
    sb.append(s"**Name suggestions for $keyword:**\n\n")

    for (suggestion <- suggestions) {
      val actionId = InsertHelper.registerInsertAction(view, suggestion)
      sb.append(s"- `$suggestion` {{INSERT:$actionId}}\n")
    }

    ChatAction.addMessage(ChatAction.Assistant, sb.toString)
    AssistantDockable.showConversation(ChatAction.getHistory)
  }
}
