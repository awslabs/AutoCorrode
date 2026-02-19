/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/** Explains Isabelle code at cursor or selection using LLM with PIDE-derived context. */
object ExplainAction {
  
  def explain(view: View, commandText: String): Unit = {
    val target = getCurrentTarget(view)
    ChatAction.addMessage(ChatAction.User, s":explain ${TargetParser.formatTarget(target)}")
    AssistantDockable.showConversation(ChatAction.getHistory)
    
    ActionHelper.runAndRespond("assistant-explain", "Explaining code...") {
      val context = ContextFetcher.getContext(view, AssistantConstants.CONTEXT_FETCH_TIMEOUT)
      val subs = Map("theorem" -> commandText) ++ context.map("context" -> _)
      val prompt = PromptLoader.load("explain_with_context.md", subs)
      BedrockClient.invokeInContext(prompt)
    }
  }

  private def getCurrentTarget(view: View): TargetParser.Target = {
    val selection = view.getTextArea.getSelectedText
    if (selection != null && selection.trim.nonEmpty) TargetParser.CurrentSelection
    else TargetParser.CurrentCursor
  }

  /** Extract the defined name from Isabelle source, handling plain names, cartouches,
   *  locale qualifiers, attribute annotations, and primed identifiers. */
  def extractName(text: String): Option[String] = {
    // Identifier: word chars plus primes, or cartouche-delimited
    val id = """([\w']+|‹[\w']+›|\\<open>[\w']+\\<close>)"""
    // Optional locale qualifier: (in locale_name)
    val localeQ = """(?:\s*\(in\s+\w+\))?"""
    // Optional attributes: [simp] or [simp, intro]
    val attrs = """(?:\s*\[[^\]]*\])?"""
    val defKws = "definition|fun|function|primrec|abbreviation"
    val thmKws = "lemma|theorem|corollary|proposition"
    val dtKws = "datatype|codatatype"

    val defP = s"""(?:$defKws)$localeQ\\s+$id""".r
    val thmP = s"""(?:$thmKws)$localeQ\\s+$id$attrs""".r
    val dtP = s"""(?:$dtKws)\\s+[^=]*?$id\\s*=""".r

    def clean(s: String): String =
      s.stripPrefix("‹").stripSuffix("›").stripPrefix("\\<open>").stripSuffix("\\<close>")

    def firstCapture(m: scala.util.matching.Regex.Match): String =
      (1 to m.groupCount).flatMap(i => Option(m.group(i))).headOption.map(clean).getOrElse(m.group(0))

    defP.findFirstMatchIn(text).map(firstCapture)
      .orElse(thmP.findFirstMatchIn(text).map(firstCapture))
      .orElse(dtP.findFirstMatchIn(text).map(firstCapture))
  }
}
