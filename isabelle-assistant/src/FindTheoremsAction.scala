/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import javax.swing.JOptionPane

/** Searches for theorems via I/Q find_theorems, with free-variable wildcard substitution. */
object FindTheoremsAction {
  def findTheoremsForGoal(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    GoalExtractor.getGoalState(buffer, offset).flatMap(extractGoalPattern) match {
      case Some(pattern) => findTheorems(view, Some(pattern))
      case None =>
        GUI.warning_dialog(
          view,
          "Isabelle Assistant",
          "No goal at cursor position"
        )
    }
  }

  def findTheorems(view: View, initialPattern: Option[String]): Unit = {
    val patternOpt = initialPattern.filter(_.trim.nonEmpty).orElse {
      Option(JOptionPane.showInputDialog(view, "Search pattern:", "Find Theorems", JOptionPane.PLAIN_MESSAGE))
        .map(_.trim).filter(_.nonEmpty)
    }
    patternOpt.foreach { pattern =>
      ChatAction.addMessage(ChatAction.User, s":find $pattern")
      AssistantDockable.showConversation(ChatAction.getHistory)

      if (!IQAvailable.isAvailable) {
        GUI.warning_dialog(view, "Isabelle Assistant", "I/Q plugin not available")
      } else {
        val searchPattern = toSearchPattern(pattern, view)
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition

        IQIntegration.getCommandAtOffset(buffer, offset) match {
          case Some(command) =>
            AssistantDockable.setStatus("Searching theorems...")
            val quotedPattern = "\"" + searchPattern + "\""

            IQIntegration.runFindTheoremsAsync(
              view,
              command,
              quotedPattern,
              AssistantOptions.getFindTheoremsLimit,
              AssistantOptions.getFindTheoremsTimeout,
              {
                case Right(results) =>
                  GUI_Thread.later { displayResults(view, searchPattern, results) }
                case Left(error) =>
                  GUI_Thread.later {
                    AssistantDockable.respondInChat(s"Find theorems error: $error")
                    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                  }
              }
            )
          case None =>
            GUI.warning_dialog(
              view,
              "Isabelle Assistant",
              "No Isabelle command at cursor position"
            )
        }
      }
    }
  }

  private def displayResults(view: View, pattern: String, results: List[String]): Unit = {
    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)

    if (results.isEmpty) {
      AssistantDockable.respondInChat(s"No theorems found matching: $pattern")
    } else {
      val sb = new StringBuilder(s"Find Theorems: \"$pattern\"\n\nFound ${results.length} theorems:\n\n")
      for (line <- results) {
        val colonIdx = line.indexOf(':')
        if (colonIdx > 0) {
          val name = line.substring(0, colonIdx).trim
          val stmt = line.substring(colonIdx + 1).trim
          val id = AssistantDockable.registerAction(() => {
            view.getBuffer.insert(view.getTextArea.getCaretPosition, name)
          })
          sb.append(s"* `$name`: $stmt {{INSERT:$id}}\n")
        } else {
          sb.append(s"* $line\n")
        }
      }
      ChatAction.addMessage(ChatAction.Assistant, sb.toString)
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
  }

  private[assistant] def extractGoalPattern(goalState: String): Option[String] = {
    val lines = goalState.linesIterator.map(_.trim).filter(_.nonEmpty).toList
    val numbered =
      lines.collectFirst { case l if l.matches("""^\d+\.\s+.*""") =>
        l.replaceFirst("""^\d+\.\s*""", "")
      }
    val fallback = lines.find(l =>
      !l.startsWith("goal") &&
        !l.contains("subgoal") &&
        !l.startsWith("proof")
    )
    numbered
      .orElse(fallback)
      .map(_.trim)
      .filter(_.nonEmpty)
      .map(_.take(AssistantConstants.MAX_RESPONSE_LENGTH))
  }

  /** Replace free variables with _ wildcards for find_theorems search.
   *  Uses word-boundary-aware replacement to avoid corrupting constant names
   *  that contain the variable as a substring (e.g., variable "x" in "max"). */
  private def toSearchPattern(text: String, view: View): String = {
    var s = text.trim
    s = s.stripPrefix("\u2039").stripSuffix("\u203a")
    s = s.stripPrefix("\\<open>").stripSuffix("\\<close>")
    val freeVars = getFreeVariableNames(view)
    for (v <- freeVars) {
      // Word-boundary-aware replacement: only replace when the variable is not
      // adjacent to word characters (letters, digits, underscore, prime)
      val wordChar = """[\w']"""
      val pattern = s"(?<!$wordChar)${java.util.regex.Pattern.quote(v)}(?!$wordChar)"
      s = s.replaceAll(pattern, "_")
    }
    s.trim
  }

  private def getFreeVariableNames(view: View): Set[String] = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    Document_Model.get_model(buffer).map { model =>
      val snapshot = Document_Model.snapshot(model)
      val range = snapshot.node.command_iterator(Text.Range(offset, offset + 1))
        .toList.headOption.map { case (cmd, cmdOffset) =>
          Text.Range(cmdOffset, cmdOffset + cmd.length)
        }.getOrElse(Text.Range(offset, math.min(offset + 1, buffer.getLength)))
      // Accumulate constants and free vars via cumulate return value (no side effects)
      val (constants, freeVars) = snapshot.cumulate(range, (Set.empty[String], Set.empty[String]),
        Markup.Elements(Markup.CONST, Markup.FREE), _ => {
          case ((cs, fs), Text.Info(r, XML.Elem(Markup(Markup.CONST, _), _))) =>
            Some((cs + buffer.getText(r.start, r.length), fs))
          case ((cs, fs), Text.Info(r, XML.Elem(Markup(Markup.FREE, _), _))) =>
            Some((cs, fs + buffer.getText(r.start, r.length)))
          case _ => None
        }).foldLeft((Set.empty[String], Set.empty[String])) { case ((ac, af), Text.Info(_, (c, f))) => (ac ++ c, af ++ f) }
      freeVars -- constants
    }.getOrElse(Set.empty[String])
  }
}
