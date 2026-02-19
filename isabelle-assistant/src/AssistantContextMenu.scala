/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.gui.DynamicContextMenuService
import org.gjt.sp.jedit.textarea.JEditTextArea
import java.awt.event.MouseEvent
import javax.swing.{JMenu, JMenuItem}

/** Dynamic right-click context menu for Isabelle/jEdit. Adapts available
  * actions based on cursor context: proof state, selection, error presence,
  * definition type, and I/Q availability.
  */
class AssistantContextMenu extends DynamicContextMenuService {
  override def createMenu(
      textArea: JEditTextArea,
      evt: MouseEvent
  ): Array[JMenuItem] = {
    if (evt == null) Array.empty
    else {
      val buffer = textArea.getBuffer
      val mode = buffer.getMode
      if (mode == null || mode.getName != "isabelle") Array.empty
      else {
        val view = textArea.getView
        val offset = textArea.xyToOffset(evt.getX, evt.getY)
        val selection = Option(textArea.getSelectedText)
        val ctx = MenuContext.analyze(view, buffer, offset, selection)
        val menu = new JMenu("Isabelle Assistant")

        // === Understanding ===
        val understandMenu = new JMenu("Understanding")
        if (ctx.hasCommand || ctx.hasSelection) {
          addItem(understandMenu, "Explain") { _ =>
            val text = selection
              .filter(_.trim.nonEmpty)
              .orElse(CommandExtractor.getCommandAtOffset(buffer, offset))
            text match {
              case Some(t) => ExplainAction.explain(view, t)
              case None    =>
                AssistantDockable.respondInChat("No command at cursor.")
            }
          }
        }

        if (ctx.onError)
          addItem(understandMenu, "Explain Error")(_ =>
            ExplainErrorAction.explainError(view)
          )

        if (ctx.hasTypeInfo)
          addItem(understandMenu, "Show Type")(_ =>
            ShowTypeAction.showType(view)
          )

        addItem(understandMenu, "Summarize Theory")(_ =>
          SummarizeTheoryAction.summarize(view)
        )
        menu.add(understandMenu)

        // === Proof (only in proof context) ===
        if (ctx.inProof) {
          val proofMenu = new JMenu("Proof")

          addItem(proofMenu, "Suggest Proof Step")(_ =>
            SuggestAction.suggest(view, buffer, offset)
          )
          addItem(proofMenu, "Suggest Strategy")(_ =>
            SuggestStrategyAction.suggest(view)
          )

          if (ctx.iqAvailable) {
            proofMenu.addSeparator()
            addItem(proofMenu, "Auto-Prove")(_ =>
              ChatAction.chat(view, ":prove")
            )
            addItem(proofMenu, "Run Sledgehammer")(_ =>
              SledgehammerAction.run(view)
            )
            addItem(proofMenu, "Run Nitpick")(_ =>
              CounterexampleFinderAction.run(
                view,
                CounterexampleFinderAction.Nitpick
              )
            )
            addItem(proofMenu, "Run Quickcheck")(_ =>
              CounterexampleFinderAction.run(
                view,
                CounterexampleFinderAction.Quickcheck
              )
            )
            addItem(proofMenu, "Try Methods")(_ => TryMethodsAction.run(view))
            proofMenu.addSeparator()
            addItem(proofMenu, "Trace Simp")(_ =>
              TraceSimplifierAction.trace(view, "simp")
            )
            addItem(proofMenu, "Trace Auto")(_ =>
              TraceSimplifierAction.trace(view, "auto")
            )
            addItem(proofMenu, "Print Context")(_ =>
              PrintContextAction.run(view)
            )
          }

          if (ctx.hasSelection)
            addItem(proofMenu, "Extract Lemma")(_ =>
              selection.foreach(ExtractLemmaAction.extract(view, _))
            )

          if (ctx.hasApplyProof) {
            addItem(proofMenu, "Refactor to Isar") { _ =>
              val block = selection
                .filter(_.trim.nonEmpty)
                .orElse(ProofExtractor.getProofBlockAtOffset(buffer, offset))
              block.foreach(RefactorAction.refactor(view, _))
            }
          }

          menu.add(proofMenu)
        }

        // === Search ===
        if (ctx.iqAvailable) {
          addItem(menu, "Find Theorems") { _ =>
            val pattern = selection.filter(_.trim.nonEmpty)
            FindTheoremsAction.findTheorems(view, pattern)
          }
        }

        // === Generation ===
        if (ctx.hasCommand || ctx.hasSelection) {
          val genMenu = new JMenu("Generate")

          if (ctx.onDefinition) {
            val defText = CommandExtractor.getCommandAtOffset(buffer, offset)
            addItem(genMenu, "Intro Rule") { _ =>
              defText.foreach(t => GenerateRulesAction.generateIntro(view, t))
            }
            addItem(genMenu, "Elim Rule") { _ =>
              defText.foreach(t => GenerateRulesAction.generateElim(view, t))
            }
            addItem(genMenu, "Test Cases") { _ =>
              defText.foreach(t => GenerateTestsAction.generate(view, t))
            }
          }

          val commandForDoc =
            CommandExtractor.getCommandAtOffset(buffer, offset)
          // Use PIDE span name for command type detection — no string splitting
          val commandType =
            GenerateDocAction.detectCommandTypeAtOffset(buffer, offset)
          if (commandType.isDefined) {
            addItem(genMenu, "Doc Comment") { _ =>
              commandForDoc.foreach(text =>
                GenerateDocAction.generate(
                  view,
                  text,
                  commandType.getOrElse("command")
                )
              )
            }
          }

          if (ctx.onDefinition)
            addItem(genMenu, "Suggest Name")(_ =>
              SuggestNameAction.suggestName(view)
            )
          if (ctx.hasSelection || ctx.inProof)
            addItem(genMenu, "Tidy Up")(_ => TidyAction.tidy(view))

          if (ctx.hasSelection)
            addItem(genMenu, "Generate Tactic")(_ =>
              selection.foreach(SuggestTacticAction.suggest(view, _))
            )

          menu.add(genMenu)
        }

        // === Analysis ===
        if (ctx.hasCommand)
          addItem(menu, "Analyze Patterns")(_ =>
            AnalyzePatternsAction.analyze(view)
          )

        Array(menu)
      }
    }
  }

  private def addItem(
      menu: JMenu,
      label: String
  )(action: Unit => Unit): Unit = {
    val item = new JMenuItem(label)
    item.addActionListener(_ => action(()))
    menu.add(item)
  }
}
