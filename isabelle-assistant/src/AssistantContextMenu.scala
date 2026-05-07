/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.gui.DynamicContextMenuService
import org.gjt.sp.jedit.textarea.JEditTextArea
import java.awt.event.MouseEvent
import javax.swing.{JMenu, JMenuItem}

/** Pure decisions about which menu groups/items a given MenuContext.Context
  * should expose. Split out of the class body so it can be exercised in
  * unit tests without standing up a Swing JEditTextArea. */
private[assistant] object AssistantContextMenuEnablement {
  import MenuContext.Context

  def showExplain(ctx: Context): Boolean = ctx.hasCommand || ctx.hasSelection
  def showExplainError(ctx: Context): Boolean = ctx.onError
  def showShowType(ctx: Context): Boolean = ctx.hasTypeInfo

  def showProofSubmenu(ctx: Context): Boolean = ctx.inProof
  def showIQProofItems(ctx: Context): Boolean = ctx.inProof && ctx.iqAvailable
  def showExtractLemma(ctx: Context): Boolean = ctx.inProof && ctx.hasSelection
  def showRefactorToIsar(ctx: Context): Boolean = ctx.inProof && ctx.hasApplyProof

  def showFindTheoremsTop(ctx: Context): Boolean = ctx.iqAvailable

  def showGenerateSubmenu(ctx: Context): Boolean = ctx.hasCommand || ctx.hasSelection
  def showGenerateOnDefinition(ctx: Context): Boolean =
    showGenerateSubmenu(ctx) && ctx.onDefinition
  def showSuggestName(ctx: Context): Boolean =
    showGenerateSubmenu(ctx) && ctx.onDefinition
  def showTidyUp(ctx: Context): Boolean =
    showGenerateSubmenu(ctx) && (ctx.hasSelection || ctx.inProof)
  def showGenerateTactic(ctx: Context): Boolean =
    showGenerateSubmenu(ctx) && ctx.hasSelection

  def showAnalyzePatterns(ctx: Context): Boolean = ctx.hasCommand
}

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
        val ctx = MenuContext.analyzeLocal(view, buffer, offset, selection)
        val menu = new JMenu("Isabelle Assistant")

        import AssistantContextMenuEnablement._

        // === Understanding ===
        val understandMenu = new JMenu("Understanding")
        if (showExplain(ctx)) {
          addItem(understandMenu, "Explain") { _ =>
            // Selection is EDT-safe; if no selection, resolve the command
            // on a background thread (CommandExtractor goes to I/Q MCP).
            selection.filter(_.trim.nonEmpty) match {
              case Some(t) => ExplainAction.explain(view, t)
              case None =>
                AssistantDockable.setStatus("Resolving command…")
                val _ = Isabelle_Thread.fork(name = "menu-explain-resolve") {
                  val t = CommandExtractor.getCommandAtOffset(buffer, offset)
                  GUI_Thread.later {
                    AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                    t match {
                      case Some(cmd) => ExplainAction.explain(view, cmd)
                      case None =>
                        AssistantDockable.respondInChat(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
                    }
                  }
                }
            }
          }
        }

        if (showExplainError(ctx))
          addItem(understandMenu, "Explain Error")(_ =>
            ExplainErrorAction.explainError(view)
          )

        if (showShowType(ctx))
          addItem(understandMenu, "Show Type")(_ =>
            ShowTypeAction.showType(view)
          )

        addItem(understandMenu, "Summarize Theory")(_ =>
          SummarizeTheoryAction.summarize(view)
        )
        menu.add(understandMenu)

        // === Proof (only in proof context) ===
        if (showProofSubmenu(ctx)) {
          val proofMenu = new JMenu("Proof")

          addItem(proofMenu, "Suggest Proof Step")(_ =>
            SuggestAction.suggest(view, buffer, offset)
          )
          addItem(proofMenu, "Suggest Strategy")(_ =>
            SuggestStrategyAction.suggest(view)
          )

          if (showIQProofItems(ctx)) {
            proofMenu.addSeparator()
            addItem(proofMenu, "Find Theorems for Goal")(_ =>
              FindTheoremsAction.findTheoremsForGoal(view)
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
            addItem(proofMenu, "Suggest Methods")(_ => TryMethodsAction.run(view))
            proofMenu.addSeparator()
            addItem(proofMenu, "Trace Simplifier")(_ =>
              TraceSimplifierAction.trace(view, "simp")
            )
            addItem(proofMenu, "Trace Auto Method")(_ =>
              TraceSimplifierAction.trace(view, "auto")
            )
            addItem(proofMenu, "Print Context")(_ =>
              PrintContextAction.run(view)
            )
          }

          if (showExtractLemma(ctx))
            addItem(proofMenu, "Extract Lemma")(_ =>
              selection.foreach(ExtractLemmaAction.extract(view, _))
            )

          if (showRefactorToIsar(ctx)) {
            addItem(proofMenu, "Refactor to Isar") { _ =>
              selection.filter(_.trim.nonEmpty) match {
                case Some(t) => RefactorAction.refactor(view, t)
                case None =>
                  AssistantDockable.setStatus("Locating proof block…")
                  val _ = Isabelle_Thread.fork(name = "menu-refactor-resolve") {
                    val block = ProofExtractor.getProofBlockAtOffset(buffer, offset)
                    GUI_Thread.later {
                      AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                      block.foreach(RefactorAction.refactor(view, _))
                    }
                  }
              }
            }
          }

          val _ = menu.add(proofMenu)
        }

        // === Search ===
        if (showFindTheoremsTop(ctx)) {
          addItem(menu, "Find Theorems") { _ =>
            val pattern = selection.filter(_.trim.nonEmpty)
            FindTheoremsAction.findTheorems(view, pattern)
          }
        }

        // === Generation ===
        if (showGenerateSubmenu(ctx)) {
          val genMenu = new JMenu("Generate")

          if (showGenerateOnDefinition(ctx)) {
            // All four of these do a CommandExtractor MCP call. Route them
            // through a shared helper that forks to a background thread
            // first, so clicking the menu does not freeze jEdit.
            addItem(genMenu, "Generate Intro Rule") { _ =>
              forkResolveCommand(buffer, offset) {
                case Some(t) => GenerateRulesAction.generateIntro(view, t)
                case None => AssistantDockable.respondInChat(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
              }
            }
            addItem(genMenu, "Generate Elim Rule") { _ =>
              forkResolveCommand(buffer, offset) {
                case Some(t) => GenerateRulesAction.generateElim(view, t)
                case None => AssistantDockable.respondInChat(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
              }
            }
            addItem(genMenu, "Generate Test Cases") { _ =>
              forkResolveCommand(buffer, offset) {
                case Some(t) => GenerateTestsAction.generate(view, t)
                case None => AssistantDockable.respondInChat(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
              }
            }
            addItem(genMenu, "Generate Doc Comment") { _ =>
              AssistantDockable.setStatus("Resolving command…")
              val _ = Isabelle_Thread.fork(name = "menu-gendoc-resolve") {
                val commandText = CommandExtractor.getCommandAtOffset(buffer, offset)
                val commandType = GenerateDocAction.detectCommandTypeAtOffset(buffer, offset)
                GUI_Thread.later {
                  AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                  commandText match {
                    case Some(text) =>
                      GenerateDocAction.generate(
                        view,
                        text,
                        commandType.getOrElse("command")
                      )
                    case None =>
                      AssistantDockable.respondInChat(AssistantConstants.UIText.NO_COMMAND_AT_CURSOR)
                  }
                }
              }
            }
          }

          if (showSuggestName(ctx))
            addItem(genMenu, "Suggest Name")(_ =>
              SuggestNameAction.suggestName(view)
            )
          if (showTidyUp(ctx))
            addItem(genMenu, "Tidy Up")(_ => TidyAction.tidy(view))

          if (showGenerateTactic(ctx))
            addItem(genMenu, "Generate Tactic")(_ =>
              selection.foreach(SuggestTacticAction.suggest(view, _))
            )

          val _ = menu.add(genMenu)
        }

        // === Analysis ===
        if (showAnalyzePatterns(ctx))
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
    val _ = menu.add(item)
  }

  /** Fork a background thread, resolve the command at `offset`, and run
    * `onResult` on the EDT with the result. Used by menu items whose action
    * body needs the command source but can't block the EDT during the MCP
    * round trip.
    */
  private def forkResolveCommand(
      buffer: org.gjt.sp.jedit.buffer.JEditBuffer,
      offset: Int
  )(onResult: Option[String] => Unit): Unit = {
    AssistantDockable.setStatus("Resolving command…")
    val _ = Isabelle_Thread.fork(name = "menu-resolve-command") {
      val t = CommandExtractor.getCommandAtOffset(buffer, offset)
      GUI_Thread.later {
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        onResult(t)
      }
    }
  }
}
