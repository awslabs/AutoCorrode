/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.awt.{BorderLayout, FlowLayout}
import java.awt.event.{ActionEvent, ActionListener, MouseAdapter, MouseEvent}
import javax.swing.{
  JCheckBox,
  JComboBox,
  JLabel,
  JPanel,
  JScrollPane,
  JTable,
  JTextField
}
import javax.swing.table.AbstractTableModel

import scala.collection.mutable
import scala.annotation.unused

import isabelle.{Command, Document, GUI_Thread, Markup, Session, Text}
import isabelle.jedit.PIDE

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DefaultFocusComponent

class FineGrainedTimingDockable(view: View, @unused position: String)
extends JPanel(new BorderLayout) with DefaultFocusComponent {
  private val ScopeCommand = "Command"
  private val ScopeProof = "Proof"
  private val ScopeTheory = "Theory"
  private val ScopeGlobal = "Global"
  private val CallsView = "Calls"
  private val AggregateView = "Aggregate"

  private val columns =
    Vector("Location", "Name", "Outcome", "Count", "Total", "Average",
      "p50", "p90", "p99", "Min", "Max", "CPU", "GC")

  private final case class CommandTiming(
      command: Command,
      index: Int,
      theory: String,
      invocations: Vector[FineGrainedTiming.Invocation]
  )

  private sealed trait TimingRow {
    def command: Command
    def values: Vector[String]
  }

  private final case class InvocationRow(
      command: Command,
      location: String,
      invocation: FineGrainedTiming.Invocation
  ) extends TimingRow {
    def values: Vector[String] = {
      val sampleCount = invocation.samples.iterator.map(_.aggregate.count).sum
      val elapsed = invocation.timing.map(timing => formatMicros(timing.elapsedMicros))
      val cpu = invocation.timing.map(timing => formatMicros(timing.cpuMicros))
      val gc = invocation.timing.map(timing => formatMicros(timing.gcMicros))
      Vector(
        location,
        invocation.method,
        if (invocation.success) "success" else "failure",
        sampleCount.toString,
        elapsed.getOrElse(""),
        "",
        "",
        "",
        "",
        "",
        "",
        cpu.getOrElse(""),
        gc.getOrElse("")
      )
    }
  }

  private final case class AggregateRow(
      command: Command,
      location: String,
      key: FineGrainedTiming.SampleKey,
      aggregate: FineGrainedTiming.Aggregate
  ) extends TimingRow {
    def values: Vector[String] =
      Vector(
        location,
        key.name,
        if (key.success) "success" else "failure",
        aggregate.count.toString,
        formatMicros(aggregate.timing.elapsedMicros),
        formatMicros(aggregate.averageElapsedMicros),
        formatMicros(aggregate.percentileElapsedMicros(0.50)),
        formatMicros(aggregate.percentileElapsedMicros(0.90)),
        formatMicros(aggregate.percentileElapsedMicros(0.99)),
        formatMicros(aggregate.minElapsedMicros),
        formatMicros(aggregate.maxElapsedMicros),
        formatMicros(aggregate.timing.cpuMicros),
        formatMicros(aggregate.timing.gcMicros)
      )
  }

  private final class TimingTableModel extends AbstractTableModel {
    private var rows = Vector.empty[TimingRow]

    def update(newRows: Vector[TimingRow]): Unit = {
      rows = newRows
      fireTableDataChanged()
    }

    def row(index: Int): Option[TimingRow] = rows.lift(index)

    override def getRowCount: Int = rows.length
    override def getColumnCount: Int = columns.length
    override def getColumnName(column: Int): String = columns(column)
    override def getValueAt(row: Int, column: Int): Object = rows(row).values(column)
  }

  private val tableModel = new TimingTableModel
  private val table = new JTable(tableModel)
  table.setAutoCreateRowSorter(true)
  table.setFillsViewportHeight(true)
  table.addMouseListener(new MouseAdapter {
    override def mouseClicked(event: MouseEvent): Unit = {
      if (event.getClickCount == 2) {
        val viewRow = table.rowAtPoint(event.getPoint)
        if (viewRow >= 0) {
          val modelRow = table.convertRowIndexToModel(viewRow)
          for {
            row <- tableModel.row(modelRow)
            hyperlink <- PIDE.editor.hyperlink_command(
              PIDE.session.snapshot(), row.command.id, focus = true)
          } hyperlink.follow(view)
        }
      }
    }
  })

  private val scopeSelector =
    new JComboBox[String](Array(ScopeCommand, ScopeProof, ScopeTheory, ScopeGlobal))
  private val viewSelector =
    new JComboBox[String](Array(AggregateView, CallsView))
  private val categorySelector =
    new JComboBox[String](
      Array("all", "branch", "step", "call", "clarsimp", "seplog",
        "transaction", "setup", "other")
    )
  private val showSuccess = new JCheckBox("Success", true)
  private val showFailure = new JCheckBox("Failure", true)
  private val thresholdField = new JTextField("0.000", 6)
  private val currentLabel = new JLabel("No active theory")

  private val refreshListener = new ActionListener {
    override def actionPerformed(event: ActionEvent): Unit = {
      val _ = event
      refresh()
    }
  }
  scopeSelector.addActionListener(refreshListener)
  viewSelector.addActionListener(refreshListener)
  categorySelector.addActionListener(refreshListener)
  showSuccess.addActionListener(refreshListener)
  showFailure.addActionListener(refreshListener)
  thresholdField.addActionListener(refreshListener)

  private val controls = new JPanel(new FlowLayout(FlowLayout.LEFT, 6, 2))
  controls.add(new JLabel("Scope:"))
  controls.add(scopeSelector)
  controls.add(new JLabel("View:"))
  controls.add(viewSelector)
  controls.add(new JLabel("Category:"))
  controls.add(categorySelector)
  controls.add(showSuccess)
  controls.add(showFailure)
  controls.add(new JLabel("Threshold (s):"))
  controls.add(thresholdField)
  controls.add(currentLabel)

  add(controls, BorderLayout.NORTH)
  add(new JScrollPane(table), BorderLayout.CENTER)

  private var globalTimings =
    Map.empty[Document.Node.Name, Vector[CommandTiming]]

  private def refresh(
      changedNodes: Option[Set[Document.Node.Name]] = None
  ): Unit = {
    GUI_Thread.require {}
    val sessionSnapshot = PIDE.session.snapshot()
    if (globalTimings.nonEmpty) updateGlobalTimings(sessionSnapshot, changedNodes)

    if (scopeSelector.getSelectedItem.toString == ScopeGlobal) {
      if (globalTimings.isEmpty) updateGlobalTimings(sessionSnapshot, None)
      val selected = globalTimings.toVector.sortBy(_._1.theory).flatMap(_._2)
      val theoryCount =
        selected.iterator.filter(_.invocations.nonEmpty).map(_.theory).toSet.size
      val location = s"Global: $theoryCount theories"
      currentLabel.setText(location)
      tableModel.update(makeRows(selected, location))
    } else PIDE.editor.current_node_snapshot(view) match {
      case Some(snapshot) if !snapshot.is_outdated =>
        val node = snapshot.node
        val commandPairs = node.command_iterator().toVector
        val scopeCommands =
          commandPairs.map { case (command, offset) =>
            FineGrainedTimingScope.ScopeCommand(command.span.name, offset, command.length)
          }
        val proofs = FineGrainedTimingScope.partitionNamedProofs(scopeCommands)
        val currentCommand = PIDE.editor.current_command(view, snapshot)
        val currentIndex =
          currentCommand.flatMap(command => commandPairs.indexWhere(_._1.id == command.id) match {
            case index if index >= 0 => Some(index)
            case _ => None
          })
        val timings =
          commandPairs.zipWithIndex.map { case ((command, offset), index) =>
            CommandTiming(
              command, index, snapshot.node_name.theory,
              invocations(snapshot, command, offset))
          }
        val selected = selectedCommands(timings, currentIndex, proofs)
        val location = selectedLocation(snapshot, currentIndex, proofs, commandPairs)
        currentLabel.setText(location)
        tableModel.update(makeRows(selected, location))
      case _ =>
        currentLabel.setText("No active theory")
        tableModel.update(Vector.empty)
    }
  }

  private def updateGlobalTimings(
      snapshot: Document.Snapshot,
      changedNodes: Option[Set[Document.Node.Name]]
  ): Unit = {
    val domain =
      snapshot.version.nodes.names_iterator
        .filter(name => name.is_theory && !PIDE.resources.loaded_theory(name))
        .toSet
    val refreshNodes =
      if (globalTimings.isEmpty) domain
      else changedNodes.getOrElse(Set.empty).intersect(domain)
    val retained = globalTimings.filter { case (name, _) => domain.contains(name) }
    val refreshed =
      refreshNodes.iterator.map { name =>
        val nodeSnapshot = snapshot.switch(name)
        val timings =
          nodeSnapshot.node.command_iterator().zipWithIndex.flatMap {
            case ((command, offset), index) =>
              val reports = invocations(nodeSnapshot, command, offset)
              if (reports.isEmpty) None
              else Some(CommandTiming(command, index, name.theory, reports))
          }.toVector
        name -> timings
      }.toMap
    globalTimings = retained ++ refreshed
  }

  private def invocations(
      snapshot: Document.Snapshot,
      command: Command,
      offset: Int
  ): Vector[FineGrainedTiming.Invocation] = {
    val range = Text.Range(offset, offset + command.length)
    snapshot
      .select[FineGrainedTiming.Invocation](
        range,
        Markup.Elements(FineGrainedTiming.ReportMarkup),
        _ => {
          case Text.Info(_, tree) => FineGrainedTiming.decode(tree)
        }
      )
      .iterator
      .map(_.info)
      .toVector
      .distinct
  }

  private def selectedCommands(
      timings: Vector[CommandTiming],
      currentIndex: Option[Int],
      proofs: IndexedSeq[FineGrainedTimingScope.NamedProof]
  ): Vector[CommandTiming] =
    scopeSelector.getSelectedItem.toString match {
      case ScopeCommand =>
        currentIndex.flatMap(timings.lift).toVector
      case ScopeProof =>
        currentIndex
          .flatMap(index => FineGrainedTimingScope.namedProofAt(proofs, index))
          .map(proof => timings.slice(proof.startIndex, proof.endIndex + 1))
          .getOrElse(Vector.empty)
      case ScopeTheory =>
        timings
      case ScopeGlobal =>
        timings
      case _ =>
        Vector.empty
    }

  private def selectedLocation(
      snapshot: Document.Snapshot,
      currentIndex: Option[Int],
      proofs: IndexedSeq[FineGrainedTimingScope.NamedProof],
      commands: Vector[(Command, Int)]
  ): String =
    scopeSelector.getSelectedItem.toString match {
      case ScopeCommand =>
        currentIndex
          .flatMap(commands.lift)
          .map { case (command, _) => s"Command: ${command.span.name}" }
          .getOrElse("Command: none")
      case ScopeProof =>
        currentIndex
          .flatMap(index => FineGrainedTimingScope.namedProofAt(proofs, index))
          .flatMap(proof => commands.lift(proof.startIndex))
          .map { case (command, _) => s"Proof: ${proofName(command)}" }
          .getOrElse("Proof: none")
      case ScopeTheory =>
        s"Theory: ${snapshot.node_name.theory}"
      case ScopeGlobal =>
        "Global"
      case _ =>
        ""
    }

  private def makeRows(
      commands: Vector[CommandTiming],
      location: String
  ): Vector[TimingRow] = {
    val threshold = thresholdMicros
    val successEnabled = showSuccess.isSelected
    val failureEnabled = showFailure.isSelected
    if (viewSelector.getSelectedItem.toString == CallsView) {
      commands.iterator
        .flatMap(command =>
          command.invocations.iterator.map(invocation =>
            InvocationRow(
              command.command,
              if (scopeSelector.getSelectedItem.toString == ScopeGlobal)
                s"${command.theory}: ${command.command.span.name}"
              else location,
              invocation)))
        .filter(row => if (row.invocation.success) successEnabled else failureEnabled)
        .filter(row =>
          row.invocation.timing.forall(_.elapsedMicros.toDouble >= threshold))
        .toVector
        .sortBy(row => -row.invocation.timing.map(_.elapsedMicros).getOrElse(0L))
    } else {
      val merged =
        mutable.LinkedHashMap.empty[
          FineGrainedTiming.SampleKey,
          (FineGrainedTiming.Aggregate, Command)
        ]
      commands.foreach { command =>
        FineGrainedTiming.aggregate(command.invocations).foreach { case (key, aggregate) =>
          merged.updateWith(key) {
            case Some((existing, firstCommand)) =>
              Some((existing + aggregate, firstCommand))
            case None =>
              Some((aggregate, command.command))
          }
        }
      }
      merged.iterator
        .map { case (key, (aggregate, command)) =>
          AggregateRow(command, location, key, aggregate)
        }
        .filter(row => if (row.key.success) successEnabled else failureEnabled)
        .filter(row => categoryMatches(row.key.name))
        .filter(_.aggregate.timing.elapsedMicros.toDouble >= threshold)
        .toVector
        .sortBy(row => -row.aggregate.timing.elapsedMicros)
    }
  }

  private def categoryMatches(name: String): Boolean = {
    val selected = categorySelector.getSelectedItem.toString
    selected == "all" || category(name) == selected
  }

  private def category(name: String): String = {
    val lower = name.toLowerCase
    if (lower.contains("clarsimp")) "clarsimp"
    else if (lower.contains("seplog") || lower.contains("aentails")) "seplog"
    else if (lower.contains("transaction")) "transaction"
    else if (lower.contains("call")) "call"
    else if (lower.contains("setup") || lower.contains("instantiation")) "setup"
    else if (lower.contains("step")) "step"
    else if (lower.contains("branch")) "branch"
    else "other"
  }

  private def proofName(command: Command): String = {
    val pattern =
      """(?s)^\s*(?:lemma|theorem|corollary|proposition|schematic_goal)\s+([A-Za-z0-9_']+)""".r
    pattern.findFirstMatchIn(command.source).map(_.group(1))
      .getOrElse(command.span.name)
  }

  private def thresholdMicros: Double =
    try math.max(0.0, thresholdField.getText.trim.toDouble) * 1000000.0
    catch { case _: NumberFormatException => 0.0 }

  private def formatMicros(micros: Long): String =
    f"${micros.toDouble / 1000000.0}%.6fs"

  private def formatMicros(micros: Double): String =
    f"${micros / 1000000.0}%.6fs"

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        GUI_Thread.later { refresh(Some(changed.nodes)) }
      case Session.Caret_Focus =>
        GUI_Thread.later { refresh() }
      case _ =>
    }

  override def addNotify(): Unit = {
    super.addNotify()
    PIDE.session.commands_changed += main
    PIDE.session.caret_focus += main
    refresh()
  }

  override def removeNotify(): Unit = {
    PIDE.session.caret_focus -= main
    PIDE.session.commands_changed -= main
    super.removeNotify()
  }

  def focusOnDefaultComponent(): Unit = table.requestFocus()
}
