/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.awt.{BorderLayout, FlowLayout, GridLayout}
import java.awt.event.{ActionEvent, ActionListener, MouseAdapter, MouseEvent}
import java.util.Locale
import javax.swing.{
  JButton,
  JCheckBox,
  JComboBox,
  JLabel,
  JPanel,
  JOptionPane,
  JScrollPane,
  JTextField
}
import javax.swing.event.{TreeExpansionEvent, TreeWillExpandListener}
import javax.swing.table.TableColumn

import scala.annotation.unused

import isabelle.{
  Command,
  Document,
  Document_ID,
  Exn,
  Future,
  GUI_Thread,
  Line,
  Markup,
  Output,
  Session,
  Synchronized,
  Text
}
import isabelle.jedit.PIDE

import org.gjt.sp.jedit.jEdit
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
  private val VisibleColumnsProperty = "fine-grained-timing.visible-columns"
  private val TimingDigitsProperty = "fine-grained-timing.timing-digits"
  private val DefaultTimingDigits = 3
  private val MinTimingDigits = 0
  private val MaxTimingDigits = 9

  private final case class ColumnDescriptor(
      id: String,
      title: String,
      defaultVisible: Boolean
  )

  private val columnDescriptors = Vector(
    ColumnDescriptor("location", "Location", defaultVisible = true),
    ColumnDescriptor("name", "Name", defaultVisible = true),
    ColumnDescriptor("outcome", "Outcome", defaultVisible = true),
    ColumnDescriptor("count", "Count", defaultVisible = true),
    ColumnDescriptor("total", "Total", defaultVisible = true),
    ColumnDescriptor("average", "Average", defaultVisible = false),
    ColumnDescriptor("p50", "p50", defaultVisible = true),
    ColumnDescriptor("p90", "p90", defaultVisible = true),
    ColumnDescriptor("p99", "p99", defaultVisible = true),
    ColumnDescriptor("min", "Min", defaultVisible = false),
    ColumnDescriptor("max", "Max", defaultVisible = true)
  )
  private val columnIndex =
    columnDescriptors.iterator.zipWithIndex.map { case (column, index) =>
      column.id -> index
    }.toMap

  private final case class CommandTiming(
      command: Command,
      theory: String,
      proof: Option[String],
      proofStart: Option[Command],
      line: Int,
      invocations: Vector[FineGrainedTiming.Invocation]
  )

  private final case class ProofContext(name: String, start: Command)

  private final case class IndexOptions(
      view: FineGrainedTimingHierarchy.View,
      nameFilter: String,
      showSuccess: Boolean,
      showFailure: Boolean
  )

  private final case class DisplayOptions(
      expandedNodes: Set[String],
      timingDigits: Int,
      thresholdMicros: Double
  )

  private final case class RenderState(
      index: FineGrainedTimingHierarchy.Index[CommandTiming],
      scope: String,
      view: FineGrainedTimingHierarchy.View,
      location: String,
      navigation: NavigationTarget
  )

  private final case class GlobalRefreshResult(
      renderState: RenderState,
      tree: Vector[FineGrainedTimingTreeTable.Data],
      timings: Map[Document.Node.Name, Vector[CommandTiming]],
      indexes: Map[
        Document.Node.Name,
        FineGrainedTimingHierarchy.Index[CommandTiming]
      ],
      indexOptions: IndexOptions,
      domain: Set[Document.Node.Name],
      refreshedNodes: Set[Document.Node.Name],
      version: Document_ID.Version
  )

  private sealed trait NavigationTarget {
    def follow(snapshot: Document.Snapshot): Unit
  }

  private case object NoNavigation extends NavigationTarget {
    override def follow(snapshot: Document.Snapshot): Unit = {
      val _ = snapshot
    }
  }

  private final case class TheoryNavigation(name: Document.Node.Name)
      extends NavigationTarget {
    override def follow(snapshot: Document.Snapshot): Unit = {
      val _ = snapshot
      PIDE.editor.goto_file(view, name.node, line = 0, focus = true)
    }
  }

  private final case class CommandNavigation(command: Command)
      extends NavigationTarget {
    override def follow(snapshot: Document.Snapshot): Unit =
      PIDE.editor.hyperlink_command(
        snapshot,
        command.id,
        focus = true
      ).foreach(_.follow(view))
  }

  private sealed trait TimingRow {
    def navigation: NavigationTarget
    def nodeId: String
    def values: Vector[String]
  }

  private final case class DetailRow(
      navigation: NavigationTarget,
      nodeId: String,
      values: Vector[String]
  ) extends TimingRow

  private final case class GroupRow(
      navigation: NavigationTarget,
      nodeId: String,
      values: Vector[String]
  ) extends TimingRow

  private val treeTableColumns =
    new FineGrainedTimingTreeTable.Columns {
      override def count: Int = columnDescriptors.length
      override def name(column: Int): String =
        columnDescriptors(column).title
      override def columnClass(column: Int): Class[?] =
        if (column == columnIndex("location"))
          classOf[FineGrainedTimingTreeTable.TreeColumn]
        else classOf[String]
      override def valueAt(value: AnyRef, column: Int): AnyRef =
        value match {
          case row: TimingRow => row.values(column)
          case FineGrainedTimingTreeTable.Loading =>
            if (column == columnIndex("location")) "Loading..." else ""
          case _ => ""
        }
    }
  private val treeModel =
    new FineGrainedTimingTreeTable.Model(treeTableColumns)
  private val table =
    new FineGrainedTimingTreeTable.Table(
      treeModel,
      columnIndex("location")
    )
  table.setAutoCreateColumnsFromModel(false)
  table.setFillsViewportHeight(true)
  private var visibleColumnIds = loadVisibleColumnIds()
  private var expandedNodes = Set.empty[String]
  private var restoringTreeExpansion = false
  applyVisibleColumns()
  table.tree.addTreeWillExpandListener(new TreeWillExpandListener {
    override def treeWillExpand(event: TreeExpansionEvent): Unit =
      if (!restoringTreeExpansion) {
        treeModel.value(event.getPath.getLastPathComponent) match {
          case group: GroupRow if !expandedNodes.contains(group.nodeId) =>
            expandedNodes += group.nodeId
            rerenderCurrent()
          case _ =>
        }
      }

    override def treeWillCollapse(event: TreeExpansionEvent): Unit =
      if (!restoringTreeExpansion) {
        treeModel.value(event.getPath.getLastPathComponent) match {
          case group: GroupRow if expandedNodes.contains(group.nodeId) =>
            expandedNodes -= group.nodeId
            rerenderCurrent()
          case _ =>
        }
      }
  })
  table.addMouseListener(new MouseAdapter {
    override def mouseClicked(event: MouseEvent): Unit = {
      val viewRow = table.rowAtPoint(event.getPoint)
      if (event.getClickCount == 2 && viewRow >= 0) {
        for {
          value <- table.valueAtRow(viewRow)
          row <- value match {
            case timingRow: TimingRow => Some(timingRow)
            case _ => None
          }
        } row.navigation.follow(PIDE.session.snapshot())
      }
    }
  })

  private val scopeSelector =
    new JComboBox[String](Array(ScopeCommand, ScopeProof, ScopeTheory, ScopeGlobal))
  private val viewSelector =
    new JComboBox[String](Array(AggregateView, CallsView))
  private val columnsButton = new JButton("Columns...")
  private val filterField = new JTextField("", 14)
  private val showSuccess = new JCheckBox("Success", true)
  private val showFailure = new JCheckBox("Failure", true)
  private val thresholdField = new JTextField("0.000", 6)
  private var timingDigits = loadTimingDigits()
  private val timingDigitsField = new JTextField(timingDigits.toString, 2)

  private val refreshListener = new ActionListener {
    override def actionPerformed(event: ActionEvent): Unit = {
      val _ = event
      refresh()
    }
  }
  scopeSelector.addActionListener(refreshListener)
  viewSelector.addActionListener(refreshListener)
  columnsButton.addActionListener(new ActionListener {
    override def actionPerformed(event: ActionEvent): Unit = {
      val _ = event
      showColumnDialog()
    }
  })
  filterField.addActionListener(refreshListener)
  showSuccess.addActionListener(refreshListener)
  showFailure.addActionListener(refreshListener)
  thresholdField.addActionListener(new ActionListener {
    override def actionPerformed(event: ActionEvent): Unit = {
      val _ = event
      if (currentRenderState.nonEmpty) rerenderCurrent() else refresh()
    }
  })
  timingDigitsField.addActionListener(new ActionListener {
    override def actionPerformed(event: ActionEvent): Unit = {
      val _ = event
      updateTimingDigits()
    }
  })

  private val controls = new JPanel(new FlowLayout(FlowLayout.LEFT, 6, 2))
  controls.add(new JLabel("Scope:"))
  controls.add(scopeSelector)
  controls.add(new JLabel("View:"))
  controls.add(viewSelector)
  columnsButton.setToolTipText("Choose which timing columns are visible")
  controls.add(columnsButton)
  controls.add(new JLabel("Filter:"))
  filterField.setToolTipText(
    "Show rows whose method or sample name contains this text"
  )
  controls.add(filterField)
  controls.add(showSuccess)
  controls.add(showFailure)
  controls.add(new JLabel("Threshold (s):"))
  controls.add(thresholdField)
  controls.add(new JLabel("Digits:"))
  timingDigitsField.setToolTipText(
    "Number of fractional digits shown for timing values (0-9)"
  )
  controls.add(timingDigitsField)

  add(controls, BorderLayout.NORTH)
  add(new JScrollPane(table), BorderLayout.CENTER)

  private var globalTimings =
    Map.empty[Document.Node.Name, Vector[CommandTiming]]
  private var globalIndexes =
    Map.empty[
      Document.Node.Name,
      FineGrainedTimingHierarchy.Index[CommandTiming]
    ]
  private var globalIndexOptions = Option.empty[IndexOptions]
  private var globalVersion = Option.empty[Document_ID.Version]
  private var dirtyGlobalNodes = Set.empty[Document.Node.Name]
  private var currentRenderState = Option.empty[RenderState]
  private var refreshGeneration = 0L
  private val futureRefresh =
    Synchronized[Option[Future[Unit]]](None)

  private def refresh(
      changedNodes: Option[Set[Document.Node.Name]] = None
  ): Unit = {
    GUI_Thread.require {}
    changedNodes.foreach(nodes => dirtyGlobalNodes ++= nodes)
    cancelRefresh()

    val scope = scopeSelector.getSelectedItem.toString
    val indexOptions = captureIndexOptions()
    val displayOptions = captureDisplayOptions()
    if (scope == ScopeGlobal) {
      startGlobalRefresh(
        PIDE.session.snapshot(),
        indexOptions,
        displayOptions
      )
    } else {
      PIDE.editor.current_node_snapshot(view) match {
        case Some(snapshot) if !snapshot.is_outdated =>
          val currentCommandId =
            PIDE.editor.current_command(view, snapshot).map(_.id)
          startLocalRefresh(
            snapshot,
            currentCommandId,
            scope,
            indexOptions,
            displayOptions
          )
        case _ =>
          updateTree(Vector.empty)
      }
    }
  }

  private def startLocalRefresh(
      snapshot: Document.Snapshot,
      currentCommandId: Option[Document_ID.Command],
      scope: String,
      indexOptions: IndexOptions,
      displayOptions: DisplayOptions
  ): Unit = {
    forkRefresh {
      val node = snapshot.node
      val commandPairs = node.command_iterator().toVector
      val scopeCommands =
        commandPairs.map { case (command, offset) =>
          FineGrainedTimingScope.ScopeCommand(
            command.span.name,
            offset,
            command.length
          )
        }
      val proofs = FineGrainedTimingScope.partitionNamedProofs(scopeCommands)
      val proofContexts = proofContextsByCommand(proofs, commandPairs)
      val currentIndex =
        currentCommandId.flatMap { id =>
          commandPairs.indexWhere(_._1.id == id) match {
            case index if index >= 0 => Some(index)
            case _ => None
          }
        }
      val selectedIndices =
        selectedCommandIndices(scope, currentIndex, proofs, commandPairs.length)
      val lineDocument = Line.Document(node.source)
      val timings =
        selectedIndices.iterator.flatMap { index =>
          Exn.Interrupt.expose()
          commandPairs.lift(index).flatMap { case (command, offset) =>
            val reports = invocations(snapshot, command, offset)
            if (reports.isEmpty) None
            else {
              val proofContext = proofContexts(index)
              Some(CommandTiming(
                command,
                snapshot.node_name.theory,
                proofContext.map(_.name),
                proofContext.map(_.start),
                lineDocument.position(offset).line + 1,
                reports
              ))
            }
          }
        }.toVector
      val location =
        selectedLocation(
          snapshot,
          scope,
          currentIndex,
          proofs,
          commandPairs,
          lineDocument
        )
      val navigation =
        selectedNavigation(
          snapshot,
          scope,
          currentIndex,
          proofs,
          commandPairs
        )
      val renderState =
        makeRenderState(
          timings,
          scope,
          location,
          navigation,
          indexOptions
        )
      renderState -> makeTree(renderState, displayOptions)
    } { case (renderState, tree) =>
      currentRenderState = Some(renderState)
      updateTree(tree)
    }
  }

  private def startGlobalRefresh(
      snapshot: Document.Snapshot,
      indexOptions: IndexOptions,
      displayOptions: DisplayOptions
  ): Unit = {
    val previousTimings = globalTimings
    val previousIndexes = globalIndexes
    val previousIndexOptions = globalIndexOptions
    val previousVersion = globalVersion
    val dirtyNodes = dirtyGlobalNodes
    forkRefresh {
      val domain =
        snapshot.version.nodes.names_iterator
          .filter(name => name.is_theory && !PIDE.resources.loaded_theory(name))
          .toSet
      val refreshNodes =
        if (
          previousTimings.isEmpty ||
          (previousVersion.exists(_ != snapshot.version.id) &&
            dirtyNodes.isEmpty)
        ) domain
        else dirtyNodes.intersect(domain)
      val retained =
        previousTimings.filter { case (name, _) => domain.contains(name) }
      val refreshed =
        refreshNodes.toVector.sortBy(_.theory).iterator.map { name =>
          Exn.Interrupt.expose()
          name -> loadNodeTimings(snapshot.switch(name))
        }.toMap
      val timingsByNode = retained ++ refreshed
      val reindexAll =
        previousIndexes.isEmpty ||
          !previousIndexOptions.contains(indexOptions)
      val retainedIndexes =
        if (reindexAll) Map.empty
        else {
          previousIndexes.filter { case (name, _) =>
            domain.contains(name) && !refreshNodes.contains(name)
          }
        }
      val reindexNodes = if (reindexAll) domain else refreshNodes
      val rebuiltIndexes =
        reindexNodes.toVector.sortBy(_.theory).iterator.map { name =>
          Exn.Interrupt.expose()
          name -> makeIndex(timingsByNode.getOrElse(name, Vector.empty), indexOptions)
        }.toMap
      val indexesByNode = retainedIndexes ++ rebuiltIndexes
      val globalIndex =
        FineGrainedTimingHierarchy.mergeIndexes(
          indexesByNode.toVector.sortBy(_._1.theory).map(_._2)
        )
      val renderState =
        RenderState(
          globalIndex,
          ScopeGlobal,
          indexOptions.view,
          "Global",
          NoNavigation
        )
      GlobalRefreshResult(
        renderState,
        makeTree(renderState, displayOptions),
        timingsByNode,
        indexesByNode,
        indexOptions,
        domain,
        refreshNodes,
        snapshot.version.id
      )
    } { result =>
      globalTimings = result.timings
      globalIndexes = result.indexes
      globalIndexOptions = Some(result.indexOptions)
      globalVersion = Some(result.version)
      dirtyGlobalNodes =
        dirtyGlobalNodes.intersect(result.domain) -- result.refreshedNodes
      currentRenderState = Some(result.renderState)
      updateTree(result.tree)
    }
  }

  private def rerenderCurrent(): Unit = {
    GUI_Thread.require {}
    currentRenderState.foreach { renderState =>
      val displayOptions = captureDisplayOptions()
      forkRefresh {
        makeTree(renderState, displayOptions)
      } { tree =>
        updateTree(tree)
      }
    }
  }

  private def forkRefresh[A](work: => A)(install: A => Unit): Unit = {
    GUI_Thread.require {}
    refreshGeneration += 1L
    val generation = refreshGeneration
    futureRefresh.change { previous =>
      previous.foreach(_.cancel())
      Some(Future.fork {
        val result = Exn.capture(work)
        GUI_Thread.later {
          if (generation == refreshGeneration) {
            result match {
              case Exn.Res(value) =>
                install(value)
              case Exn.Exn(exn) if Exn.is_interrupt(exn) =>
              case Exn.Exn(exn) =>
                currentRenderState = None
                updateTree(Vector.empty)
                Output.error_message(
                  s"Fine-Grained Timing refresh failed: ${Exn.message(exn)}"
                )
            }
          }
        }
      })
    }
  }

  private def cancelRefresh(): Unit = {
    GUI_Thread.require {}
    refreshGeneration += 1L
    currentRenderState = None
    futureRefresh.change { previous =>
      previous.foreach(_.cancel())
      None
    }
  }

  private def loadNodeTimings(
      snapshot: Document.Snapshot
  ): Vector[CommandTiming] = {
    val node = snapshot.node
    val commandPairs = node.command_iterator().toVector
    val scopeCommands =
      commandPairs.map { case (command, offset) =>
        FineGrainedTimingScope.ScopeCommand(
          command.span.name,
          offset,
          command.length
        )
      }
    val proofs = FineGrainedTimingScope.partitionNamedProofs(scopeCommands)
    val proofContexts = proofContextsByCommand(proofs, commandPairs)
    val lineDocument = Line.Document(node.source)
    commandPairs.zipWithIndex.flatMap { case ((command, offset), index) =>
      Exn.Interrupt.expose()
      val reports = invocations(snapshot, command, offset)
      if (reports.isEmpty) None
      else {
        val proofContext = proofContexts(index)
        Some(CommandTiming(
          command,
          snapshot.node_name.theory,
          proofContext.map(_.name),
          proofContext.map(_.start),
          lineDocument.position(offset).line + 1,
          reports
        ))
      }
    }
  }

  private def invocations(
      snapshot: Document.Snapshot,
      command: Command,
      offset: Int
  ): Vector[FineGrainedTiming.Invocation] = {
    val range = Text.Range(offset, offset + command.length)
    /* `select` keeps only the last markup element of a given name per
       markup-tree entry, and every report of one command shares
       `Position.thread_data`, so all of them land in a single entry: a
       command that opens several profiles — nested ones, or
       `apply (crush_base ..., crush_base ...)` — showed just one.
       `cumulate` accumulates the whole entry instead. */
    val decoded =
      snapshot
        .cumulate[Vector[FineGrainedTiming.Invocation]](
          range,
          Vector.empty,
          Markup.Elements(FineGrainedTiming.ReportMarkup),
          _ => { case (found, Text.Info(_, tree)) =>
            FineGrainedTiming.decode(tree).map(found :+ _)
          }
        )
        .iterator
        .flatMap(_.info)
        .toVector
    FineGrainedTiming.latestPerInvocation(decoded)
  }

  private def makeRenderState(
      commands: Vector[CommandTiming],
      scope: String,
      location: String,
      navigation: NavigationTarget,
      options: IndexOptions
  ): RenderState = {
    val index = makeIndex(commands, options)
    RenderState(index, scope, options.view, location, navigation)
  }

  private def makeIndex(
      commands: Vector[CommandTiming],
      options: IndexOptions
  ): FineGrainedTimingHierarchy.Index[CommandTiming] = {
    val inputs =
      commands.zipWithIndex.map { case (command, order) =>
        FineGrainedTimingHierarchy.Command(
          command,
          order,
          command.theory,
          command.proof,
          command.invocations
        )
      }
    FineGrainedTimingHierarchy.build(
      inputs,
      options.view,
      options.nameFilter,
      options.showSuccess,
      options.showFailure
    )
  }

  private def makeTree(
      state: RenderState,
      options: DisplayOptions
  ): Vector[FineGrainedTimingTreeTable.Data] =
    state.index.signals.flatMap { signalData =>
      Exn.Interrupt.expose()
      if (groupVisible(
        state.view,
        signalData.aggregate,
        signalData.commands,
        options.thresholdMicros
      )) {
        val rootId = signalRootId(state, signalData.signal)
        state.scope match {
          case ScopeGlobal =>
            Vector(groupNode(
              signalData.signal,
              "Global",
              signalData.aggregate,
              NoNavigation,
              rootId,
              options
            ) {
              makeTheoryNodes(
                state,
                signalData,
                rootId,
                options
              )
            })

          case ScopeTheory =>
            Vector(groupNode(
              signalData.signal,
              state.location,
              signalData.aggregate,
              state.navigation,
              rootId,
              options
            ) {
              makeProofNodes(
                state,
                signalData.signal,
                signalData.commands,
                rootId,
                options
              )
            })

          case ScopeProof =>
            Vector(groupNode(
              signalData.signal,
              state.location,
              signalData.aggregate,
              state.navigation,
              rootId,
              options
            ) {
              makeCommandNodes(
                state,
                signalData.signal,
                signalData.commands,
                rootId,
                options
              )
            })

          case ScopeCommand =>
            signalData.commands
              .filter(commandVisible(state.view, _, options.thresholdMicros))
              .flatMap { commandData =>
                makeDetailNodes(
                  state,
                  signalData.signal,
                  commandData,
                  "command",
                  options
                )
              }

          case _ =>
            Vector.empty
        }
      }
      else Vector.empty
    }

  private def makeTheoryNodes(
      state: RenderState,
      signalData: FineGrainedTimingHierarchy.SignalData[CommandTiming],
      parentId: String,
      options: DisplayOptions
  ): Vector[FineGrainedTimingTreeTable.Data] = {
    val theoryGroups =
      signalData.commands.groupBy(_.command.theory).toVector.flatMap {
        case (theory, commands) =>
          FineGrainedTimingHierarchy.merge(commands.iterator.map(_.aggregate))
            .filter(aggregate =>
              groupVisible(
                state.view,
                aggregate,
                commands,
                options.thresholdMicros
              ))
            .map(aggregate => (theory, commands, aggregate))
      }.sortBy { case (_, _, aggregate) =>
        -aggregate.timing.elapsedMicros
      }
    theoryGroups.map { case (theory, commands, aggregate) =>
      Exn.Interrupt.expose()
      val nodeId = s"$parentId/theory:$theory"
      val command = firstCommand(commands)
      groupNode(
        signalData.signal,
        command.node_name.theory_base_name,
        aggregate,
        TheoryNavigation(command.node_name),
        nodeId,
        options
      ) {
        makeProofNodes(
          state,
          signalData.signal,
          commands,
          nodeId,
          options
        )
      }
    }
  }

  private def makeProofNodes(
      state: RenderState,
      signal: FineGrainedTimingHierarchy.Signal,
      commands: Vector[FineGrainedTimingHierarchy.CommandData[CommandTiming]],
      parentId: String,
      options: DisplayOptions
  ): Vector[FineGrainedTimingTreeTable.Data] = {
    val proofGroups =
      commands
        .groupBy(_.command.proof.getOrElse("<top-level commands>"))
        .toVector
        .flatMap {
          case (proof, proofCommands) =>
            FineGrainedTimingHierarchy.merge(
              proofCommands.iterator.map(_.aggregate)
            ).filter(aggregate =>
              groupVisible(
                state.view,
                aggregate,
                proofCommands,
                options.thresholdMicros
              ))
              .map(aggregate => (proof, proofCommands, aggregate))
        }
        .sortBy { case (_, proofCommands, _) =>
          proofCommands.iterator.map(_.command.order).min
        }
    proofGroups.map { case (proof, proofCommands, aggregate) =>
      Exn.Interrupt.expose()
      val nodeId = s"$parentId/proof:$proof"
      groupNode(
        signal,
        proof,
        aggregate,
        CommandNavigation(proofStartCommand(proofCommands)),
        nodeId,
        options
      ) {
        makeCommandNodes(
          state,
          signal,
          proofCommands,
          nodeId,
          options
        )
      }
    }
  }

  private def makeCommandNodes(
      state: RenderState,
      signal: FineGrainedTimingHierarchy.Signal,
      commands: Vector[FineGrainedTimingHierarchy.CommandData[CommandTiming]],
      parentId: String,
      options: DisplayOptions
  ): Vector[FineGrainedTimingTreeTable.Data] =
    commands.filter(commandVisible(state.view, _, options.thresholdMicros))
      .sortBy(_.command.order)
      .map { commandData =>
        Exn.Interrupt.expose()
        val command = commandData.command.value
        val nodeId = s"$parentId/command:${command.command.id}"
        groupNode(
          signal,
          commandContext(command),
          commandData.aggregate,
          CommandNavigation(command.command),
          nodeId,
          options
        ) {
          makeDetailNodes(
            state,
            signal,
            commandData,
            nodeId,
            options
          )
        }
      }

  private def makeDetailNodes(
      state: RenderState,
      signal: FineGrainedTimingHierarchy.Signal,
      commandData: FineGrainedTimingHierarchy.CommandData[CommandTiming],
      parentId: String,
      options: DisplayOptions
  ): Vector[FineGrainedTimingTreeTable.Data] = {
    val command = commandData.command.value
    state.view match {
      case FineGrainedTimingHierarchy.Calls =>
        commandData.invocations
          .filter(visible =>
            invocationVisible(visible.invocation, options.thresholdMicros))
          .sortBy(visible =>
            -visible.invocation.totalElapsedMicros)
          .map { visible =>
            val invocation = visible.invocation
            val location =
              detailLocation(
                state,
                command,
                invocation.id.toString
              )
            FineGrainedTimingTreeTable.Data(
              DetailRow(
                CommandNavigation(command.command),
                s"$parentId/invocation:${visible.index}:${invocation.id}",
                invocationValues(
                  location,
                  invocation,
                  options.timingDigits
                )
              )
            )
          }

      case FineGrainedTimingHierarchy.Aggregate =>
        if (
          commandData.aggregate.timing.elapsedMicros.toDouble >=
            options.thresholdMicros
        ) {
          val location = detailLocation(state, command, "Sample")
          Vector(
            FineGrainedTimingTreeTable.Data(
              DetailRow(
                CommandNavigation(command.command),
                s"$parentId/sample:${signal.name}:${signal.success}",
                aggregateValues(
                  location,
                  signal,
                  commandData.aggregate,
                  options.timingDigits
                )
              )
            )
          )
        }
        else Vector.empty
    }
  }

  private def groupNode(
      signal: FineGrainedTimingHierarchy.Signal,
      location: String,
      aggregate: FineGrainedTiming.Aggregate,
      navigation: NavigationTarget,
      nodeId: String,
      options: DisplayOptions
  )(
      children: => Vector[FineGrainedTimingTreeTable.Data]
  ): FineGrainedTimingTreeTable.Data = {
    val expanded = options.expandedNodes.contains(nodeId)
    FineGrainedTimingTreeTable.Data(
      GroupRow(
        navigation,
        nodeId,
        aggregateValues(
          location,
          signal,
          aggregate,
          options.timingDigits
        )
      ),
      children = if (expanded) children else Vector.empty,
      unloaded = !expanded
    )
  }

  private def invocationValues(
      location: String,
      invocation: FineGrainedTiming.Invocation,
      digits: Int
  ): Vector[String] = {
    val sampleCount = invocation.samples.iterator.map(_.aggregate.count).sum
    val elapsed =
      invocation.totalTiming.map(timing => formatMicros(timing.elapsedMicros, digits))
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
      ""
    )
  }

  private def aggregateValues(
      location: String,
      signal: FineGrainedTimingHierarchy.Signal,
      aggregate: FineGrainedTiming.Aggregate,
      digits: Int
  ): Vector[String] =
    Vector(
      location,
      signal.name,
      if (signal.success) "success" else "failure",
      aggregate.count.toString,
      formatMicros(aggregate.timing.elapsedMicros, digits),
      formatMicros(aggregate.averageElapsedMicros, digits),
      formatMicros(aggregate.percentileElapsedMicros(0.50), digits),
      formatMicros(aggregate.percentileElapsedMicros(0.90), digits),
      formatMicros(aggregate.percentileElapsedMicros(0.99), digits),
      formatMicros(aggregate.minElapsedMicros, digits),
      formatMicros(aggregate.maxElapsedMicros, digits)
    )

  private def firstCommand(
      commands: Vector[FineGrainedTimingHierarchy.CommandData[CommandTiming]]
  ): Command =
    commands.minBy(_.command.order).command.value.command

  private def proofStartCommand(
      commands: Vector[FineGrainedTimingHierarchy.CommandData[CommandTiming]]
  ): Command =
    commands.iterator.flatMap(_.command.value.proofStart).nextOption
      .getOrElse(firstCommand(commands))

  private def invocationVisible(
      invocation: FineGrainedTiming.Invocation,
      thresholdMicros: Double
  ): Boolean =
    /* Old schema 2 reports have no outer timing. Their total is unknown, not
       zero, so retain them rather than hiding otherwise decodable heaps. */
    invocation.totalTiming.forall(
      _.elapsedMicros.toDouble >= thresholdMicros)

  private def commandVisible(
      view: FineGrainedTimingHierarchy.View,
      command: FineGrainedTimingHierarchy.CommandData[CommandTiming],
      thresholdMicros: Double
  ): Boolean =
    view match {
      case FineGrainedTimingHierarchy.Calls =>
        command.invocations.exists(visible =>
          invocationVisible(visible.invocation, thresholdMicros))
      case FineGrainedTimingHierarchy.Aggregate =>
        command.aggregate.timing.elapsedMicros.toDouble >= thresholdMicros
    }

  private def groupVisible(
      view: FineGrainedTimingHierarchy.View,
      aggregate: FineGrainedTiming.Aggregate,
      commands: Vector[
        FineGrainedTimingHierarchy.CommandData[CommandTiming]
      ],
      thresholdMicros: Double
  ): Boolean =
    view match {
      case FineGrainedTimingHierarchy.Calls =>
        commands.exists(commandVisible(view, _, thresholdMicros))
      case FineGrainedTimingHierarchy.Aggregate =>
        aggregate.timing.elapsedMicros.toDouble >= thresholdMicros
    }

  private def signalRootId(
      state: RenderState,
      signal: FineGrainedTimingHierarchy.Signal
  ): String = {
    val location = if (state.scope == ScopeGlobal) "global" else state.location
    s"signal:${signal.name}:${signal.success}/scope:${state.scope}/$location"
  }

  private def selectedCommandIndices(
      scope: String,
      currentIndex: Option[Int],
      proofs: IndexedSeq[FineGrainedTimingScope.NamedProof],
      commandCount: Int
  ): Vector[Int] =
    scope match {
      case ScopeCommand =>
        currentIndex.toVector
      case ScopeProof =>
        currentIndex
          .flatMap(index => FineGrainedTimingScope.namedProofAt(proofs, index))
          .map(proof => (proof.startIndex to proof.endIndex).toVector)
          .getOrElse(Vector.empty)
      case ScopeTheory | ScopeGlobal =>
        (0 until commandCount).toVector
      case _ =>
        Vector.empty
    }

  private def selectedLocation(
      snapshot: Document.Snapshot,
      scope: String,
      currentIndex: Option[Int],
      proofs: IndexedSeq[FineGrainedTimingScope.NamedProof],
      commands: Vector[(Command, Int)],
      lineDocument: Line.Document
  ): String =
    scope match {
      case ScopeCommand =>
        currentIndex
          .flatMap(commands.lift)
          .map { case (command, offset) =>
            val line = lineDocument.position(offset).line + 1
            s"${command.span.name}:$line"
          }
          .getOrElse("none")
      case ScopeProof =>
        currentIndex
          .flatMap(index => FineGrainedTimingScope.namedProofAt(proofs, index))
          .flatMap(proof => commands.lift(proof.startIndex))
          .map { case (command, _) => proofName(command) }
          .getOrElse("none")
      case ScopeTheory =>
        snapshot.node_name.theory_base_name
      case ScopeGlobal =>
        "Global"
      case _ =>
        ""
    }

  private def selectedNavigation(
      snapshot: Document.Snapshot,
      scope: String,
      currentIndex: Option[Int],
      proofs: IndexedSeq[FineGrainedTimingScope.NamedProof],
      commands: Vector[(Command, Int)]
  ): NavigationTarget =
    scope match {
      case ScopeCommand =>
        currentIndex.flatMap(commands.lift)
          .map { case (command, _) => CommandNavigation(command) }
          .getOrElse(NoNavigation)
      case ScopeProof =>
        currentIndex
          .flatMap(index => FineGrainedTimingScope.namedProofAt(proofs, index))
          .flatMap(proof => commands.lift(proof.startIndex))
          .map { case (command, _) => CommandNavigation(command) }
          .getOrElse(NoNavigation)
      case ScopeTheory =>
        TheoryNavigation(snapshot.node_name)
      case _ =>
        NoNavigation
    }

  private def proofName(command: Command): String =
    FineGrainedTimingScope.proofName(command.source, command.span.name)

  private def proofContextsByCommand(
      proofs: IndexedSeq[FineGrainedTimingScope.NamedProof],
      commands: Vector[(Command, Int)]
  ): Vector[Option[ProofContext]] = {
    val result = Array.fill[Option[ProofContext]](commands.length)(None)
    proofs.foreach { proof =>
      val context =
        commands.lift(proof.startIndex).map { case (command, _) =>
          ProofContext(proofName(command), command)
        }
      var index = proof.startIndex
      while (index <= proof.endIndex && index < result.length) {
        result(index) = context
        index += 1
      }
    }
    result.toVector
  }

  private def commandContext(command: CommandTiming): String =
    s"${command.command.span.name}:${command.line}"

  private def detailLocation(
      state: RenderState,
      command: CommandTiming,
      detail: String
  ): String =
    if (state.scope == ScopeCommand)
      s"${commandContext(command)} / $detail"
    else detail

  private def captureIndexOptions(): IndexOptions = {
    GUI_Thread.require {}
    IndexOptions(
      if (viewSelector.getSelectedItem.toString == CallsView)
        FineGrainedTimingHierarchy.Calls
      else FineGrainedTimingHierarchy.Aggregate,
      filterField.getText,
      showSuccess.isSelected,
      showFailure.isSelected
    )
  }

  private def captureDisplayOptions(): DisplayOptions = {
    GUI_Thread.require {}
    DisplayOptions(expandedNodes, timingDigits, thresholdMicros)
  }

  private def updateTree(
      data: Vector[FineGrainedTimingTreeTable.Data]
  ): Unit = {
    GUI_Thread.require {}
    val selectedId =
      table.valueAtRow(table.getSelectedRow).collect {
        case row: TimingRow => row.nodeId
      }
    restoringTreeExpansion = true
    try {
      treeModel.update(data)
      val paths = treeModel.paths
      paths.foreach {
        case (group: GroupRow, path)
            if expandedNodes.contains(group.nodeId) =>
          table.tree.expandPath(path)
        case _ =>
      }
      selectedId.foreach { nodeId =>
        paths.collectFirst {
          case (row: TimingRow, path) if row.nodeId == nodeId => path
        }.foreach(table.tree.setSelectionPath)
      }
      table.refreshRows()
    } finally {
      restoringTreeExpansion = false
    }
  }

  private def loadVisibleColumnIds(): Vector[String] = {
    val defaults = (
      "location" +: "name" +:
        columnDescriptors.iterator
          .filter(_.defaultVisible)
          .map(_.id)
          .toVector
    ).distinct
    val stored = jEdit.getProperty(VisibleColumnsProperty, "").split(",")
      .iterator.map(_.trim).filter(columnIndex.contains).toVector.distinct
    if (stored.nonEmpty) ("location" +: "name" +: stored).distinct else defaults
  }

  private def applyVisibleColumns(): Unit = {
    val model = table.getColumnModel
    while (model.getColumnCount > 0) model.removeColumn(model.getColumn(0))
    visibleColumnIds.foreach { id =>
      val column = new TableColumn(columnIndex(id))
      column.setHeaderValue(columnDescriptors(columnIndex(id)).title)
      model.addColumn(column)
    }
  }

  private def showColumnDialog(): Unit = {
    GUI_Thread.require {}
    val checks = columnDescriptors.map { descriptor =>
      val check = new JCheckBox(
        descriptor.title,
        visibleColumnIds.contains(descriptor.id)
      )
      check.setEnabled(descriptor.id != "name" && descriptor.id != "location")
      descriptor -> check
    }
    val panel = new JPanel(new GridLayout(0, 2, 8, 2))
    checks.foreach { case (_, check) => panel.add(check) }
    val result = JOptionPane.showConfirmDialog(
      this,
      panel,
      "Visible Timing Columns",
      JOptionPane.OK_CANCEL_OPTION,
      JOptionPane.PLAIN_MESSAGE
    )
    if (result == JOptionPane.OK_OPTION) {
      val selected =
        checks.iterator.collect {
          case (descriptor, check) if check.isSelected => descriptor.id
        }.toVector
      visibleColumnIds = ("location" +: "name" +: selected).distinct
      if (visibleColumnIds.nonEmpty) {
        jEdit.setProperty(VisibleColumnsProperty, visibleColumnIds.mkString(","))
        applyVisibleColumns()
      }
    }
  }

  private def thresholdMicros: Double =
    try math.max(0.0, thresholdField.getText.trim.toDouble) * 1000000.0
    catch { case _: NumberFormatException => 0.0 }

  private def loadTimingDigits(): Int = {
    val stored = jEdit.getProperty(
      TimingDigitsProperty,
      DefaultTimingDigits.toString
    )
    try math.max(MinTimingDigits, math.min(MaxTimingDigits, stored.trim.toInt))
    catch { case _: NumberFormatException => DefaultTimingDigits }
  }

  private def updateTimingDigits(): Unit = {
    val value =
      try math.max(
        MinTimingDigits,
        math.min(MaxTimingDigits, timingDigitsField.getText.trim.toInt)
      )
      catch { case _: NumberFormatException => timingDigits }
    timingDigits = value
    timingDigitsField.setText(value.toString)
    jEdit.setProperty(TimingDigitsProperty, value.toString)
    rerenderCurrent()
  }

  private def formatMicros(micros: Long, digits: Int): String =
    String.format(
      Locale.ROOT,
      "%." + digits + "fs",
      java.lang.Double.valueOf(micros.toDouble / 1000000.0)
    )

  private def formatMicros(micros: Double, digits: Int): String =
    String.format(
      Locale.ROOT,
      "%." + digits + "fs",
      java.lang.Double.valueOf(micros / 1000000.0)
    )

  private val main =
    Session.Consumer[Any](getClass.getName) {
      case changed: Session.Commands_Changed =>
        GUI_Thread.later { refresh(Some(changed.nodes)) }
      case Session.Caret_Focus =>
        GUI_Thread.later {
          if (scopeSelector.getSelectedItem.toString != ScopeGlobal) refresh()
        }
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
    cancelRefresh()
    globalTimings = Map.empty
    globalIndexes = Map.empty
    globalIndexOptions = None
    globalVersion = None
    dirtyGlobalNodes = Set.empty
    super.removeNotify()
  }

  def focusOnDefaultComponent(): Unit = table.requestFocus()
}
