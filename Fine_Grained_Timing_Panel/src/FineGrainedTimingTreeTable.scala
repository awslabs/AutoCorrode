/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.awt.{Component, Graphics}
import java.awt.event.{KeyAdapter, KeyEvent, MouseEvent}
import java.util.EventObject
import javax.swing.{
  AbstractCellEditor,
  JTable,
  JTree,
  ListSelectionModel
}
import javax.swing.event.{
  ListSelectionEvent,
  ListSelectionListener,
  TreeExpansionEvent,
  TreeExpansionListener,
  TreeModelEvent,
  TreeModelListener,
  TreeSelectionEvent,
  TreeSelectionListener
}
import javax.swing.table.{
  AbstractTableModel,
  TableCellEditor,
  TableCellRenderer
}
import javax.swing.tree.{
  DefaultMutableTreeNode,
  DefaultTreeCellRenderer,
  DefaultTreeModel,
  TreePath
}

object FineGrainedTimingTreeTable {
  sealed trait TreeColumn

  case object Loading

  final case class Data(
      value: AnyRef,
      children: Vector[Data] = Vector.empty,
      unloaded: Boolean = false
  )

  trait Columns {
    def count: Int
    def name(column: Int): String
    def columnClass(column: Int): Class[?]
    def valueAt(value: AnyRef, column: Int): AnyRef
  }

  private final class Node(value: AnyRef)
  extends DefaultMutableTreeNode(value)

  final class Model(val columns: Columns)
  extends DefaultTreeModel(new Node(null)) {
    private def rootNode: Node = getRoot.asInstanceOf[Node]

    private def makeNode(data: Data): Node = {
      val node = new Node(data.value)
      data.children.foreach(child => node.add(makeNode(child)))
      if (data.unloaded) node.add(new Node(Loading))
      node
    }

    def update(data: Vector[Data]): Unit = {
      rootNode.removeAllChildren()
      data.foreach(entry => rootNode.add(makeNode(entry)))
      reload(rootNode)
    }

    def value(node: AnyRef): AnyRef =
      node.asInstanceOf[Node].getUserObject

    def valueAt(node: AnyRef, column: Int): AnyRef =
      columns.valueAt(value(node), column)

    def paths: Vector[(AnyRef, TreePath)] = {
      val result = Vector.newBuilder[(AnyRef, TreePath)]
      val nodes = rootNode.preorderEnumeration()
      while (nodes.hasMoreElements) {
        val node = nodes.nextElement().asInstanceOf[Node]
        if (node ne rootNode) {
          val path =
            new TreePath(node.getPath.map(_.asInstanceOf[AnyRef]))
          result += ((node.getUserObject, path))
        }
      }
      result.result()
    }
  }

  final class Table(val treeModel: Model, val treeColumn: Int)
  extends JTable {
    private final class TreeRenderer
    extends JTree(treeModel) with TableCellRenderer {
      private var visibleRow = 0

      setRootVisible(false)
      setShowsRootHandles(true)
      setCellRenderer(new DefaultTreeCellRenderer {
        setOpenIcon(null)
        setClosedIcon(null)
        setLeafIcon(null)

        override def getTreeCellRendererComponent(
            tree: JTree,
            value: AnyRef,
            selected: Boolean,
            expanded: Boolean,
            leaf: Boolean,
            row: Int,
            hasFocus: Boolean
        ): Component = {
          val component =
            super.getTreeCellRendererComponent(
              tree,
              value,
              selected,
              expanded,
              leaf,
              row,
              hasFocus
            )
          val text =
            Table.this.treeModel.value(value) match {
              case Loading => "Loading..."
              case entry =>
                Table.this.treeModel.columns
                  .valueAt(entry, treeColumn).toString
            }
          setText(text)
          component
        }
      })

      override def getTableCellRendererComponent(
          table: JTable,
          value: AnyRef,
          selected: Boolean,
          hasFocus: Boolean,
          row: Int,
          column: Int
      ): Component = {
        val _ = (value, hasFocus, column)
        visibleRow = row
        setBackground(
          if (selected) table.getSelectionBackground
          else table.getBackground
        )
        this
      }

      override def setBounds(
          x: Int,
          y: Int,
          width: Int,
          height: Int
      ): Unit = {
        val _ = (y, height)
        super.setBounds(x, 0, width, Table.this.getHeight)
      }

      override def paint(graphics: Graphics): Unit = {
        graphics.translate(0, -visibleRow * getRowHeight)
        super.paint(graphics)
      }
    }

    private final class Adapter(tree: JTree)
    extends AbstractTableModel {
      private def refreshRows(): Unit = fireTableDataChanged()

      tree.addTreeExpansionListener(new TreeExpansionListener {
        override def treeExpanded(event: TreeExpansionEvent): Unit = {
          val _ = event
          refreshRows()
        }

        override def treeCollapsed(event: TreeExpansionEvent): Unit = {
          val _ = event
          refreshRows()
        }
      })

      treeModel.addTreeModelListener(new TreeModelListener {
        override def treeNodesChanged(event: TreeModelEvent): Unit = {
          val _ = event
          refreshRows()
        }

        override def treeNodesInserted(event: TreeModelEvent): Unit = {
          val _ = event
          refreshRows()
        }

        override def treeNodesRemoved(event: TreeModelEvent): Unit = {
          val _ = event
          refreshRows()
        }

        override def treeStructureChanged(event: TreeModelEvent): Unit = {
          val _ = event
          refreshRows()
        }
      })

      override def getColumnCount: Int = treeModel.columns.count
      override def getColumnName(column: Int): String =
        treeModel.columns.name(column)
      override def getColumnClass(column: Int): Class[?] =
        treeModel.columns.columnClass(column)
      override def getRowCount: Int = tree.getRowCount
      override def isCellEditable(row: Int, column: Int): Boolean = {
        val _ = row
        column == treeColumn
      }

      override def getValueAt(row: Int, column: Int): AnyRef = {
        val path = tree.getPathForRow(row)
        if (path == null) ""
        else treeModel.valueAt(path.getLastPathComponent, column)
      }
    }

    private final class TreeEditor(tree: JTree)
    extends AbstractCellEditor with TableCellEditor {
      override def getTableCellEditorComponent(
          table: JTable,
          value: AnyRef,
          selected: Boolean,
          row: Int,
          column: Int
      ): Component = {
        val _ = (table, value, selected, row, column)
        tree
      }

      override def getCellEditorValue: AnyRef = null

      override def isCellEditable(event: EventObject): Boolean = {
        event match {
          case mouse: MouseEvent =>
            val viewColumn = columnAtPoint(mouse.getPoint)
            if (
              viewColumn >= 0 &&
              convertColumnIndexToModel(viewColumn) == treeColumn
            ) {
              val cell = getCellRect(0, viewColumn, true)
              val forwarded =
                new MouseEvent(
                  tree,
                  mouse.getID,
                  mouse.getWhen,
                  mouse.getModifiersEx,
                  mouse.getX - cell.x,
                  mouse.getY,
                  mouse.getClickCount,
                  mouse.isPopupTrigger,
                  mouse.getButton
                )
              tree.dispatchEvent(forwarded)
            }
          case _ =>
        }
        false
      }
    }

    private val treeRenderer = new TreeRenderer
    private val adapter = new Adapter(treeRenderer)
    private var synchronizingSelection = false

    setModel(adapter)
    setDefaultRenderer(classOf[TreeColumn], treeRenderer)
    setDefaultEditor(classOf[TreeColumn], new TreeEditor(treeRenderer))
    setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
    treeRenderer.setRowHeight(getRowHeight)

    getSelectionModel.addListSelectionListener(new ListSelectionListener {
      override def valueChanged(event: ListSelectionEvent): Unit = {
        if (!event.getValueIsAdjusting && !synchronizingSelection) {
          synchronizingSelection = true
          try {
            val row = getSelectedRow
            if (row >= 0) treeRenderer.setSelectionRow(row)
            else treeRenderer.clearSelection()
          } finally {
            synchronizingSelection = false
          }
        }
      }
    })

    treeRenderer.addTreeSelectionListener(new TreeSelectionListener {
      override def valueChanged(event: TreeSelectionEvent): Unit = {
        val _ = event
        if (!synchronizingSelection) {
          synchronizingSelection = true
          try {
            val rows = treeRenderer.getSelectionRows
            if (rows == null || rows.isEmpty) clearSelection()
            else setRowSelectionInterval(rows.head, rows.head)
          } finally {
            synchronizingSelection = false
          }
        }
      }
    })

    addKeyListener(new KeyAdapter {
      private def selectPath(path: TreePath): Unit = {
        val row = treeRenderer.getRowForPath(path)
        if (row >= 0) {
          setRowSelectionInterval(row, row)
          scrollRectToVisible(getCellRect(row, 0, true))
        }
      }

      override def keyPressed(event: KeyEvent): Unit = {
        val path = treeRenderer.getSelectionPath
        if (path != null) {
          event.getKeyCode match {
            case KeyEvent.VK_RIGHT =>
              if (!treeModel.isLeaf(path.getLastPathComponent)) {
                if (!treeRenderer.isExpanded(path)) {
                  treeRenderer.expandPath(path)
                }
                else {
                  val nextRow = treeRenderer.getRowForPath(path) + 1
                  Option(treeRenderer.getPathForRow(nextRow))
                    .foreach(selectPath)
                }
                event.consume()
              }
            case KeyEvent.VK_LEFT =>
              if (treeRenderer.isExpanded(path)) {
                treeRenderer.collapsePath(path)
                event.consume()
              }
              else {
                val parent = path.getParentPath
                if (
                  parent != null &&
                  parent.getParentPath != null
                ) {
                  selectPath(parent)
                  event.consume()
                }
              }
            case _ =>
          }
        }
      }
    })

    override def getEditingRow: Int = {
      val column = getEditingColumn
      if (
        column >= 0 &&
        convertColumnIndexToModel(column) == treeColumn
      ) -1
      else super.getEditingRow
    }

    def tree: JTree = treeRenderer

    def valueAtRow(row: Int): Option[AnyRef] =
      Option(treeRenderer.getPathForRow(row))
        .map(path => treeModel.value(path.getLastPathComponent))

    def refreshRows(): Unit = adapter.fireTableDataChanged()
  }
}
