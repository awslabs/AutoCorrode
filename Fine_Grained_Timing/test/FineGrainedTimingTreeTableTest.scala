/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.awt.event.KeyEvent
import javax.swing.SwingUtilities

object FineGrainedTimingTreeTableTest {
  private final case class Row(name: String, total: String)

  private def requireThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  private def testExpansionAndReplacement(): Unit = {
    val columns =
      new FineGrainedTimingTreeTable.Columns {
        override def count: Int = 2
        override def name(column: Int): String =
          if (column == 0) "Name" else "Total"
        override def columnClass(column: Int): Class[?] =
          if (column == 0)
            classOf[FineGrainedTimingTreeTable.TreeColumn]
          else classOf[String]
        override def valueAt(value: AnyRef, column: Int): AnyRef =
          value match {
            case Row(name, total) => if (column == 0) name else total
            case FineGrainedTimingTreeTable.Loading =>
              if (column == 0) "Loading..." else ""
            case _ => ""
          }
      }
    val model = new FineGrainedTimingTreeTable.Model(columns)
    val table = new FineGrainedTimingTreeTable.Table(model, treeColumn = 0)

    model.update(Vector(
      FineGrainedTimingTreeTable.Data(
        Row("signal", "2.0s"),
        unloaded = true
      )
    ))
    table.refreshRows()

    val groupPath =
      model.paths.collectFirst {
        case (Row("signal", _), path) => path
      }.getOrElse(sys.error("missing signal path"))
    requireThat(table.getRowCount == 1,
      s"collapsed group should occupy one row: ${table.getRowCount}")
    requireThat(!table.tree.isExpanded(groupPath),
      "new group should start collapsed")
    requireThat(table.getModel.isCellEditable(0, 0),
      "tree column must accept mouse events through its editor")

    table.setRowSelectionInterval(0, 0)
    val expand =
      new KeyEvent(
        table,
        KeyEvent.KEY_PRESSED,
        System.currentTimeMillis(),
        0,
        KeyEvent.VK_RIGHT,
        KeyEvent.CHAR_UNDEFINED
      )
    table.getKeyListeners.foreach(_.keyPressed(expand))
    requireThat(table.getRowCount == 2,
      s"loading child should become visible: ${table.getRowCount}")
    requireThat(
      table.valueAtRow(1).contains(FineGrainedTimingTreeTable.Loading),
      s"expanded unloaded group should show Loading: ${table.valueAtRow(1)}"
    )

    model.update(Vector(
      FineGrainedTimingTreeTable.Data(
        Row("signal", "2.0s"),
        children = Vector(
          FineGrainedTimingTreeTable.Data(Row("Theory", "2.0s"))
        )
      )
    ))
    val loadedGroupPath =
      model.paths.collectFirst {
        case (Row("signal", _), path) => path
      }.getOrElse(sys.error("missing loaded signal path"))
    table.tree.expandPath(loadedGroupPath)
    table.refreshRows()

    requireThat(table.getRowCount == 2,
      s"loaded child should replace placeholder: ${table.getRowCount}")
    requireThat(table.valueAtRow(1).contains(Row("Theory", "2.0s")),
      s"unexpected loaded child: ${table.valueAtRow(1)}")
    requireThat(table.getValueAt(1, 1) == "2.0s",
      s"timing column lost row alignment: ${table.getValueAt(1, 1)}")

    table.setRowSelectionInterval(0, 0)
    val collapse =
      new KeyEvent(
        table,
        KeyEvent.KEY_PRESSED,
        System.currentTimeMillis(),
        0,
        KeyEvent.VK_LEFT,
        KeyEvent.CHAR_UNDEFINED
      )
    table.getKeyListeners.foreach(_.keyPressed(collapse))
    requireThat(table.getRowCount == 1,
      s"collapse should hide the child: ${table.getRowCount}")
  }

  def main(_args: Array[String]): Unit = {
    var failure = Option.empty[Throwable]
    SwingUtilities.invokeAndWait(new Runnable {
      override def run(): Unit =
        try testExpansionAndReplacement()
        catch { case exn: Throwable => failure = Some(exn) }
    })
    failure.foreach(throw _)
    println("FineGrainedTimingTreeTableTest: all tests passed")
  }
}
