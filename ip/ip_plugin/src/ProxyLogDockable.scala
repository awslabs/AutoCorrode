/* Proxy Log dockable: scrolling text area showing proxy_log messages. */

import isabelle._

import java.awt.{BorderLayout, Font}
import java.awt.event.{ActionEvent, ActionListener}
import javax.swing.{JButton, JPanel, JTextArea, JScrollPane}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DefaultFocusComponent


class ProxyLogDockable(view: View, position: String)
extends JPanel(new BorderLayout) with DefaultFocusComponent {

  private val textArea = new JTextArea
  textArea.setEditable(false)
  textArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12))

  private val clearButton = new JButton("Clear")
  clearButton.addActionListener((_: ActionEvent) => textArea.setText(""))

  add(new JScrollPane(textArea), BorderLayout.CENTER)
  add(clearButton, BorderLayout.SOUTH)

  private val listener: String => Unit = { text =>
    textArea.append(text + "\n")
    textArea.setCaretPosition(textArea.getDocument.getLength)
  }

  ProxyState.addLogListener(listener)

  /* Called by jEdit when the dockable is closed. */
  def dispose(): Unit = ProxyState.removeLogListener(listener)

  def focusOnDefaultComponent(): Unit = textArea.requestFocus()
}
