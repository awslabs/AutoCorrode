/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

import java.awt.{BorderLayout, FlowLayout, Font}
import java.awt.event.{ActionEvent, ActionListener}
import javax.swing.{JButton, JPanel, JTextArea, JScrollPane, JLabel, JCheckBox, BorderFactory}
import javax.swing.text.BadLocationException
import java.time.LocalTime
import java.time.format.DateTimeFormatter

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DefaultFocusComponent
import org.gjt.sp.jedit.textarea.JEditTextArea

// Companion object for MCP communication logging
object IQCommunicationLogger {
  private var dockableInstance: Option[IQLogDockable] = None

  def setDockable(dockable: IQLogDockable): Unit = {
    dockableInstance = Some(dockable)
  }

  def clearDockable(dockable: IQLogDockable): Unit = synchronized {
    if (dockableInstance.contains(dockable)) dockableInstance = None
  }

  def logCommunication(message: String): Unit = {
    dockableInstance.foreach { dockable =>
      val finalMessage = if (dockable.isTruncationEnabled && message.length > 500) {
        s"${message.take(250)}...[${message.length} chars total]...${message.takeRight(250)}"
      } else {
        message
      }
      dockable.logMCPCommunication(finalMessage)
    }
  }

  def updateClientStatus(connected: Boolean): Unit = {
    dockableInstance.foreach(_.updateClientConnectionStatus(connected))
  }

  def isLoggingEnabled: Boolean = {
    dockableInstance.map(_.isMCPLoggingEnabled).getOrElse(false)
  }
}

class IQLogDockable(view: View, position: String)
extends JPanel(new BorderLayout) with DefaultFocusComponent {

  // Register this instance for MCP communication logging
  IQCommunicationLogger.setDockable(this)

  // Create the output text area
  private val outputTextArea = new JTextArea(15, 50)
  outputTextArea.setEditable(false)
  outputTextArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12))
  outputTextArea.setText("Isabelle/Q Server Output:\n" + "=" * 50 + "\n")
  outputTextArea.getAccessibleContext.setAccessibleName("I/Q server log output")
  outputTextArea.getAccessibleContext.setAccessibleDescription(
    "Shows MCP server log messages and client connection events."
  )

  private val scrollPane = new JScrollPane(outputTextArea)
  private val timeFmt = DateTimeFormatter.ofPattern("HH:mm:ss")
  private val uiSettings = IQUISettings.current

  // Helper method to append text to the output area
  private def appendOutput(text: String): Unit = {
    val timestamp = LocalTime.now().format(timeFmt)
    outputTextArea.append(s"[$timestamp] $text\n")
    trimToMaxLines()
    if (uiSettings.autoScrollLogs) {
      outputTextArea.setCaretPosition(outputTextArea.getDocument.getLength)
    }
  }

  private def trimToMaxLines(): Unit = {
    val lineCount = outputTextArea.getLineCount
    val maxLines = uiSettings.maxLogLines
    if (lineCount <= maxLines) return
    val excessLines = lineCount - maxLines
    try {
      val cutoff = outputTextArea.getLineEndOffset(excessLines - 1)
      outputTextArea.replaceRange("", 0, cutoff)
    } catch {
      case _: BadLocationException => ()
    }
  }

  // Create buttons
  private val clearLogButton = new JButton("Clear Log")
  clearLogButton.setMnemonic('L')
  clearLogButton.getAccessibleContext.setAccessibleName("Clear log")

  // MCP communication logging checkbox
  private val logCommunicationCheckbox = new JCheckBox("Log MCP Communication", true)
  logCommunicationCheckbox.setMnemonic('M')
  logCommunicationCheckbox.getAccessibleContext.setAccessibleName("Log MCP communication")
  private val truncateMessagesCheckbox = new JCheckBox("Truncate Long Messages", true)
  truncateMessagesCheckbox.setMnemonic('T')
  truncateMessagesCheckbox.getAccessibleContext.setAccessibleName("Truncate long messages")

  // MCP Client connection status label
  private val mcpClientStatusLabel = new JLabel("MCP Client: Not connected")
  mcpClientStatusLabel.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5))
  mcpClientStatusLabel.getAccessibleContext.setAccessibleName("MCP client status")

  // Clear log button action
  clearLogButton.addActionListener(new ActionListener {
    def actionPerformed(e: ActionEvent): Unit = {
      outputTextArea.setText("Isabelle/Q Server Output:\n" + "=" * 50 + "\n")
      appendOutput("Log cleared")
    }
  })

  // Create button panel
  private val buttonPanel = new JPanel(new FlowLayout())
  buttonPanel.add(clearLogButton)
  buttonPanel.add(logCommunicationCheckbox)
  buttonPanel.add(truncateMessagesCheckbox)
  buttonPanel.add(mcpClientStatusLabel)

  // Create top panel with buttons and status
  private val topPanel = new JPanel(new BorderLayout())
  topPanel.add(buttonPanel, BorderLayout.CENTER)

  // Layout: buttons and status at top, text area in center
  add(topPanel, BorderLayout.NORTH)
  add(scrollPane, BorderLayout.CENTER)

  // Method to check if MCP communication logging is enabled
  def isMCPLoggingEnabled: Boolean = logCommunicationCheckbox.isSelected

  // Method to check if message truncation is enabled
  def isTruncationEnabled: Boolean = truncateMessagesCheckbox.isSelected

  // Method to log MCP communication to the output area
  def logMCPCommunication(message: String): Unit = {
    if (isMCPLoggingEnabled) {
      javax.swing.SwingUtilities.invokeLater(new Runnable {
        def run(): Unit = {
          appendOutput(s"MCP: $message")
        }
      })
    }
  }

  // Method to update MCP client connection status
  def updateClientConnectionStatus(connected: Boolean): Unit = {
    javax.swing.SwingUtilities.invokeLater(new Runnable {
      def run(): Unit = {
        if (connected) {
          mcpClientStatusLabel.setText("MCP Client: Connected ✓")
          appendOutput("MCP client connected")
        } else {
          mcpClientStatusLabel.setText("MCP Client: Not connected")
          appendOutput("MCP client disconnected")
        }
      }
    })
  }

  def focusOnDefaultComponent(): Unit = {
    clearLogButton.requestFocus()
  }

  def exit(): Unit = {
    IQCommunicationLogger.clearDockable(this)
  }
}
