/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import java.awt.{BorderLayout, Color, Cursor, FlowLayout, Font, Toolkit}
import java.awt.datatransfer.StringSelection
import java.awt.event.{ActionEvent, ActionListener, MouseAdapter, MouseEvent}
import javax.swing.{JButton, JPanel, JTextArea, JScrollPane, JLabel, JCheckBox,
                     BorderFactory, BoxLayout, JSeparator, SwingConstants}
import javax.swing.text.BadLocationException
import java.time.LocalTime
import java.time.format.DateTimeFormatter
import scala.annotation.unused

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.GUIUtilities
import org.gjt.sp.jedit.gui.DefaultFocusComponent

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

  def updateClientStatus(
    connected: Boolean, count: Int = 0, address: String = ""
  ): Unit = {
    dockableInstance.foreach(_.updateClientConnectionStatus(connected, count, address))
  }

  def isLoggingEnabled: Boolean = {
    dockableInstance.map(_.isMCPLoggingEnabled).getOrElse(false)
  }
}

class IQLogDockable(@unused view: View, @unused position: String)
extends JPanel(new BorderLayout) with DefaultFocusComponent {

  // Register this instance for MCP communication logging
  IQCommunicationLogger.setDockable(this)

  // --- Shared copy icon (75% of jEdit's Copy.png) ---

  private val copyIcon = {
    val orig = GUIUtilities.loadIcon("Copy.png")
    val img = orig.asInstanceOf[javax.swing.ImageIcon].getImage
    val w = (orig.getIconWidth * 0.75).toInt
    val h = (orig.getIconHeight * 0.75).toInt
    new javax.swing.ImageIcon(img.getScaledInstance(w, h, java.awt.Image.SCALE_SMOOTH))
  }

  private def makeCopyLabel(tokenFn: () => Option[String]): JLabel = {
    val label = new JLabel(copyIcon)
    label.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR))
    label.setToolTipText("Copy token to clipboard")
    label.getAccessibleContext.setAccessibleName("Copy token to clipboard")
    label.setVisible(false)
    label.addMouseListener(new MouseAdapter {
      override def mouseClicked(e: MouseEvent): Unit = {
        tokenFn().foreach { t =>
          val sel = new StringSelection(t)
          Toolkit.getDefaultToolkit.getSystemClipboard.setContents(sel, null)
          label.setIcon(null)
          label.setText("\u2713")
          val timer = new javax.swing.Timer(1500, (_: ActionEvent) => {
            label.setText("")
            label.setIcon(copyIcon)
          })
          timer.setRepeats(false)
          timer.start()
        }
      }
    })
    label
  }

  // --- Info header labels (updated by polling timer and client events) ---

  private val serverStatusLabel = new JLabel("Not running")
  serverStatusLabel.getAccessibleContext.setAccessibleName("I/Q MCP server status")

  private val tokenValueLabel = new JLabel("")
  tokenValueLabel.setFont(new Font(Font.MONOSPACED, Font.PLAIN,
    tokenValueLabel.getFont.getSize))
  tokenValueLabel.getAccessibleContext.setAccessibleName("I/Q authentication token")

  private val copyLabel = makeCopyLabel(() =>
    Option(System.getProperty(IQPlugin.AUTH_TOKEN_PROPERTY)).filter(_.nonEmpty))

  private val clientInfoLabel = new JLabel("None")
  clientInfoLabel.setForeground(Color.GRAY)
  clientInfoLabel.getAccessibleContext.setAccessibleName("Client connection info")

  private val irStatusLabel = new JLabel("Not running")
  irStatusLabel.setForeground(Color.GRAY)
  irStatusLabel.getAccessibleContext.setAccessibleName("I/R REPL status")

  private val irTokenValueLabel = new JLabel("")
  irTokenValueLabel.setFont(new Font(Font.MONOSPACED, Font.PLAIN,
    irTokenValueLabel.getFont.getSize))
  irTokenValueLabel.getAccessibleContext.setAccessibleName("I/R authentication token")

  private val irCopyLabel = makeCopyLabel(() => IQPlugin.irReplToken)

  private def createInfoPanel(): JPanel = {
    val panel = new JPanel()
    panel.setLayout(new BoxLayout(panel, BoxLayout.Y_AXIS))
    panel.setBorder(BorderFactory.createEmptyBorder(4, 6, 4, 6))

    def makeRow(labelText: String, valueComponents: JLabel*): JPanel = {
      val row = new JPanel(new FlowLayout(FlowLayout.LEFT, 4, 1))
      val label = new JLabel(labelText)
      label.setFont(label.getFont.deriveFont(Font.BOLD))
      row.add(label)
      valueComponents.foreach(row.add)
      row
    }

    panel.add(makeRow("I/Q MCP Server:", serverStatusLabel, clientInfoLabel))
    panel.add(makeRow("I/Q Auth Token:", tokenValueLabel, copyLabel))
    panel.add(makeRow("I/R REPL:", irStatusLabel))
    panel.add(makeRow("I/R Auth Token:", irTokenValueLabel, irCopyLabel))
    panel.add(new JSeparator(SwingConstants.HORIZONTAL))
    panel
  }

  // --- Server log text area ---

  private val outputTextArea = new JTextArea(15, 50)
  outputTextArea.setEditable(false)
  outputTextArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12))
  outputTextArea.setText("I/Q Server Log:\n" + "=" * 50 + "\n")
  outputTextArea.getAccessibleContext.setAccessibleName("I/Q server log output")
  outputTextArea.getAccessibleContext.setAccessibleDescription(
    "Shows MCP server log messages and client connection events."
  )

  private val scrollPane = new JScrollPane(outputTextArea)
  private val timeFmt = DateTimeFormatter.ofPattern("HH:mm:ss")
  private val uiSettings = IQUISettings.current

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

  // --- Button panel ---

  private val clearLogButton = new JButton("Clear Log")
  clearLogButton.setMnemonic('L')
  clearLogButton.getAccessibleContext.setAccessibleName("Clear log")

  private val logCommunicationCheckbox = new JCheckBox("Log MCP Communication", true)
  logCommunicationCheckbox.setMnemonic('M')
  logCommunicationCheckbox.getAccessibleContext.setAccessibleName("Log MCP communication")
  private val truncateMessagesCheckbox = new JCheckBox("Truncate Long Messages", true)
  truncateMessagesCheckbox.setMnemonic('T')
  truncateMessagesCheckbox.getAccessibleContext.setAccessibleName("Truncate long messages")

  clearLogButton.addActionListener(new ActionListener {
    def actionPerformed(e: ActionEvent): Unit = {
      outputTextArea.setText("I/Q Server Log:\n" + "=" * 50 + "\n")
      appendOutput("Log cleared")
    }
  })

  private val buttonPanel = new JPanel(new FlowLayout())
  buttonPanel.add(clearLogButton)
  buttonPanel.add(logCommunicationCheckbox)
  buttonPanel.add(truncateMessagesCheckbox)

  // --- Layout: info header + buttons at top, log text area in center ---

  private val infoPanel = createInfoPanel()
  private val topPanel = new JPanel(new BorderLayout())
  topPanel.add(infoPanel, BorderLayout.NORTH)
  topPanel.add(buttonPanel, BorderLayout.SOUTH)

  add(topPanel, BorderLayout.NORTH)
  add(scrollPane, BorderLayout.CENTER)

  // --- Polling timer for server status / token / I/R ---

  private def refreshServerInfo(): Unit = {
    // I/Q MCP Server + Clients
    val port = IQPlugin.mcpPort
    val token = Option(System.getProperty(IQPlugin.AUTH_TOKEN_PROPERTY))
    val connected = IQPlugin.activeClientCount
    val authenticated = IQPlugin.authenticatedClientCount
    port match {
      case Some(p) =>
        serverStatusLabel.setText(s"Running on port $p")
        serverStatusLabel.setForeground(new Color(0, 128, 0))
        token match {
          case Some(t) if t.nonEmpty =>
            tokenValueLabel.setText(t)
            copyLabel.setVisible(true)
          case _ =>
            tokenValueLabel.setText("(unavailable)")
            copyLabel.setVisible(false)
        }
        if (connected > 0) {
          clientInfoLabel.setText(s"($connected connected, $authenticated authenticated)")
          clientInfoLabel.setForeground(
            if (authenticated >= connected) new Color(0, 128, 0) else new Color(200, 140, 0))
        } else {
          clientInfoLabel.setText("(no clients)")
          clientInfoLabel.setForeground(Color.GRAY)
        }
      case None =>
        serverStatusLabel.setText("Not running")
        serverStatusLabel.setForeground(Color.RED)
        tokenValueLabel.setText("")
        copyLabel.setVisible(false)
        clientInfoLabel.setText("")
    }

    // I/R REPL
    IQPlugin.irReplPort match {
      case Some(p) =>
        irStatusLabel.setText(s"Running on port $p")
        irStatusLabel.setForeground(new Color(0, 128, 0))
        IQPlugin.irReplToken match {
          case Some(tok) if tok.nonEmpty =>
            irTokenValueLabel.setText(tok)
            irCopyLabel.setVisible(true)
          case _ =>
            irTokenValueLabel.setText("")
            irCopyLabel.setVisible(false)
        }
      case None =>
        irStatusLabel.setText("Not running")
        irStatusLabel.setForeground(Color.GRAY)
        irTokenValueLabel.setText("N/A")
        irCopyLabel.setVisible(false)
    }
  }

  private val infoRefreshTimer = new javax.swing.Timer(2000, (_: ActionEvent) => {
    refreshServerInfo()
  })
  infoRefreshTimer.start()
  refreshServerInfo()

  // --- Public API ---

  def isMCPLoggingEnabled: Boolean = logCommunicationCheckbox.isSelected

  def isTruncationEnabled: Boolean = truncateMessagesCheckbox.isSelected

  def logMCPCommunication(message: String): Unit = {
    if (isMCPLoggingEnabled) {
      javax.swing.SwingUtilities.invokeLater(new Runnable {
        def run(): Unit = {
          appendOutput(s"MCP: $message")
        }
      })
    }
  }

  def updateClientConnectionStatus(
    connected: Boolean, count: Int = 0, address: String = ""
  ): Unit = {
    javax.swing.SwingUtilities.invokeLater(new Runnable {
      def run(): Unit = {
        if (connected) {
          val addrInfo = if (address.nonEmpty) s" ($address)" else ""
          clientInfoLabel.setText(s"$count connected$addrInfo")
          clientInfoLabel.setForeground(new Color(0, 128, 0))
          appendOutput("MCP client connected")
        } else {
          clientInfoLabel.setText("None")
          clientInfoLabel.setForeground(Color.GRAY)
          appendOutput("MCP client disconnected")
        }
      }
    })
  }

  def focusOnDefaultComponent(): Unit = {
    clearLogButton.requestFocus()
  }

  def exit(): Unit = {
    infoRefreshTimer.stop()
    IQCommunicationLogger.clearDockable(this)
  }
}
