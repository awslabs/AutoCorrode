/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

import java.awt.{BorderLayout, FlowLayout, Font, GridLayout}
import java.awt.event.{ActionEvent, ActionListener}
import javax.swing.{JButton, JPanel, JTextArea, JScrollPane, JLabel, JCheckBox, BorderFactory}

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.DefaultFocusComponent

// Companion object for PIDE markup logging
object PIDEMarkupLogger {
  private var dockableInstance: Option[IQDumpPIDEDockable] = None

  def setDockable(dockable: IQDumpPIDEDockable): Unit = {
    dockableInstance = Some(dockable)
  }

  def logMarkup(markupType: String, message: String, properties: Properties.T = Nil, xmlBody: XML.Body = Nil): Unit = {
    dockableInstance.foreach(_.logMarkupMessage(markupType, message, properties, xmlBody, None))
  }

  def isLoggingEnabled: Boolean = {
    dockableInstance.map(_.isMarkupLoggingEnabled).getOrElse(false)
  }
}

class IQDumpPIDEDockable(view: View, position: String)
extends JPanel(new BorderLayout) with DefaultFocusComponent {

  // Register this instance for PIDE markup logging
  PIDEMarkupLogger.setDockable(this)

  // Store the consumer for cleanup
  private var markupConsumer: Option[Session.Consumer[Prover.Message]] = None

  // Create the output text area
  private val outputTextArea = new JTextArea(20, 70)
  outputTextArea.setEditable(false)
  outputTextArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 11))
  outputTextArea.setText("I/Q PIDE Markup Dump:\n" + "=" * 70 + "\n")

  private val scrollPane = new JScrollPane(outputTextArea)

  // Helper method to append text to the output area
  private def appendOutput(text: String): Unit = {
    val timestamp = java.time.LocalTime.now().toString.substring(0, 12)
    outputTextArea.append(s"[$timestamp] $text\n")
    // Auto-scroll to bottom
    outputTextArea.setCaretPosition(outputTextArea.getDocument.getLength)
  }

  // Create buttons and controls
  private val clearLogButton = new JButton("Clear Log")
  private val enableLoggingCheckbox = new JCheckBox("Enable Markup Logging", false)
  private val showPropertiesCheckbox = new JCheckBox("Show Properties", true)
  private val showFullXMLCheckbox = new JCheckBox("Show Full XML", true)

  // Markup type filter checkboxes
  private val logErrorsCheckbox = new JCheckBox("Errors", true)
  private val logResultsCheckbox = new JCheckBox("Results", false)
  private val logWarningsCheckbox = new JCheckBox("Warnings", false)
  private val logStatusCheckbox = new JCheckBox("Status", false)
  private val logReportsCheckbox = new JCheckBox("Reports", false)
  private val logOthersCheckbox = new JCheckBox("Others", false)

  // Status label
  private val statusLabel = new JLabel("PIDE Markup Logging: Disabled")
  statusLabel.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5))

  // Clear log button action
  clearLogButton.addActionListener(new ActionListener {
    def actionPerformed(e: ActionEvent): Unit = {
      outputTextArea.setText("I/Q PIDE Markup Dump:\n" + "=" * 70 + "\n")
      appendOutput("Log cleared")
    }
  })

  // Enable/disable logging checkbox action
  enableLoggingCheckbox.addActionListener(new ActionListener {
    def actionPerformed(e: ActionEvent): Unit = {
      if (enableLoggingCheckbox.isSelected) {
        statusLabel.setText("PIDE Markup Logging: Active")
        appendOutput("Markup logging enabled")
      } else {
        statusLabel.setText("PIDE Markup Logging: Disabled")
        appendOutput("Markup logging disabled")
      }
    }
  })

  // Create control panels
  private val mainControlPanel = new JPanel(new FlowLayout())
  mainControlPanel.add(clearLogButton)
  mainControlPanel.add(enableLoggingCheckbox)
  mainControlPanel.add(showPropertiesCheckbox)
  mainControlPanel.add(showFullXMLCheckbox)

  private val filterPanel = new JPanel(new FlowLayout())
  filterPanel.setBorder(BorderFactory.createTitledBorder("Markup Types"))
  filterPanel.add(logErrorsCheckbox)
  filterPanel.add(logResultsCheckbox)
  filterPanel.add(logWarningsCheckbox)
  filterPanel.add(logStatusCheckbox)
  filterPanel.add(logReportsCheckbox)
  filterPanel.add(logOthersCheckbox)

  private val statusPanel = new JPanel(new FlowLayout())
  statusPanel.add(statusLabel)

  // Create top panel with all controls
  private val topPanel = new JPanel(new BorderLayout())
  topPanel.add(mainControlPanel, BorderLayout.NORTH)
  topPanel.add(filterPanel, BorderLayout.CENTER)
  topPanel.add(statusPanel, BorderLayout.SOUTH)

  // Layout: controls at top, text area in center
  add(topPanel, BorderLayout.NORTH)
  add(scrollPane, BorderLayout.CENTER)

  // Method to check if markup logging is enabled
  def isMarkupLoggingEnabled: Boolean = enableLoggingCheckbox.isSelected

  // Method to check if properties should be shown
  def isShowPropertiesEnabled: Boolean = showPropertiesCheckbox.isSelected

  // Method to check if full XML should be shown
  def isShowFullXMLEnabled: Boolean = showFullXMLCheckbox.isSelected

  // Method to check if a specific markup type should be logged
  def shouldLogMarkupType(markupType: String): Boolean = {
    markupType match {
      case Markup.ERROR => logErrorsCheckbox.isSelected
      case Markup.RESULT => logResultsCheckbox.isSelected
      case Markup.WARNING => logWarningsCheckbox.isSelected
      case Markup.STATUS => logStatusCheckbox.isSelected
      case Markup.REPORT => logReportsCheckbox.isSelected
      case _ => logOthersCheckbox.isSelected
    }
  }

  // Method to get display name for markup type
  def getMarkupDisplayName(markupType: String): String = {
    markupType match {
      case Markup.ERROR => "ERROR"
      case Markup.RESULT => "RESULT"
      case Markup.WARNING => "WARNING"
      case Markup.STATUS => "STATUS"
      case Markup.REPORT => "REPORT"
      case _ => s"MARKUP($markupType)"
    }
  }

  // Method to log markup messages to the output area
  def logMarkupMessage(markupType: String, message: String, properties: Properties.T = Nil, xmlBody: XML.Body = Nil, fullOutput: Option[Prover.Output] = None): Unit = {
    if (isMarkupLoggingEnabled && shouldLogMarkupType(markupType)) {
      javax.swing.SwingUtilities.invokeLater(new Runnable {
        def run(): Unit = {
          val displayName = getMarkupDisplayName(markupType)

          val markupText = if (isShowFullXMLEnabled && xmlBody.nonEmpty) {
            // Show full XML structure including the outer markup wrapper
            val fullMessage = fullOutput match {
              case Some(output) => output.message.toString
              case None => xmlBody.map(_.toString).mkString("\n")
            }
            val baseText = s"$displayName (Full XML): $message"
            val fullText = if (isShowPropertiesEnabled && properties.nonEmpty) {
              val propsText = properties.map { case (k, v) => s"$k=$v" }.mkString(", ")
              s"$baseText\n       Properties: [$propsText]\n       Full XML Message:\n$fullMessage"
            } else {
              s"$baseText\n       Full XML Message:\n$fullMessage"
            }
            fullText
          } else {
            // Show content only (default behavior)
            val baseText = s"$displayName: $message"
            if (isShowPropertiesEnabled && properties.nonEmpty) {
              val propsText = properties.map { case (k, v) => s"$k=$v" }.mkString(", ")
              s"$baseText\n       Properties: [$propsText]"
            } else {
              baseText
            }
          }
          appendOutput(markupText)
        }
      })
    }
  }

  def focusOnDefaultComponent(): Unit = {
    clearLogButton.requestFocus()
  }

  // Initialize PIDE markup message monitoring
  private def initializePIDEMonitoring(): Unit = {
    try {
      // Get the current session
      val session = PIDE.session

      // Create a consumer for markup messages
      val consumer = Session.Consumer[Prover.Message]("pide_markup_dump") { msg =>
        msg match {
          case output: Prover.Output =>
            val markupType = output.kind
            val content = XML.content(output.body)

            // Log if it's a type we're interested in
            if (shouldLogMarkupType(markupType) && content.nonEmpty) {
              logMarkupMessage(markupType, content, output.properties, output.body, Some(output))
            }
          case _ => // Ignore non-output messages
        }
      }

      // Store the consumer for cleanup
      markupConsumer = Some(consumer)

      // Subscribe to all messages to catch markup
      session.all_messages += consumer

      appendOutput("PIDE markup monitoring initialized")
      appendOutput("Monitoring: " + getEnabledMarkupTypes.mkString(", "))
    } catch {
      case ex: Exception =>
        appendOutput(s"Failed to initialize PIDE monitoring: ${ex.getMessage}")
    }
  }

  // Helper method to get list of enabled markup types
  private def getEnabledMarkupTypes: List[String] = {
    var types = List.empty[String]
    if (logErrorsCheckbox.isSelected) types = "Errors" :: types
    if (logResultsCheckbox.isSelected) types = "Results" :: types
    if (logWarningsCheckbox.isSelected) types = "Warnings" :: types
    if (logStatusCheckbox.isSelected) types = "Status" :: types
    if (logReportsCheckbox.isSelected) types = "Reports" :: types
    if (logOthersCheckbox.isSelected) types = "Others" :: types
    types.reverse
  }

  // Cleanup method to remove the consumer
  def cleanup(): Unit = {
    try {
      markupConsumer.foreach { consumer =>
        val session = PIDE.session
        session.all_messages -= consumer
        appendOutput("PIDE markup monitoring stopped")
      }
      markupConsumer = None
    } catch {
      case ex: Exception =>
        appendOutput(s"Error during cleanup: ${ex.getMessage}")
    }
  }

  // Initialize monitoring when dockable is created
  initializePIDEMonitoring()
}
