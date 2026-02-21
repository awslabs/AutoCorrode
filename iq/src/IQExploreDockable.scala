/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import isabelle._
import isabelle.jedit._

import java.awt.{BorderLayout, FlowLayout}
import java.awt.event.{ActionEvent, ActionListener, KeyEvent, KeyListener, ItemEvent, ItemListener}
import javax.swing.{JButton, JPanel, JLabel, BorderFactory,
                   JRadioButton, ButtonGroup, JFileChooser, BoxLayout}
import javax.swing.filechooser.FileNameExtensionFilter
import java.io.File
import scala.annotation.unused

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.gui.{DefaultFocusComponent, HistoryTextField}

class IQExploreDockable(view: View, @unused position: String)
extends JPanel(new BorderLayout) with DefaultFocusComponent {

  /* output area */

  private val output: Output_Area = new Output_Area(view)
  private val uiSettings = IQUISettings.current

  // Store accumulated messages to preserve them when results are displayed
  private var accumulatedMessages: List[XML.Elem] = List.empty
  private var lastProcessedOutputSize: Int = 0

  private def logDebug(message: => String): Unit = {
    if (uiSettings.exploreDebugLogging) Output.writeln(message)
  }

  // Helper method to append text to the output area (for compatibility)
  private def appendOutput(text: String): Unit = {
    // Convert plain text to XML for the output area
    val xml_elem = XML.Elem(Markup("writeln", Nil), List(XML.Text(text)))
    // Add to accumulated messages with size limit to prevent memory leaks
    accumulatedMessages =
      (accumulatedMessages :+ xml_elem).takeRight(uiSettings.maxExploreMessages)
    // Update display with all accumulated messages
    output.pretty_text_area.update(Document.Snapshot.init, Command.Results.empty, accumulatedMessages)
  }

  // Clear accumulated messages (for new operations)
  private def clearOutput(): Unit = {
    accumulatedMessages = List.empty
    lastProcessedOutputSize = 0
    output.pretty_text_area.update(Document.Snapshot.init, Command.Results.empty, List.empty)
  }

  // Helper method to get current file path
  private def getCurrentFilePath(): Option[String] = {
    try {
      val buffer = view.getBuffer
      if (buffer != null && buffer.getPath != null) {
        Some(buffer.getPath)
      } else {
        None
      }
    } catch {
      case _: Exception => None
    }
  }

  // Process XML output by appending only new results (for gradual sledgehammer output)
  private def processXMLOutput(xml_output: List[XML.Tree]): Unit = {
    logDebug(s"I/Q Explore: processXMLOutput called with ${xml_output.size} XML trees")

    if (xml_output.nonEmpty) {
      val types = xml_output.map(_.getClass.getSimpleName).distinct
      logDebug(s"I/Q Explore: XML tree types: ${types.mkString(", ")}")

      xml_output.take(3).foreach { tree =>
        logDebug(s"I/Q Explore: XML tree: ${tree.toString.take(200)}")
      }

      // Convert XML.Tree to XML.Elem for the Pretty_Text_Area
      val xml_elems = xml_output.collect { case elem: XML.Elem => elem }

      logDebug(s"I/Q Explore: Found ${xml_elems.size} XML elements")
      xml_elems.take(3).foreach { elem =>
        logDebug(s"I/Q Explore: XML element markup: ${elem.markup.name}, body size: ${elem.body.size}")
      }

      // Only process new elements (for gradual output like sledgehammer)
      if (xml_elems.size > lastProcessedOutputSize) {
        val newElements = xml_elems.drop(lastProcessedOutputSize)
        lastProcessedOutputSize = xml_elems.size

        logDebug(s"I/Q Explore: Processing ${newElements.size} new elements (total: $lastProcessedOutputSize)")

        // Append only the new results to accumulated messages with size limit
        accumulatedMessages =
          (accumulatedMessages ++ newElements).takeRight(uiSettings.maxExploreMessages)
        // Update display with all accumulated messages (initial messages + all results so far)
        output.pretty_text_area.update(Document.Snapshot.init, Command.Results.empty, accumulatedMessages)
      }
    }
  }

  // Create controls
  private val inputFieldLabel = new JLabel("Arguments")
  inputFieldLabel.setToolTipText("Arguments: For 'isar_explore': Isar proof methods (e.g., 'by simp'). For 'sledgehammer': prover names (e.g., 'z3', 'cvc4'). For 'find_theorems': search criteria with quotes.")

  private val inputField = new HistoryTextField("isabelle-iq-explore-methods") {
    setColumns(30)
    setToolTipText(inputFieldLabel.getToolTipText)

    addKeyListener(new KeyListener {
      override def keyTyped(e: KeyEvent): Unit = {}
      override def keyPressed(e: KeyEvent): Unit = {
        if (e.getKeyCode == KeyEvent.VK_ENTER) {
          explore()
        }
      }
      override def keyReleased(e: KeyEvent): Unit = {}
    })
  }
  inputField.getAccessibleContext.setAccessibleName("Query arguments")

  // Mode selection
  private val currentCommandRadio = new JRadioButton("Current Command", true)
  currentCommandRadio.setToolTipText("Apply to the command at the current cursor position")

  private val fileOffsetRadio = new JRadioButton("File + Offset", false)
  fileOffsetRadio.setToolTipText("Apply to a command at a specific file and offset")

  private val filePatternRadio = new JRadioButton("File + Pattern", false)
  filePatternRadio.setToolTipText("Apply to a command matching a substring pattern in a file")

  private val modeGroup = new ButtonGroup()
  modeGroup.add(currentCommandRadio)
  modeGroup.add(fileOffsetRadio)
  modeGroup.add(filePatternRadio)

  // File+Offset panel
  private val fileOffsetPanel = new JPanel()
  fileOffsetPanel.setLayout(new BoxLayout(fileOffsetPanel, BoxLayout.Y_AXIS))

  private val filePanel = new JPanel(new FlowLayout(FlowLayout.LEFT))
  private val fileLabel = new JLabel("File:")
  private val fileField = new HistoryTextField("isabelle-iq-explore-file") {
    setColumns(30)
    setToolTipText("Path to the theory file")

    // Method to handle "Current" selection
    private def handleCurrentSelection(): Unit = {
      if (getText == "Current") {
        getCurrentFilePath() match {
          case Some(currentPath) =>
            setText(currentPath)
            addCurrentToHistory()
          case None =>
            appendOutput("No current file available")
            setText("")
        }
      }
    }

    // Add action listener to handle "Current" selection (Enter key)
    addActionListener(new ActionListener {
      override def actionPerformed(e: ActionEvent): Unit = {
        handleCurrentSelection()
      }
    })

    // Add document listener to catch dropdown selections
    getDocument.addDocumentListener(new javax.swing.event.DocumentListener {
      override def insertUpdate(e: javax.swing.event.DocumentEvent): Unit = {
        javax.swing.SwingUtilities.invokeLater(new Runnable {
          override def run(): Unit = handleCurrentSelection()
        })
      }
      override def removeUpdate(e: javax.swing.event.DocumentEvent): Unit = {
        javax.swing.SwingUtilities.invokeLater(new Runnable {
          override def run(): Unit = handleCurrentSelection()
        })
      }
      override def changedUpdate(e: javax.swing.event.DocumentEvent): Unit = {
        javax.swing.SwingUtilities.invokeLater(new Runnable {
          override def run(): Unit = handleCurrentSelection()
        })
      }
    })
  }
  fileField.getAccessibleContext.setAccessibleName("Target file path")
  private val browseButton = new JButton("Browse...")
  browseButton.addActionListener(new ActionListener {
    def actionPerformed(e: ActionEvent): Unit = {
      val fileChooser = new JFileChooser()
      fileChooser.setFileFilter(new FileNameExtensionFilter("Theory Files", "thy"))
      if (fileField.getText.nonEmpty) {
        val currentFile = new File(fileField.getText)
        if (currentFile.exists()) {
          fileChooser.setSelectedFile(currentFile)
        }
      }

      val result = fileChooser.showOpenDialog(IQExploreDockable.this)
      if (result == JFileChooser.APPROVE_OPTION) {
        val selectedFile = fileChooser.getSelectedFile
        fileField.setText(selectedFile.getAbsolutePath)
        fileField.addCurrentToHistory()
      }
    }
  })

  filePanel.add(fileLabel)
  filePanel.add(fileField)
  filePanel.add(browseButton)

  private val offsetPanel = new JPanel(new FlowLayout(FlowLayout.LEFT))
  private val offsetLabel = new JLabel("Offset:")
  private val offsetField = new HistoryTextField("isabelle-iq-explore-offset") {
    setColumns(10)
    setToolTipText("Character offset in the file")
  }
  offsetField.getAccessibleContext.setAccessibleName("Target file offset")

  offsetPanel.add(offsetLabel)
  offsetPanel.add(offsetField)

  fileOffsetPanel.add(filePanel)
  fileOffsetPanel.add(offsetPanel)
  fileOffsetPanel.setVisible(false)

  // File+Pattern panel
  private val filePatternPanel = new JPanel()
  filePatternPanel.setLayout(new BoxLayout(filePatternPanel, BoxLayout.Y_AXIS))

  private val patternFilePanel = new JPanel(new FlowLayout(FlowLayout.LEFT))
  private val patternFileLabel = new JLabel("File:")
  private val patternFileField = new HistoryTextField("isabelle-iq-explore-pattern-file") {
    setColumns(30)
    setToolTipText("Path to the theory file")

    addKeyListener(new KeyListener {
      override def keyTyped(e: KeyEvent): Unit = {}
      override def keyPressed(e: KeyEvent): Unit = {
        if (e.getKeyCode == KeyEvent.VK_ENTER) {
          explore()
        }
      }
      override def keyReleased(e: KeyEvent): Unit = {}
    })

    // Method to handle "Current" selection
    private def handleCurrentSelection(): Unit = {
      if (getText == "Current") {
        getCurrentFilePath() match {
          case Some(currentPath) =>
            setText(currentPath)
            addCurrentToHistory()
          case None =>
            appendOutput("No current file available")
            setText("")
        }
      }
    }

    // Add action listener to handle "Current" selection (Enter key)
    addActionListener(new ActionListener {
      override def actionPerformed(e: ActionEvent): Unit = {
        handleCurrentSelection()
      }
    })

    // Add document listener to catch dropdown selections
    getDocument.addDocumentListener(new javax.swing.event.DocumentListener {
      override def insertUpdate(e: javax.swing.event.DocumentEvent): Unit = {
        javax.swing.SwingUtilities.invokeLater(new Runnable {
          override def run(): Unit = handleCurrentSelection()
        })
      }
      override def removeUpdate(e: javax.swing.event.DocumentEvent): Unit = {
        javax.swing.SwingUtilities.invokeLater(new Runnable {
          override def run(): Unit = handleCurrentSelection()
        })
      }
      override def changedUpdate(e: javax.swing.event.DocumentEvent): Unit = {
        javax.swing.SwingUtilities.invokeLater(new Runnable {
          override def run(): Unit = handleCurrentSelection()
        })
      }
    })
  }
  patternFileField.getAccessibleContext.setAccessibleName("Pattern target file path")

  private val patternBrowseButton = new JButton("Browse...")
  patternBrowseButton.addActionListener(new ActionListener {
    def actionPerformed(e: ActionEvent): Unit = {
      val fileChooser = new JFileChooser()
      fileChooser.setFileFilter(new javax.swing.filechooser.FileNameExtensionFilter("Theory Files", "thy"))
      if (patternFileField.getText.nonEmpty) {
        val currentFile = new java.io.File(patternFileField.getText)
        if (currentFile.exists()) {
          fileChooser.setSelectedFile(currentFile)
        }
      }

      val result = fileChooser.showOpenDialog(IQExploreDockable.this)
      if (result == JFileChooser.APPROVE_OPTION) {
        val selectedFile = fileChooser.getSelectedFile
        patternFileField.setText(selectedFile.getAbsolutePath)
        patternFileField.addCurrentToHistory()
      }
    }
  })

  patternFilePanel.add(patternFileLabel)
  patternFilePanel.add(patternFileField)
  patternFilePanel.add(patternBrowseButton)

  private val patternPanel = new JPanel(new FlowLayout(FlowLayout.LEFT))
  private val patternLabel = new JLabel("Pattern:")
  private val patternField = new HistoryTextField("isabelle-iq-explore-pattern") {
    setColumns(30)
    setToolTipText("Substring pattern to match in command source (must match exactly one command)")

    addKeyListener(new KeyListener {
      override def keyTyped(e: KeyEvent): Unit = {}
      override def keyPressed(e: KeyEvent): Unit = {
        if (e.getKeyCode == KeyEvent.VK_ENTER) {
          explore()
        }
      }
      override def keyReleased(e: KeyEvent): Unit = {}
    })
  }
  patternField.getAccessibleContext.setAccessibleName("Pattern matcher")

  patternPanel.add(patternLabel)
  patternPanel.add(patternField)

  filePatternPanel.add(patternFilePanel)
  filePatternPanel.add(patternPanel)
  filePatternPanel.setVisible(false)

  // Mode selection listener
  currentCommandRadio.addItemListener(new ItemListener {
    def itemStateChanged(e: ItemEvent): Unit = {
      fileOffsetPanel.setVisible(!currentCommandRadio.isSelected)
      filePatternPanel.setVisible(false)
    }
  })

  fileOffsetRadio.addItemListener(new ItemListener {
    def itemStateChanged(e: ItemEvent): Unit = {
      fileOffsetPanel.setVisible(fileOffsetRadio.isSelected)
      filePatternPanel.setVisible(false)
    }
  })

  filePatternRadio.addItemListener(new ItemListener {
    def itemStateChanged(e: ItemEvent): Unit = {
      fileOffsetPanel.setVisible(false)
      filePatternPanel.setVisible(filePatternRadio.isSelected)
    }
  })

  // Query selection for I/Q Explore with auto-suggestions
  private val queryLabel = new JLabel("Query:")
  queryLabel.setToolTipText("Query operation: 'isar_explore', 'sledgehammer' (automated proving), 'find_theorems' (search theorems), or other operations")

  private val queryField = new HistoryTextField("isabelle-iq-explore-query") {
    setColumns(20)
    setText("isar_explore") // Default query
    setToolTipText("Query operation to run")

    private var lastQueryValue = getText // Track the last query value

    // Method to check for changes and update if needed
    private def checkAndUpdate(): Unit = {
      val currentQuery = getText
      if (currentQuery != lastQueryValue) {
        lastQueryValue = currentQuery
        updateArgumentsForQuery()
      }
    }

    addKeyListener(new KeyListener {
      override def keyTyped(e: KeyEvent): Unit = {}
      override def keyPressed(e: KeyEvent): Unit = {
        if (e.getKeyCode == KeyEvent.VK_ENTER) {
          explore()
        }
      }
      override def keyReleased(e: KeyEvent): Unit = {
        checkAndUpdate()
      }
    })

    // Update arguments when text changes (including dropdown selection)
    addActionListener(new ActionListener {
      override def actionPerformed(e: ActionEvent): Unit = {
        checkAndUpdate()
      }
    })

    // Add document listener to catch all text changes including dropdown selections
    getDocument.addDocumentListener(new javax.swing.event.DocumentListener {
      override def insertUpdate(e: javax.swing.event.DocumentEvent): Unit = {
        // Use SwingUtilities.invokeLater to ensure the text field is updated before we read it
        javax.swing.SwingUtilities.invokeLater(new Runnable {
          override def run(): Unit = checkAndUpdate()
        })
      }
      override def removeUpdate(e: javax.swing.event.DocumentEvent): Unit = {
        javax.swing.SwingUtilities.invokeLater(new Runnable {
          override def run(): Unit = checkAndUpdate()
        })
      }
      override def changedUpdate(e: javax.swing.event.DocumentEvent): Unit = {
        javax.swing.SwingUtilities.invokeLater(new Runnable {
          override def run(): Unit = checkAndUpdate()
        })
      }
    })
  }
  queryField.getAccessibleContext.setAccessibleName("Explore query type")

  private var lastAutoFilledArguments: Option[String] = None

  private def maybeApplyDefaultArguments(queryType: String, force: Boolean): Unit = {
    val defaultArguments = IQUtils.getDefaultArguments(queryType)
    if (defaultArguments.isEmpty) return
    if (!force && !uiSettings.autoFillDefaults) return

    val current = inputField.getText
    val safeCurrent = if (current == null) "" else current
    val shouldReplace =
      force || safeCurrent.trim.isEmpty || lastAutoFilledArguments.contains(safeCurrent)

    if (shouldReplace) {
      inputField.setText(defaultArguments)
      lastAutoFilledArguments = Some(defaultArguments)
    } else {
      lastAutoFilledArguments = None
    }
  }

  // Method to update arguments field based on selected query
  private def updateArgumentsForQuery(): Unit = {
    val queryType = queryField.getText.trim
    queryType match {
      case "isar_explore" | "sledgehammer" | "find_theorems" =>
        maybeApplyDefaultArguments(queryType, force = false)
      case _ => ()
    }
  }

  private val queryPanel = new JPanel(new FlowLayout(FlowLayout.LEFT))
  queryPanel.add(queryLabel)
  queryPanel.add(queryField)

  private val applyButton = new JButton("<html><b>Explore</b></html>")
  applyButton.setToolTipText("Apply the selected query to the command")
  applyButton.setMnemonic('E')
  applyButton.getAccessibleContext.setAccessibleName("Run explore query")

  private val cancelButton = new JButton("Cancel")
  cancelButton.setToolTipText("Interrupt unfinished operation")
  cancelButton.setMnemonic('C')
  cancelButton.getAccessibleContext.setAccessibleName("Cancel explore query")

  private val locateButton = new JButton("Locate")
  locateButton.setToolTipText("Locate context of current query within source text")
  locateButton.setMnemonic('L')
  locateButton.getAccessibleContext.setAccessibleName("Locate query context")

  // Process indicator
  private val statusLabel = new JLabel("Ready")
  statusLabel.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5))

  // Button actions
  applyButton.addActionListener(new ActionListener {
    def actionPerformed(e: ActionEvent): Unit = {
      explore()
    }
  })

  cancelButton.addActionListener(new ActionListener {
    def actionPerformed(e: ActionEvent): Unit = {
      cancelExplore()
    }
  })

  locateButton.addActionListener(new ActionListener {
    def actionPerformed(e: ActionEvent): Unit = {
      locateContext()
    }
  })

  // Create function mode selection panel
  // Removed - no longer needed since we only have I/Q Explore mode

  // Create command mode selection panel
  private val commandModePanel = new JPanel(new FlowLayout(FlowLayout.LEFT))
  commandModePanel.add(currentCommandRadio)
  commandModePanel.add(fileOffsetRadio)
  commandModePanel.add(filePatternRadio)

  // Create button panel
  private val controlsPanel = new JPanel()
  controlsPanel.setLayout(new BoxLayout(controlsPanel, BoxLayout.Y_AXIS))

  private val inputPanel = new JPanel(new FlowLayout(FlowLayout.LEFT))
  inputPanel.add(inputFieldLabel)
  inputPanel.add(inputField)

  private val buttonsPanel = new JPanel(new FlowLayout(FlowLayout.LEFT))
  buttonsPanel.add(applyButton)
  buttonsPanel.add(cancelButton)
  buttonsPanel.add(locateButton)
  buttonsPanel.add(statusLabel)

  controlsPanel.add(queryPanel)
  controlsPanel.add(inputPanel)
  controlsPanel.add(commandModePanel)
  controlsPanel.add(fileOffsetPanel)
  controlsPanel.add(filePatternPanel)
  controlsPanel.add(buttonsPanel)

  // Setup output area
  output.setup(this)

  // Make sure the text area can receive focus for mouse wheel events
  output.pretty_text_area.setFocusable(true)
  output.pretty_text_area.getAccessibleContext.setAccessibleName("I/Q explore output")
  output.pretty_text_area.getAccessibleContext.setAccessibleDescription(
    "Shows incremental output from explore queries."
  )
  output.pretty_text_area.requestFocus()

  // Layout: buttons at top, output area in center (use pretty_text_area directly - it has built-in scrolling)
  add(controlsPanel, BorderLayout.NORTH)
  add(output.pretty_text_area, BorderLayout.CENTER)

  // Initialize defaults based on selected query and add some common entries to history
  maybeApplyDefaultArguments(queryField.getText.trim, force = true)

  // Add some common query types to history by temporarily setting text and adding to history
  private def initializeHistoryEntries(): Unit = {
    // Save current text
    val currentQueryText = queryField.getText
    val currentInputText = inputField.getText
    val currentFileText = fileField.getText
    val currentPatternFileText = patternFileField.getText

    // Add query suggestions to history
    queryField.setText("isar_explore")
    queryField.addCurrentToHistory()
    queryField.setText("sledgehammer")
    queryField.addCurrentToHistory()
    queryField.setText("find_theorems")
    queryField.addCurrentToHistory()

    // Add input suggestions to history
    inputField.setText("by simp")
    inputField.addCurrentToHistory()
    inputField.setText("by auto")
    inputField.addCurrentToHistory()
    inputField.setText("by blast")
    inputField.addCurrentToHistory()
    inputField.setText("z3")
    inputField.addCurrentToHistory()
    inputField.setText("cvc4")
    inputField.addCurrentToHistory()
    inputField.setText("\"_ :: nat\" = \"_ :: nat\"")
    inputField.addCurrentToHistory()
    inputField.setText("name: *map*")
    inputField.addCurrentToHistory()

    // Add "Current" option to both file fields
    fileField.setText("Current")
    fileField.addCurrentToHistory()
    patternFileField.setText("Current")
    patternFileField.addCurrentToHistory()

    // Restore original text
    queryField.setText(currentQueryText)
    inputField.setText(currentInputText)
    fileField.setText(currentFileText)
    patternFileField.setText(currentPatternFileText)
  }

  initializeHistoryEntries()

  // Query operation - use our custom Extended_Query_Operation class
  private var exploreOperation: Option[Extended_Query_Operation] = None

  // Find command at file+offset
  private def findCommandAtFileOffset(file_path: String, offset: Int): Option[Command] = {
    IQUtils.findCommandAtFileOffset(file_path, offset) match {
      case scala.util.Success(command) =>
        // Log the found command for debugging
        val cmdText = command.source.trim.replace("\n", "\\n")
        val displayText = if (cmdText.length > 100) cmdText.take(100) + "..." else cmdText
        appendOutput(s"Found command at offset $offset: [$displayText]")
        Some(command)
      case scala.util.Failure(ex) =>
        appendOutput(s"Error: ${ex.getMessage}")
        None
    }
  }

  // Find command by substring pattern in file
  private def findCommandByPattern(file_path: String, pattern: String): Option[Command] = {
    IQUtils.findCommandByPattern(file_path, pattern) match {
      case scala.util.Success(command) => Some(command)
      case scala.util.Failure(ex) =>
        appendOutput(ex.getMessage)
        None
    }
  }

  private def explore(): Unit = {
    // Clear previous messages for new operation
    clearOutput()

    inputField.addCurrentToHistory()
    queryField.addCurrentToHistory()

    // Use custom query with selected method
    val printFunction = queryField.getText.trim
    if (!IQUtils.validateQuery(printFunction)) {
      appendOutput(
        s"Error: unsupported query '$printFunction'. Supported queries: isar_explore, sledgehammer, find_theorems."
      )
      statusLabel.setText("Error")
      return
    }
    val query = IQUtils.formatQueryArguments(printFunction, inputField.getText)

    // Log the query being used
    printFunction match {
      case "sledgehammer" =>
        appendOutput(s"Using sledgehammer with provers: ${inputField.getText}, isar_proofs: false, try0: true")
      case "find_theorems" =>
        appendOutput(s"Using find_theorems with limit: 20, allow_dups: false, query: ${inputField.getText}")
      case "isar_explore" =>
        appendOutput(s"Using isar_explore with method: ${inputField.getText}")
      case _ =>
        appendOutput(s"Using ${printFunction} with arguments: ${inputField.getText}")
    }

    // Initialize operation if needed or if print function has changed
    val currentOperation = exploreOperation.map(op => (op, op.get_print_function))

    if (exploreOperation.isEmpty || currentOperation.exists(_._2 != printFunction + "_query")) {
      // Deactivate existing operation if it exists
      exploreOperation.foreach(_.deactivate())

      // Create new operation with the selected print function
      exploreOperation = Some(new Extended_Query_Operation(
        PIDE.editor, view, printFunction,
        status => {
          status match {
            case Extended_Query_Operation.Status.inactive =>
              statusLabel.setText("No active query")
            case Extended_Query_Operation.Status.waiting =>
              statusLabel.setText("Waiting for evaluation of context ...")
            case Extended_Query_Operation.Status.running =>
              statusLabel.setText(s"Running ${queryField.getText} ...")
            case Extended_Query_Operation.Status.finished =>
              statusLabel.setText("Ready")
            case Extended_Query_Operation.Status.failed =>
              statusLabel.setText("Failed - Missing print function")
              appendOutput(s"FAILED! Cannot find print function $printFunction")
              if (printFunction == "isar_explore") {
                appendOutput(s"To use the isar_explore print function, you need to import Isar_Explore.thy from the I/Q directory.")
              }
          }
        },
        (snapshot, command_results, output) => {
          logDebug(s"I/Q Explore: Output callback called with ${output.size} XML trees")
          logDebug(s"I/Q Explore: Command results is_empty: ${command_results.is_empty}")

          // Process the output
          processXMLOutput(output)
        },
      ))
      exploreOperation.foreach(_.activate())
    }

    // Apply query based on selected mode
    if (currentCommandRadio.isSelected) {
      // Use the current command at cursor position
      appendOutput(s"Using current command at cursor position with ${queryField.getText}")
      exploreOperation.foreach(_.apply_query(query))
    } else if (fileOffsetRadio.isSelected) {
      // Use file+offset to find command
      if (fileField.getText.isEmpty) {
        appendOutput("Error: Please specify a file path")
        return
      }

      if (offsetField.getText.isEmpty) {
        appendOutput("Error: Please specify an offset")
        return
      }

      try {
        val offset = offsetField.getText.toInt
        fileField.addCurrentToHistory()
        offsetField.addCurrentToHistory()

        appendOutput(s"Looking for command at ${fileField.getText}:$offset")
        findCommandAtFileOffset(fileField.getText, offset) match {
          case Some(command) =>
            val cmdText = command.source.trim.replace("\n", "\\n")
            val displayText = if (cmdText.length > 100) cmdText.take(100) + "..." else cmdText
            appendOutput(s"Applying ${queryField.getText} to command: [$displayText]")
            exploreOperation.foreach(_.apply_query_at_command(command, query))
          case None =>
            appendOutput(s"Error: No command found at offset $offset in ${fileField.getText}")
        }
      } catch {
        case e: NumberFormatException =>
          appendOutput("Error: Offset must be a valid integer")
      }
    } else if (filePatternRadio.isSelected) {
      // Use file+pattern to find command
      if (patternFileField.getText.isEmpty) {
        appendOutput("Error: Please specify a file path")
        return
      }

      if (patternField.getText.isEmpty) {
        appendOutput("Error: Please specify a pattern")
        return
      }

      patternFileField.addCurrentToHistory()
      patternField.addCurrentToHistory()

      appendOutput(s"Looking for command matching pattern '${patternField.getText}' in ${patternFileField.getText}")
      findCommandByPattern(patternFileField.getText, patternField.getText) match {
        case Some(command) =>
          val cmdText = command.source.trim.replace("\n", "\\n")
          val displayText = if (cmdText.length > 100) cmdText.take(100) + "..." else cmdText
          appendOutput(s"Applying ${queryField.getText} to command: [$displayText]")
          exploreOperation.foreach(_.apply_query_at_command(command, query))
        case None =>
          // Error message already printed by findCommandByPattern
      }
    }
  }

  private def cancelExplore(): Unit = {
    exploreOperation.foreach(_.cancel_query())
    statusLabel.setText("Cancelled")
  }

  private def locateContext(): Unit = {
    exploreOperation.foreach(_.locate_query())
  }

  // Initialize
  def init(): Unit = {
    // No special initialization needed for I/Q Explore
  }

  // Cleanup
  def exit(): Unit = {
    exploreOperation.foreach(_.deactivate())
    exploreOperation = None
  }

  // Focus on default component
  def focusOnDefaultComponent(): Unit = {
    inputField.requestFocus()
  }
}
