/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.awt.{BorderLayout, CardLayout, Color, FlowLayout}
import javax.swing.{BorderFactory, JButton, JEditorPane, JLabel, JOptionPane, JPanel, JScrollPane, JTextArea}
import javax.swing.event.{HyperlinkEvent, HyperlinkListener}

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/**
 * Singleton companion for the Assistant dockable panel.
 * Manages the single instance, insert-action registry, cancellation state,
 * and provides thread-safe methods for updating the UI from background threads.
 */
object AssistantDockable {
  @volatile private var instance: Option[AssistantDockable] = None
  private val insertActions = new java.util.concurrent.ConcurrentHashMap[String, () => Unit]()
  private val insertActionOrder = new java.util.concurrent.ConcurrentLinkedDeque[String]()
  private val insertActionsLock = new Object()
  private val maxInsertActions = AssistantConstants.MAX_INSERT_ACTIONS
  @volatile private var _cancelled = false
  @volatile private var _busy = false
  @volatile private var _busyStartTime = 0L

  def setInstance(d: AssistantDockable): Unit = synchronized { instance = Some(d) }
  def clearInstance(d: AssistantDockable): Unit = synchronized {
    if (instance.contains(d)) instance = None
  }

  def isCancelled: Boolean = _cancelled

  def cancel(): Unit = {
    _cancelled = true
    _busy = false
    setStatus(AssistantConstants.STATUS_CANCELLED)
  }

  def resetCancel(): Unit = { _cancelled = false }

  /** Clear all registered insert actions. Thread-safe with atomic clear. */
  def clearInsertActions(): Unit = insertActionsLock.synchronized {
    insertActions.clear()
    insertActionOrder.clear()
  }

  /** 
   * Register an insert action and return its ID for use in hyperlinks.
   * Synchronized to ensure HashMap and Deque operations are atomic.
   */
  def registerAction(action: () => Unit): String = insertActionsLock.synchronized {
    val id = java.util.UUID.randomUUID().toString.take(8)
    insertActions.put(id, action)
    insertActionOrder.addLast(id)
    // Evict oldest entries if we exceed the limit
    while (insertActions.size > maxInsertActions) {
      val oldest = insertActionOrder.pollFirst()
      if (oldest != null) insertActions.remove(oldest)
    }
    id
  }

  /** Add a chat response with optional clickable insert link */
  def respondInChat(text: String, insertCode: Option[(String, () => Unit)] = None): Unit = {
    val content = insertCode match {
      case Some((code, action)) =>
        val id = registerAction(action)
        s"$text\n\n```action:$id\n$code\n```"
      case None => text
    }
    ChatAction.addMessage("assistant", content)
    showConversation(ChatAction.getHistory)
  }

  def showConversation(history: List[ChatAction.Message]): Unit =
    instance.foreach(d => GUI_Thread.later { d.displayConversation(history) })

  def setStatus(status: String): Unit = {
    val wasBusy = _busy
    _busy = status != AssistantConstants.STATUS_READY && status != AssistantConstants.STATUS_CANCELLED && !status.startsWith("Error")
    if (_busy && !wasBusy) _busyStartTime = System.currentTimeMillis()
    instance.foreach(d => GUI_Thread.later { d.updateStatus(status) })
  }

  def setBadge(badge: VerificationBadge.BadgeType): Unit =
    instance.foreach(d => GUI_Thread.later { d.updateBadge(badge) })

  def refreshIQStatus(): Unit =
    instance.foreach(d => GUI_Thread.later { d.updateIQStatus() })

  def refreshModelLabel(): Unit =
    instance.foreach(d => GUI_Thread.later { d.updateModelLabel() })

  /** Global teardown hook used from plugin stop to avoid leaked dockable state/subscriptions. */
  def shutdown(): Unit = {
    val current = synchronized { instance }
    current.foreach(_.disposeDockable())
    synchronized {
      instance = None
      clearInsertActions()
      _cancelled = false
      _busy = false
      _busyStartTime = 0L
    }
  }
}

/**
 * Chat UI panel docked in Isabelle/jEdit.
 * Renders conversation history as styled HTML, provides chat input with
 * keyboard shortcuts, status indicators for I/Q and model, and clickable
 * insert links for generated code.
 */
class AssistantDockable(view: View, position: String) extends Dockable(view, position) {

  AssistantDockable.setInstance(this)
  private[this] val statusSubscription =
    AssistantStatusSubscription.create(
      PIDE.session,
      s"assistant-status-${System.identityHashCode(this)}",
      _ => GUI_Thread.later { updateAssistantStatus() }
    )
  @volatile private[this] var disposed = false

  // Display state — MUST be declared before initializeUI() runs
  private val displayLock = new Object()
  @volatile private var renderedMessageCount = 0
  @volatile private var welcomeShown = false

  // UI Components
  private val badgeContainer = createBadgeContainer()
  private val htmlPane = createHtmlPane()
  private val cardLayout = new CardLayout()
  private val contentPanel = createContentPanel()
  private val mainPanel = createMainPanel()
  private val (iqStatusLabel, modelLabel) = createStatusLabels()
  private val (statusLabel, cancelButton, clearButton) = createControlElements()
  private val topPanel = createTopPanel()
  private val (chatInput, sendButton, inputPanel) = createInputPanel()

  // Initialize UI
  initializeUI()
  initializeEventHandlers()

  private def createBadgeContainer(): JPanel = {
    val container = new JPanel(new BorderLayout())
    container.setVisible(false)
    container.setBorder(BorderFactory.createMatteBorder(0, 0, 1, 0, javax.swing.UIManager.getColor("Separator.foreground")))
    container
  }

  private def createHtmlPane(): JEditorPane = {
    val pane = new JEditorPane()
    pane.setEditorKit(new LatexAwareEditorKit())
    pane.setEditable(false)
    pane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, true)
    pane.addHyperlinkListener(new HyperlinkListener {
      def hyperlinkUpdate(e: HyperlinkEvent): Unit = {
        if (e.getEventType == HyperlinkEvent.EventType.ACTIVATED) {
          val desc = e.getDescription
          if (desc != null && desc.startsWith("action:insert:")) {
            val id = desc.stripPrefix("action:insert:")
            val action = AssistantDockable.insertActions.get(id)
            if (action != null) action()
          } else if (desc != null && desc.startsWith("action:copy:")) {
            val encoded = desc.stripPrefix("action:copy:")
            val text = java.net.URLDecoder.decode(encoded, "UTF-8")
            val clipboard = java.awt.Toolkit.getDefaultToolkit.getSystemClipboard
            clipboard.setContents(new java.awt.datatransfer.StringSelection(text), null)
          }
        }
      }
    })
    pane
  }

  private def createContentPanel(): JPanel = {
    val panel = new JPanel(cardLayout)
    panel.add(new JScrollPane(htmlPane), "html")
    panel
  }

  private def createMainPanel(): JPanel = {
    val panel = new JPanel(new BorderLayout())
    panel.add(badgeContainer, BorderLayout.NORTH)
    panel.add(contentPanel, BorderLayout.CENTER)
    panel
  }

  private def createStatusLabels(): (JLabel, JLabel) = {
    val iqStatus = new JLabel("I/Q: Unknown")
    iqStatus.setOpaque(true)
    iqStatus.setBorder(BorderFactory.createEmptyBorder(2, 4, 2, 4))
    
    val model = new JLabel("Model: Loading...")
    model.setBorder(BorderFactory.createEmptyBorder(2, 4, 2, 4))
    
    (iqStatus, model)
  }

  private def createControlElements(): (JLabel, JButton, JButton) = {
    val status = new JLabel(AssistantConstants.STATUS_READY)
    val cancel = new JButton("Cancel")
    cancel.setVisible(false)
    val clear = new JButton("Clear")
    (status, cancel, clear)
  }

  private def createTopPanel(): JPanel = {
    val panel = new JPanel(new BorderLayout())
    val leftPanel = new JPanel(new FlowLayout(FlowLayout.LEFT))
    leftPanel.add(iqStatusLabel)
    leftPanel.add(modelLabel)
    
    val rightPanel = new JPanel(new FlowLayout(FlowLayout.RIGHT))
    rightPanel.add(statusLabel)
    rightPanel.add(cancelButton)
    rightPanel.add(clearButton)
    
    panel.add(leftPanel, BorderLayout.WEST)
    panel.add(rightPanel, BorderLayout.EAST)
    panel
  }

  private def createInputPanel(): (JTextArea, JButton, JPanel) = {
    val input = new JTextArea(AssistantConstants.CHAT_INPUT_ROWS, AssistantConstants.CHAT_INPUT_COLUMNS)
    input.setLineWrap(true)
    input.setWrapStyleWord(true)
    input.setFont(javax.swing.UIManager.getFont("TextField.font"))
    input.setBorder(BorderFactory.createEmptyBorder(4, 6, 4, 6))

    // Small square send button overlaid in the bottom-right corner of the text area
    val send = new JButton("Send ↵")
    send.setToolTipText("Send message (Enter)")
    send.setFont(send.getFont.deriveFont(java.awt.Font.BOLD, 11f))
    send.setPreferredSize(new java.awt.Dimension(56, 24))
    send.setMinimumSize(new java.awt.Dimension(56, 24))
    send.setMaximumSize(new java.awt.Dimension(56, 24))
    send.setMargin(new java.awt.Insets(0, 0, 0, 0))
    send.setFocusable(false)
    send.setContentAreaFilled(false)
    send.setForeground(javax.swing.UIManager.getColor("Button.foreground"))
    send.setBorder(BorderFactory.createLineBorder(javax.swing.UIManager.getColor("Button.shadow"), 1, true))
    send.setCursor(java.awt.Cursor.getPredefinedCursor(java.awt.Cursor.HAND_CURSOR))
    // Hover effect
    send.addMouseListener(new java.awt.event.MouseAdapter {
      override def mouseEntered(e: java.awt.event.MouseEvent): Unit = {
        send.setContentAreaFilled(true)
        send.setBackground(javax.swing.UIManager.getColor("Button.highlight"))
        send.setForeground(javax.swing.UIManager.getColor("Button.foreground"))
      }
      override def mouseExited(e: java.awt.event.MouseEvent): Unit = {
        send.setContentAreaFilled(false)
        send.setForeground(javax.swing.UIManager.getColor("Button.foreground"))
      }
    })

    // Anchor button in bottom-right of a layered container
    val scrollPane = new JScrollPane(input)
    scrollPane.setBorder(BorderFactory.createLineBorder(javax.swing.UIManager.getColor("TextField.darkShadow")))
    scrollPane.setVerticalScrollBarPolicy(javax.swing.ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED)

    val layered = new JPanel(null) {
      override def getPreferredSize: java.awt.Dimension = scrollPane.getPreferredSize
      override def doLayout(): Unit = {
        val w = getWidth
        val h = getHeight
        scrollPane.setBounds(0, 0, w, h)
        val bw = send.getPreferredSize.width
        val bh = send.getPreferredSize.height
        send.setBounds(w - bw - 6, h - bh - 6, bw, bh)
      }
    }
    layered.add(send)   // on top
    layered.add(scrollPane) // behind

    val panel = new JPanel(new BorderLayout())
    panel.setBorder(BorderFactory.createEmptyBorder(3, 0, 0, 0))
    panel.add(layered, BorderLayout.CENTER)
    (input, send, panel)
  }

  private def initializeUI(): Unit = {
    setupInitialState()
    layoutComponents()
    showWelcomeMessage()
  }

  private def setupInitialState(): Unit = {
    updateAssistantStatus()
    updateModelLabel()
  }

  private def layoutComponents(): Unit = {
    add(topPanel, BorderLayout.NORTH)
    set_content(mainPanel)
    add(inputPanel, BorderLayout.SOUTH)
  }

  private def showWelcomeMessage(): Unit = {
    displayConversation(ChatAction.getHistory)
  }

  private def initializeEventHandlers(): Unit = {
    setupButtonHandlers()
    setupChatInputHandlers()
    setupAccessibilityHandlers()
    setupStatusHandlers()
  }

  private def setupButtonHandlers(): Unit = {
    clearButton.addActionListener(_ => clearChat())
    sendButton.addActionListener(_ => sendChat())
    cancelButton.addActionListener(_ => AssistantDockable.cancel())
  }

  private def setupChatInputHandlers(): Unit = {
    // Enter sends, Shift+Enter inserts newline
    chatInput.addKeyListener(new java.awt.event.KeyAdapter {
      override def keyPressed(e: java.awt.event.KeyEvent): Unit = {
        if (e.getKeyCode == java.awt.event.KeyEvent.VK_ENTER && !e.isShiftDown) {
          e.consume()
          sendChat()
        }
      }
    })

    // Command auto-completion popup
    val completionPopup = new javax.swing.JPopupMenu()
    chatInput.getDocument.addDocumentListener(new javax.swing.event.DocumentListener {
      def insertUpdate(e: javax.swing.event.DocumentEvent): Unit = updateCompletion()
      def removeUpdate(e: javax.swing.event.DocumentEvent): Unit = updateCompletion()
      def changedUpdate(e: javax.swing.event.DocumentEvent): Unit = {}
      private def updateCompletion(): Unit = javax.swing.SwingUtilities.invokeLater { () =>
        val text = chatInput.getText.trim
        completionPopup.setVisible(false)
        if (text.startsWith(":") && text.length >= 2 && !text.contains(" ")) {
          val prefix = text.drop(1).toLowerCase
          val commands = ChatAction.commandNames.filter(_.startsWith(prefix)).sorted.take(8)
          if (commands.nonEmpty) {
            completionPopup.removeAll()
            for (cmd <- commands) {
              val item = new javax.swing.JMenuItem(":" + cmd)
              item.addActionListener { _ =>
                chatInput.setText(":" + cmd + " ")
                chatInput.setCaretPosition(chatInput.getText.length)
                completionPopup.setVisible(false)
              }
              completionPopup.add(item)
            }
            try {
              val caret = chatInput.modelToView2D(chatInput.getCaretPosition)
              if (caret != null)
                completionPopup.show(chatInput, caret.getBounds.x, caret.getBounds.y + caret.getBounds.height)
            } catch { case _: Exception => }
          }
        }
      }
    })
    
    val inputMap = chatInput.getInputMap(javax.swing.JComponent.WHEN_FOCUSED)
    val actionMap = chatInput.getActionMap()
    
    inputMap.put(javax.swing.KeyStroke.getKeyStroke("ctrl ENTER"), "send")
    actionMap.put("send", new javax.swing.AbstractAction() {
      def actionPerformed(e: java.awt.event.ActionEvent): Unit = sendChat()
    })
    
    inputMap.put(javax.swing.KeyStroke.getKeyStroke("ESCAPE"), "cancel-or-clear")
    actionMap.put("cancel-or-clear", new javax.swing.AbstractAction() {
      def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
        if (AssistantDockable._busy) AssistantDockable.cancel()
        else clearChat()
      }
    })
  }

  private def setupAccessibilityHandlers(): Unit = {
    chatInput.getAccessibleContext.setAccessibleName("Chat input")
    chatInput.getAccessibleContext.setAccessibleDescription("Type your message to the Isabelle Assistant. Enter sends, Shift+Enter for newline.")
    
    sendButton.getAccessibleContext.setAccessibleName("Send message")
    sendButton.getAccessibleContext.setAccessibleDescription("Send your message to the AI assistant")
    
    clearButton.getAccessibleContext.setAccessibleName("Clear conversation")
    clearButton.getAccessibleContext.setAccessibleDescription("Clear the chat history and start fresh")
    
    cancelButton.getAccessibleContext.setAccessibleName("Cancel operation")
    cancelButton.getAccessibleContext.setAccessibleDescription("Cancel the current in-progress operation")
    
    htmlPane.getAccessibleContext.setAccessibleName("Conversation display")
    htmlPane.getAccessibleContext.setAccessibleDescription("Shows the conversation history and AI responses")
    
    statusLabel.getAccessibleContext.setAccessibleName("Status")
    statusLabel.getAccessibleContext.setAccessibleDescription("Current status of the Isabelle Assistant")
    
    modelLabel.getAccessibleContext.setAccessibleName("Model information")
    modelLabel.getAccessibleContext.setAccessibleDescription("Currently selected AI model")
    
    iqStatusLabel.getAccessibleContext.setAccessibleName("I/Q status")
    iqStatusLabel.getAccessibleContext.setAccessibleDescription("Status of the I/Q integration")
    
    setFocusTraversalPolicy(new java.awt.DefaultFocusTraversalPolicy())
    setFocusCycleRoot(true)
    
    sendButton.setMnemonic('S')
    clearButton.setMnemonic('C')
  }

  private def setupStatusHandlers(): Unit = {
    iqStatusLabel.addMouseListener(new java.awt.event.MouseAdapter() {
      override def mouseClicked(e: java.awt.event.MouseEvent): Unit = showAssistantHelp()
    })

    statusSubscription.start()
  }

  private[assistant] def disposeDockable(): Unit = synchronized {
    if (!disposed) {
      disposed = true
      statusSubscription.stop()
      AssistantDockable.clearInstance(this)
    }
  }

  override def exit(): Unit = {
    disposeDockable()
    super.exit()
  }

  private def clearChat(): Unit = {
    ChatAction.clearHistory()
    AssistantDockable.clearInsertActions()
    htmlPane.setText("")
    badgeContainer.setVisible(false)
    welcomeShown = false
    renderedMessageCount = 0
    cardLayout.show(contentPanel, "html")
    chatInput.requestFocus()
  }

  private val maxInputLength = AssistantConstants.MAX_CHAT_CONTEXT_CHARS / 2  // 50K chars max per message

  private def sendChat(): Unit = {
    val message = chatInput.getText.trim
    if (message.nonEmpty) {
      if (message.length > maxInputLength) {
        javax.swing.JOptionPane.showMessageDialog(this,
          s"Message too long (${message.length} chars, max $maxInputLength). Please shorten your message.",
          "Isabelle Assistant", javax.swing.JOptionPane.WARNING_MESSAGE)
      } else {
        chatInput.setText("")
        AssistantDockable.resetCancel()
        ChatAction.chat(view, message)
      }
    }
  }

  def updateBadge(badge: VerificationBadge.BadgeType): Unit = {
    badgeContainer.removeAll()
    badgeContainer.add(VerificationBadge.createBadgePanel(badge), BorderLayout.CENTER)
    badgeContainer.setVisible(true)
    badgeContainer.revalidate()
    badgeContainer.repaint()
    statusLabel.setText(VerificationBadge.toStatus(badge))
  }

  def displayConversation(history: List[ChatAction.Message]): Unit = displayLock.synchronized {
    badgeContainer.setVisible(false)
    
    val welcome = if (history.isEmpty && !welcomeShown) { welcomeShown = true; createWelcomeHtml() } else ""
    
    // Incremental append: if we have a prefix match, append only new messages
    // Synchronized to prevent concurrent updates from desynchronizing count vs. DOM
    val canIncrement = renderedMessageCount > 0 && history.length > renderedMessageCount
    
    if (canIncrement) {
      val newMessages = history.drop(renderedMessageCount)
      val newHtml = newMessages.map { msg =>
        if (msg.role == "user") createUserMessageHtml(msg.content, ChatAction.formatTime(msg.timestamp))
        else createAssistantMessageHtml(msg.content, ChatAction.formatTime(msg.timestamp), msg.rawHtml)
      }.mkString
      
      val doc = htmlPane.getDocument.asInstanceOf[javax.swing.text.html.HTMLDocument]
      try {
        val root = doc.getDefaultRootElement
        var body: javax.swing.text.Element = null
        for (i <- 0 until root.getElementCount if body == null) {
          val child = root.getElement(i)
          if (child.getName == "body") body = child
        }
        if (body != null) {
          doc.insertBeforeEnd(body, newHtml)
          renderedMessageCount = history.length
        } else {
          fullRender(history, welcome)
        }
      } catch {
        case _: Exception => fullRender(history, welcome)
      }
    } else {
      fullRender(history, welcome)
    }
    
    javax.swing.SwingUtilities.invokeLater(() =>
      htmlPane.setCaretPosition(htmlPane.getDocument.getLength))
    cardLayout.show(contentPanel, "html")
  }

  private def fullRender(history: List[ChatAction.Message], welcome: String): Unit = {
    val htmlContent = history.map { msg =>
      if (msg.role == "user") createUserMessageHtml(msg.content, ChatAction.formatTime(msg.timestamp))
      else createAssistantMessageHtml(msg.content, ChatAction.formatTime(msg.timestamp), msg.rawHtml)
    }.mkString
    
    val fullHtml = s"""<html><head><style>
      |body { font-family: 'Segoe UI', 'Helvetica Neue', sans-serif; font-size: 12pt;
      |       margin: 0; padding: 8px; overflow-x: hidden; }
      |a { color: #7b1fa2; }
      |img { max-width: 100%; }
      |table { max-width: 100%; }
      |pre { max-width: 100%; overflow-x: auto; }
      |</style></head><body>$welcome$htmlContent</body></html>""".stripMargin
    
    htmlPane.setText(fullHtml)
    renderedMessageCount = history.length
  }

  def updateStatus(status: String): Unit = {
    val displayStatus = if (AssistantDockable._busy && AssistantDockable._busyStartTime > 0) {
      val elapsed = (System.currentTimeMillis() - AssistantDockable._busyStartTime) / 1000
      if (elapsed >= 2) s"$status (${elapsed}s)" else status
    } else status
    statusLabel.setText(displayStatus)
    cancelButton.setVisible(AssistantDockable._busy)
  }

  def updateAssistantStatus(): Unit = {
    val buffer = view.getBuffer
    val status = AssistantSupport.getStatus(buffer)
    iqStatusLabel.setBackground(AssistantSupport.statusColor(status))
    iqStatusLabel.setForeground(Color.WHITE)
    iqStatusLabel.setText(AssistantSupport.statusText(status))
  }

  def updateIQStatus(): Unit = updateAssistantStatus()

  private def showAssistantHelp(): Unit = {
    val buffer = view.getBuffer
    JOptionPane.showMessageDialog(this, AssistantSupport.helpText(buffer),
      "Isabelle Assistant Help", JOptionPane.INFORMATION_MESSAGE)
  }

  def updateModelLabel(): Unit = {
    val modelId = AssistantOptions.getModelId
    val name = if (modelId.nonEmpty) {
      // Strip CRIS prefix (us./eu./ap.) and provider prefix, show the model name portion
      val stripped = if (modelId.matches("^(us|eu|ap)\\..*")) modelId.dropWhile(_ != '.').drop(1) else modelId
      val afterProvider = if (stripped.contains(".")) stripped.substring(stripped.indexOf('.') + 1) else stripped
      afterProvider.take(30)
    } else "No model"
    modelLabel.setText(name)
    modelLabel.setToolTipText(if (modelId.nonEmpty) s"Model: $modelId" else "No model configured — use :set model <id>")
  }

  private def createUserMessageHtml(content: String, timestamp: String): String = {
    val border = UIColors.ChatBubble.userBorder
    val tsColor = UIColors.ChatBubble.userTimestamp
    s"""<div style='margin:6px 0;padding:8px 10px;background:white;border-left:4px solid $border;border-radius:3px;overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$tsColor;margin-bottom:3px;'><b>You</b> · $timestamp</div>
       |<div>${MarkdownRenderer.toBodyHtml(content)}</div>
       |</div>""".stripMargin
  }

  private def createAssistantMessageHtml(content: String, timestamp: String, rawHtml: Boolean = false): String = {
    val isError = content.startsWith("Error:") || content.startsWith("[FAIL]")
    val body = if (rawHtml) content else {
      val registerAction = (code: String) => {
        val v = view
        AssistantDockable.registerAction(InsertHelper.createInsertAction(v, code))
      }
      val rendered = MarkdownRenderer.toBodyHtmlWithActions(content, registerAction)
      val withLinks = "\\{\\{INSERT:([a-f0-9]+)\\}\\}".r.replaceAllIn(rendered,
        m => s"<a href='action:insert:${m.group(1)}'>[Insert]</a>")
      "\\{\\{ACTION:([a-f0-9]+):([^}]+)\\}\\}".r.replaceAllIn(withLinks,
        m => s"<a href='action:insert:${m.group(1)}'>Run ${m.group(2)}</a>")
    }
    val (border, tsColor) = if (isError) {
      (UIColors.ChatBubble.errorBorder, UIColors.ChatBubble.errorTimestamp)
    } else {
      (UIColors.ChatBubble.assistantBorder, UIColors.ChatBubble.assistantTimestamp)
    }
    s"""<div style='margin:6px 0;padding:8px 10px;background:white;border-left:4px solid $border;border-radius:3px;overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$tsColor;margin-bottom:3px;'><b>Assistant</b> · $timestamp</div>
       |<div>$body</div>
       |</div>""".stripMargin
  }

  private def createWelcomeHtml(): String = {
    val helpId = AssistantDockable.registerAction(() => ChatAction.chat(view, ":help"))
    val wBg = UIColors.Welcome.background
    val wBorder = UIColors.Welcome.border
    val wTitle = UIColors.Welcome.title
    val wText = UIColors.Welcome.text
    val wMuted = UIColors.Welcome.muted
    val codeBg = UIColors.Welcome.codeBackground
    val linkColor = UIColors.Welcome.linkColor
    
    val modelWarning = if (AssistantOptions.getModelId.isEmpty) {
      val eBg = UIColors.ErrorBox.background
      val eBorder = UIColors.ErrorBox.border
      val eText = UIColors.ErrorBox.text
      s"""<div style='margin-top:6px;padding:6px 8px;background:$eBg;border:1px solid $eBorder;border-radius:3px;font-size:11pt;color:$eText;'>
         |No model configured. Use <code style='background:$codeBg;padding:1px 4px;border-radius:2px;'>:set model &lt;model-id&gt;</code> or
         |<b>Plugins → Plugin Options → Isabelle Assistant</b> to set one.
         |Run <code style='background:$codeBg;padding:1px 4px;border-radius:2px;'>:models</code> to see available models.</div>""".stripMargin
    } else ""
    s"""<div style='margin:8px 0;padding:10px 12px;background:$wBg;border:1px solid $wBorder;border-radius:4px;'>
       |<div style='font-weight:bold;color:$wTitle;margin-bottom:4px;'>Isabelle Assistant</div>
       |<div style='color:$wText;font-size:11pt;'>AI assistant for Isabelle/HOL proofs, powered by AWS Bedrock.<br/>
       |Type a message or click <a href='action:insert:$helpId' style='color:$linkColor;text-decoration:none;font-weight:bold;'>:help</a> to see all available commands.
       |<span style='font-size:10pt;color:$wMuted;'>(Enter sends, Shift+Enter for newline)</span></div>
       |$modelWarning
       |</div>""".stripMargin
  }

  override def focusOnDefaultComponent(): Unit = chatInput.requestFocus()
}

/** HTMLEditorKit that resolves latex:// image URLs from MarkdownRenderer's cache. */
class LatexAwareEditorKit extends javax.swing.text.html.HTMLEditorKit {
  override def getViewFactory: javax.swing.text.ViewFactory = new LatexViewFactory(super.getViewFactory)
}

class LatexViewFactory(delegate: javax.swing.text.ViewFactory) extends javax.swing.text.ViewFactory {
  def create(elem: javax.swing.text.Element): javax.swing.text.View = {
    val kind = elem.getName
    if (kind != null && kind.equalsIgnoreCase("img")) {
      val src = elem.getAttributes.getAttribute(javax.swing.text.html.HTML.Attribute.SRC)
      if (src != null && src.toString.startsWith("latex://")) {
        new LatexImageView(elem)
      } else delegate.create(elem)
    } else delegate.create(elem)
  }
}

class LatexImageView(elem: javax.swing.text.Element) extends javax.swing.text.View(elem) {
  private val src = elem.getAttributes.getAttribute(javax.swing.text.html.HTML.Attribute.SRC).toString
  private val img = MarkdownRenderer.getCachedImage(src).orNull

  override def getPreferredSpan(axis: Int): Float = {
    if (img == null) 0f
    else if (axis == javax.swing.text.View.X_AXIS) img.getWidth(null).toFloat
    else img.getHeight(null).toFloat
  }

  override def getMinimumSpan(axis: Int): Float = getPreferredSpan(axis)
  override def getMaximumSpan(axis: Int): Float = getPreferredSpan(axis)

  override def paint(g: java.awt.Graphics, allocation: java.awt.Shape): Unit = {
    if (img != null) {
      val rect = allocation.getBounds
      g.drawImage(img, rect.x, rect.y, null)
    }
  }

  override def modelToView(pos: Int, a: java.awt.Shape, bias: javax.swing.text.Position.Bias): java.awt.Shape = {
    val rect = a.getBounds
    if (pos <= getStartOffset) new java.awt.Rectangle(rect.x, rect.y, 0, rect.height)
    else new java.awt.Rectangle(rect.x + rect.width, rect.y, 0, rect.height)
  }

  override def viewToModel(x: Float, y: Float, a: java.awt.Shape, biasReturn: Array[javax.swing.text.Position.Bias]): Int = {
    val rect = a.getBounds
    biasReturn(0) = javax.swing.text.Position.Bias.Forward
    if (x < rect.x + rect.width / 2) getStartOffset else getEndOffset
  }
}
