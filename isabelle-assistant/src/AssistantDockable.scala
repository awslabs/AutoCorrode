/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.awt.{BorderLayout, CardLayout, Color, FlowLayout}
import javax.swing.{
  BorderFactory,
  JButton,
  JEditorPane,
  JLabel,
  JOptionPane,
  JPanel,
  JScrollPane,
  JTextArea
}
import javax.swing.event.{HyperlinkEvent, HyperlinkListener}

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/** Singleton companion for the Assistant dockable panel. Manages the single
  * instance, insert-action registry, cancellation state, and provides
  * thread-safe methods for updating the UI from background threads.
  */
object AssistantDockable {
  /** Aggregate dockable-wide state: cancellation flag, busy flag, and the
    * wall-clock time the current busy window started. Held in a single
    * AtomicReference so transitions are atomic and cross-thread readers
    * cannot observe inconsistent combinations.
    */
  private[assistant] case class BusyState(cancelled: Boolean, busy: Boolean, busyStartMs: Long)
  private val busyState = new java.util.concurrent.atomic.AtomicReference[BusyState](
    BusyState(cancelled = false, busy = false, busyStartMs = 0L)
  )

  private[assistant] def currentBusyState: BusyState = busyState.get()

  def isCancelled: Boolean = busyState.get().cancelled
  def isBusy: Boolean = busyState.get().busy
  def busyStartMs: Long = busyState.get().busyStartMs

  def cancel(): Unit = {
    val _ = busyState.updateAndGet(s => s.copy(cancelled = true, busy = false))
    setStatus(AssistantConstants.STATUS_CANCELLED)
  }

  def resetCancel(): Unit = {
    val _ = busyState.updateAndGet(_.copy(cancelled = false))
  }

  /** Clear all registered insert actions. Thread-safe with atomic clear. */
  def clearInsertActions(): Unit = AssistantInsertRegistry.clear()

  /** Register an insert action and return its ID for use in hyperlinks. */
  def registerAction(action: () => Unit): String =
    AssistantInsertRegistry.register(action)

  /** Add a chat response with optional clickable insert link */
  def respondInChat(
      text: String,
      insertCode: Option[(String, () => Unit)] = None
  ): Unit = {
    val content = insertCode match {
      case Some((code, action)) =>
        val id = registerAction(action)
        s"$text\n\n```action:$id\n$code\n```"
      case None => text
    }
    ChatAction.addMessage(ChatAction.Assistant, content)
    showConversation(ChatAction.getHistory)
  }

  def showConversation(history: List[ChatAction.Message]): Unit =
    AssistantEventBus.publish(AssistantEvent.ShowConversation(history))

  def setStatus(status: String): Unit =
    setStatus(AssistantStatus.fromText(status))

  def setStatus(status: AssistantStatus): Unit = {
    val statusText = status.text
    val now = System.currentTimeMillis()
    val nowBusy =
      statusText != AssistantConstants.STATUS_READY &&
        statusText != AssistantConstants.STATUS_CANCELLED &&
        !statusText.startsWith("Error")
    val _ = busyState.updateAndGet { prev =>
      // Preserve the previous `busyStartMs` when transitioning to idle:
      // the field is only read while `busy` is true, so retaining it
      // removes a cosmetic ABA window where a quick busy→idle→busy
      // cycle could briefly surface `elapsed = now - 0`.
      val startMs =
        if (nowBusy && !prev.busy) now
        else if (nowBusy) prev.busyStartMs
        else prev.busyStartMs
      prev.copy(busy = nowBusy, busyStartMs = startMs)
    }
    AssistantEventBus.publish(AssistantEvent.StatusUpdate(status))
  }

  def setBadge(badge: VerificationBadge.BadgeType): Unit =
    AssistantEventBus.publish(AssistantEvent.BadgeUpdate(badge))

  def refreshIQStatus(): Unit =
    AssistantEventBus.publish(AssistantEvent.IQStatusRefresh())

  def refreshModelLabel(): Unit =
    AssistantEventBus.publish(AssistantEvent.ModelLabelRefresh())

  /** Allow-list dispatcher for hyperlinks emitted inside the chat panel.
    * `action:insert:<id>` fires a previously registered insert action;
    * `action:copy:<urlencoded-text>` copies the decoded text to the
    * system clipboard. Every other scheme — including `file:`,
    * `http(s):`, `mailto:`, `javascript:` — is refused and logged.
    * Extracted from the Swing listener for testability without a live
    * JEditorPane.
    *
    * @return true when the descriptor matched a supported action,
    *         false otherwise (including null/empty input). */
  private[assistant] def dispatchHyperlink(desc: String): Boolean = {
    if (desc == null || desc.isEmpty) false
    else if (desc.startsWith("action:insert:")) {
      val id = desc.stripPrefix("action:insert:")
      AssistantInsertRegistry.lookup(id).foreach(_())
      true
    } else if (desc.startsWith("action:copy:")) {
      val encoded = desc.stripPrefix("action:copy:")
      try {
        val text = java.net.URLDecoder.decode(encoded, "UTF-8")
        val clipboard =
          java.awt.Toolkit.getDefaultToolkit.getSystemClipboard
        clipboard.setContents(
          new java.awt.datatransfer.StringSelection(text),
          null
        )
        true
      } catch {
        case _: IllegalArgumentException =>
          ErrorHandler.safeWarn(
            s"[Assistant] Ignoring copy link with malformed URL-encoded payload"
          )
          false
        case _: LinkageError =>
          // No AWT at all (obscure classloader setups). Treat as a
          // successful dispatch for routing purposes so callers can
          // distinguish from "rejected scheme".
          true
        case _: java.awt.HeadlessException =>
          // Headless JVM (tests, CI). Same treatment as above.
          true
      }
    } else {
      ErrorHandler.safeWarn(
        s"[Assistant] Ignoring hyperlink with unsupported scheme: ${desc.take(64)}"
      )
      false
    }
  }

  /** Global teardown hook used from plugin stop to avoid leaked dockable
    * state/subscriptions.
    */
  def shutdown(): Unit = {
    // Instances clean themselves up via the event bus; just reset
    // the shared static state.
    clearInsertActions()
    busyState.set(BusyState(cancelled = false, busy = false, busyStartMs = 0L))
  }
}

/** Chat UI panel docked in Isabelle/jEdit. Renders conversation history as
  * styled HTML, provides chat input with keyboard shortcuts, status indicators
  * for I/Q and model, and clickable insert links for generated code.
  */
class AssistantDockable(view: View, position: String)
    extends Dockable(view, position) {

  private val eventBusListener: AssistantEvent => Unit = {
    case AssistantEvent.StatusUpdate(status) =>
      GUI_Thread.later { updateStatus(status.text) }
    case AssistantEvent.BadgeUpdate(badge) =>
      GUI_Thread.later { updateBadge(badge) }
    case AssistantEvent.ShowConversation(history) =>
      GUI_Thread.later { displayConversation(history) }
    case AssistantEvent.IQStatusRefresh() =>
      GUI_Thread.later { updateAssistantStatus() }
    case AssistantEvent.ModelLabelRefresh() =>
      GUI_Thread.later { updateModelLabel() }
    case _ => // Optional Catch-all
  }
  AssistantEventBus.subscribe(eventBusListener)

  private[this] val statusSubscription =
    AssistantStatusSubscription.create(
      PIDE.session,
      s"assistant-status-${System.identityHashCode(this)}",
      _ => GUI_Thread.later { updateAssistantStatus() }
    )
  @volatile private[this] var disposed = false

  MarkdownRenderer.setSyntheticImageReadyCallback(() => {
    if (!disposed) AssistantDockable.showConversation(ChatAction.getHistory)
  })

  // Display state — MUST be declared before initializeUI() runs
  private val displayLock = new Object()
  @volatile private var renderedMessageCount = 0
  @volatile private var welcomeShown = false

  // Input history navigation
  private val inputHistory = new InputHistoryBuffer()
  @volatile private var lastEscapeTime: Long = 0L     // For double-tap Escape

  // UI Components
  private val badgeWidget = new VerificationBadge.BadgeWidget()
  private val badgeContainer = createBadgeContainer()
  private val htmlPane = createHtmlPane()
  private val cardLayout = new CardLayout()
  private val contentPanel = createContentPanel()
  private val mainPanel = createMainPanel()
  private val (iqStatusLabel, modelLabel) = createStatusLabels()
  private val contextBar = new ContextBarPanel()
  private val (statusLabel, cancelButton, clearButton) = createControlElements()
  private val topPanel = createTopPanel()
  private val (chatInput, sendButton, inputPanel) = createInputPanel()

  // Spinner frames: cycled on a Swing Timer. Repaints only the status label
  // text so it is cheap even at ~100 ms intervals. The Braille glyphs look
  // great when the label's font can render them, but on stripped-down
  // environments they come out as tofu boxes — fall back to an ASCII
  // spinner when the active font lacks Braille coverage.
  private val BrailleSpinnerFrames = Array("⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏")
  private val AsciiSpinnerFrames   = Array("|", "/", "-", "\\")
  private val SpinnerFrames: Array[String] = {
    try {
      val font = javax.swing.UIManager.getFont("Label.font")
      // canDisplayUpTo returns -1 when every code point fits.
      if (font != null && font.canDisplayUpTo("⠋") == -1) BrailleSpinnerFrames
      else AsciiSpinnerFrames
    } catch {
      case _: Throwable => AsciiSpinnerFrames
    }
  }
  @volatile private var spinnerFrame: Int = 0
  @volatile private var lastStatusText: String = AssistantConstants.STATUS_READY
  private val spinnerTimer = new javax.swing.Timer(100, _ => {
    spinnerFrame = (spinnerFrame + 1) % SpinnerFrames.length
    updateStatus(lastStatusText)
  })

  // Initialize UI
  initializeUI()
  initializeEventHandlers()

  private def createBadgeContainer(): JPanel = {
    val container = new JPanel(new BorderLayout())
    container.setVisible(false)
    container.setBorder(
      BorderFactory.createMatteBorder(
        0,
        0,
        1,
        0,
        javax.swing.UIManager.getColor("Separator.foreground")
      )
    )
    container.add(badgeWidget, BorderLayout.CENTER)
    container
  }

  private def createHtmlPane(): JEditorPane = {
    val pane = new JEditorPane()
    pane.setEditorKit(new SyntheticImageAwareEditorKit())
    pane.setEditable(false)
    pane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, true)
    pane.addHyperlinkListener(new HyperlinkListener {
      def hyperlinkUpdate(e: HyperlinkEvent): Unit = {
        if (e.getEventType == HyperlinkEvent.EventType.ACTIVATED)
          val _ = AssistantDockable.dispatchHyperlink(e.getDescription)
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
    iqStatus.setBorder(BorderFactory.createEmptyBorder(UIDesign.sp(2), UIDesign.sp(4), UIDesign.sp(2), UIDesign.sp(4)))
    iqStatus.setToolTipText("Click to view assistant capabilities and setup")
    iqStatus.setCursor(java.awt.Cursor.getPredefinedCursor(java.awt.Cursor.HAND_CURSOR))

    val model = new JLabel("Model: Loading…")
    model.setBorder(BorderFactory.createEmptyBorder(UIDesign.sp(2), UIDesign.sp(4), UIDesign.sp(2), UIDesign.sp(4)))

    (iqStatus, model)
  }


  /** Apply consistent top-bar button styling (font, border, background, hover).
    */
  private def styleTopButton(btn: JButton): Unit = {
    btn.setFocusPainted(true)
    btn.setFont(btn.getFont.deriveFont(UIDesign.fp(11f)))
    btn.setBorder(
      BorderFactory.createCompoundBorder(
        BorderFactory.createLineBorder(
          java.awt.Color.decode(UIColors.TopButton.border),
          UIDesign.sp(1),
          true
        ),
        BorderFactory.createEmptyBorder(UIDesign.sp(2), UIDesign.sp(8), UIDesign.sp(2), UIDesign.sp(8))
      )
    )
    btn.setBackground(java.awt.Color.decode(UIColors.TopButton.background))
    btn.setForeground(javax.swing.UIManager.getColor("Button.foreground"))
    btn.setCursor(
      java.awt.Cursor.getPredefinedCursor(java.awt.Cursor.HAND_CURSOR)
    )
    btn.addMouseListener(new java.awt.event.MouseAdapter {
      override def mouseEntered(e: java.awt.event.MouseEvent): Unit =
        btn.setBackground(
          java.awt.Color.decode(UIColors.TopButton.hoverBackground)
        )
      override def mouseExited(e: java.awt.event.MouseEvent): Unit =
        btn.setBackground(java.awt.Color.decode(UIColors.TopButton.background))
    })
  }

  private def createControlElements(): (JLabel, JButton, JButton) = {
    val status = new JLabel(AssistantConstants.STATUS_READY)

    val cancel = new JButton("Cancel")
    cancel.setVisible(false)
    styleTopButton(cancel)

    val clear = new JButton("Clear")
    styleTopButton(clear)

    (status, cancel, clear)
  }

  private def createTopPanel(): JPanel = {
    val panel = new JPanel(new BorderLayout())
    val leftPanel = new JPanel(new FlowLayout(FlowLayout.LEFT, 4, 2))
    leftPanel.add(iqStatusLabel)
    leftPanel.add(modelLabel)
    leftPanel.add(contextBar)

    val rightPanel = new JPanel(new FlowLayout(FlowLayout.RIGHT))
    rightPanel.add(statusLabel)
    rightPanel.add(cancelButton)
    rightPanel.add(clearButton)

    panel.add(leftPanel, BorderLayout.WEST)
    panel.add(rightPanel, BorderLayout.EAST)
    panel
  }

  private def createInputPanel(): (JTextArea, JButton, JPanel) = {
    val input = new JTextArea(
      AssistantConstants.CHAT_INPUT_ROWS,
      AssistantConstants.CHAT_INPUT_COLUMNS
    )
    input.setLineWrap(true)
    input.setWrapStyleWord(true)
    input.setFont(javax.swing.UIManager.getFont("TextField.font"))
    // Right padding leaves room for the send-button overlay; other sides are grid-aligned.
    input.setBorder(BorderFactory.createEmptyBorder(
      UIDesign.sp(8), UIDesign.sp(12), UIDesign.sp(8), UIDesign.sp(40)
    ))
    input.setBackground(Color.decode(UIColors.ChatInput.background))

    // Placeholder label overlay (shows "Ask a question…" when empty)
    val placeholder = new JLabel(AssistantConstants.CHAT_INPUT_PLACEHOLDER)
    placeholder.setFont(input.getFont)
    placeholder.setForeground(Color.decode(UIColors.ChatInput.placeholder))
    placeholder.setVisible(input.getText.isEmpty)

    // Update placeholder visibility based on text content
    input.getDocument.addDocumentListener(
      new javax.swing.event.DocumentListener {
        def insertUpdate(e: javax.swing.event.DocumentEvent): Unit =
          placeholder.setVisible(input.getText.isEmpty)
        def removeUpdate(e: javax.swing.event.DocumentEvent): Unit =
          placeholder.setVisible(input.getText.isEmpty)
        def changedUpdate(e: javax.swing.event.DocumentEvent): Unit = {}
      }
    )
    input.addFocusListener(new java.awt.event.FocusAdapter {
      override def focusGained(e: java.awt.event.FocusEvent): Unit =
        placeholder.setVisible(false)
      override def focusLost(e: java.awt.event.FocusEvent): Unit =
        placeholder.setVisible(input.getText.isEmpty)
    })

    // Vector-painted send button: a right-pointing triangle on a round pill,
    // anti-aliased via Graphics2D so it's crisp at any DPI. Avoids the
    // tofu/glyph-rendering risks of relying on a Unicode arrow character.
    val sendSize = UIDesign.sp(28)
    val send = new JButton() {
      private var hovered = false
      setHovered(false)
      private def setHovered(b: Boolean): Unit = { hovered = b; repaint() }
      addMouseListener(new java.awt.event.MouseAdapter {
        override def mouseEntered(e: java.awt.event.MouseEvent): Unit = setHovered(true)
        override def mouseExited(e: java.awt.event.MouseEvent): Unit  = setHovered(false)
      })
      override def paintComponent(g: java.awt.Graphics): Unit = {
        val g2 = g.asInstanceOf[java.awt.Graphics2D]
        g2.setRenderingHint(
          java.awt.RenderingHints.KEY_ANTIALIASING,
          java.awt.RenderingHints.VALUE_ANTIALIAS_ON
        )
        val w = getWidth
        val h = getHeight
        // Pill background (only visible when hovered)
        if (hovered) {
          g2.setColor(Color.decode(UIColors.ChatInput.sendButtonHoverBackground))
          g2.fillOval(0, 0, w - 1, h - 1)
        }
        // Filled right-pointing triangle, geometry-based so it scales on HiDPI.
        val glyphColor =
          if (hovered) Color.decode(UIColors.ChatInput.sendButtonHover)
          else Color.decode(UIColors.ChatInput.sendButton)
        g2.setColor(glyphColor)
        val pad = w / 4
        val xs = Array(pad, pad, w - pad)
        val ys = Array(pad, h - pad, h / 2)
        g2.fillPolygon(xs, ys, 3)
      }
    }
    send.setToolTipText("Send message (Enter). Shift+Enter for newline. Ctrl+. to cancel.")
    send.setPreferredSize(new java.awt.Dimension(sendSize, sendSize))
    send.setMinimumSize(new java.awt.Dimension(sendSize, sendSize))
    send.setMaximumSize(new java.awt.Dimension(sendSize, sendSize))
    send.setMargin(new java.awt.Insets(0, 0, 0, 0))
    send.setFocusable(true)
    send.setContentAreaFilled(false)
    send.setBorderPainted(false)
    send.setBorder(BorderFactory.createEmptyBorder())
    send.setCursor(java.awt.Cursor.getPredefinedCursor(java.awt.Cursor.HAND_CURSOR))

    // Rounded border with focus ring support
    val normalBorder = BorderFactory.createLineBorder(
      Color.decode(UIColors.ChatInput.border),
      UIDesign.sp(1),
      true
    )
    val focusBorder = BorderFactory.createLineBorder(
      Color.decode(UIColors.ChatInput.focusBorder),
      UIDesign.sp(2),
      true
    )

    val scrollPane = new JScrollPane(input)
    scrollPane.setBorder(normalBorder)
    scrollPane.setVerticalScrollBarPolicy(
      javax.swing.ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED
    )

    // Focus ring - swap border on focus/blur
    input.addFocusListener(new java.awt.event.FocusAdapter {
      override def focusGained(e: java.awt.event.FocusEvent): Unit =
        scrollPane.setBorder(focusBorder)
      override def focusLost(e: java.awt.event.FocusEvent): Unit =
        scrollPane.setBorder(normalBorder)
    })

    // Layered panel with overlapping children (placeholder, send button over
    // scroll pane). Layout is metrics-driven so it stays correct across fonts
    // and HiDPI scaling.
    val layered = new JPanel(null) {
      override def isOptimizedDrawingEnabled: Boolean = false // Fix for overlapping repaints
      override def getPreferredSize: java.awt.Dimension =
        scrollPane.getPreferredSize
      override def doLayout(): Unit = {
        val w = getWidth
        val h = getHeight
        scrollPane.setBounds(0, 0, w, h)

        // Placeholder aligns with the input's actual text insets and font baseline.
        val fm = input.getFontMetrics(input.getFont)
        val inputInsets = input.getInsets
        val padL = inputInsets.left
        val padT = inputInsets.top
        val btnSz = send.getPreferredSize.width
        val gap = UIDesign.sp(8)
        placeholder.setBounds(padL, padT, math.max(0, w - padL - btnSz - gap * 2), fm.getHeight)

        // Send button anchored to the bottom-right with a uniform gap.
        val bw = send.getPreferredSize.width
        val bh = send.getPreferredSize.height
        send.setBounds(w - bw - gap, h - bh - gap, bw, bh)
      }
    }
    layered.add(placeholder) // overlay on top
    layered.add(send) // overlay on top
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
    // Non-focus-stealing auto-completion using JWindow
    val popup = new CompletionPopupManager(
      chatInput, inputPanel,
      () => javax.swing.SwingUtilities.getWindowAncestor(this)
    )

    // Document listener to update completion popup as user types
    chatInput.getDocument.addDocumentListener(
      new javax.swing.event.DocumentListener {
        def insertUpdate(e: javax.swing.event.DocumentEvent): Unit =
          popup.updateCompletions()
        def removeUpdate(e: javax.swing.event.DocumentEvent): Unit =
          popup.updateCompletions()
        def changedUpdate(e: javax.swing.event.DocumentEvent): Unit = {}
      }
    )

    // Focus listener to hide popup when input loses focus
    chatInput.addFocusListener(new java.awt.event.FocusAdapter {
      override def focusLost(e: java.awt.event.FocusEvent): Unit =
        popup.hide()
    })

    val inputMap = chatInput.getInputMap(javax.swing.JComponent.WHEN_FOCUSED)
    val actionMap = chatInput.getActionMap()

    // Use key bindings (instead of KeyListener) for reliable cross-platform handling.
    inputMap.put(javax.swing.KeyStroke.getKeyStroke("ENTER"), "send-or-complete")
    // Explicitly map Shift+Enter to insert-break for cross-platform consistency
    inputMap.put(javax.swing.KeyStroke.getKeyStroke("shift ENTER"), "insert-break")

    inputMap.put(javax.swing.KeyStroke.getKeyStroke("ctrl ENTER"), "send")
    inputMap.put(javax.swing.KeyStroke.getKeyStroke("TAB"), "accept-completion")

    // Platform-neutral "cancel current operation" shortcut. Cross-platform
    // Ctrl+. is a familiar "stop" binding; on macOS the menu accelerator
    // mask (Cmd) also maps to the same behaviour so users can keep the
    // muscle memory of Cmd+. from AppKit.
    val menuMask = java.awt.Toolkit.getDefaultToolkit.getMenuShortcutKeyMaskEx
    inputMap.put(javax.swing.KeyStroke.getKeyStroke("ctrl PERIOD"), "assistant-cancel")
    inputMap.put(
      javax.swing.KeyStroke.getKeyStroke(java.awt.event.KeyEvent.VK_PERIOD, menuMask),
      "assistant-cancel"
    )
    actionMap.put(
      "assistant-cancel",
      new javax.swing.AbstractAction() {
        def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
          if (AssistantDockable.isBusy) AssistantDockable.cancel()
        }
      }
    )

    actionMap.put(
      "send-or-complete",
      new javax.swing.AbstractAction() {
        def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
          if (popup.isVisible) popup.acceptSelected()
          else sendChat()
        }
      }
    )

    actionMap.put(
      "send",
      new javax.swing.AbstractAction() {
        def actionPerformed(e: java.awt.event.ActionEvent): Unit = sendChat()
      }
    )

    actionMap.put(
      "accept-completion",
      new javax.swing.AbstractAction() {
        def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
          if (popup.isVisible) popup.acceptSelected()
        }
      }
    )

    inputMap.put(
      javax.swing.KeyStroke.getKeyStroke("ESCAPE"),
      "cancel-or-clear"
    )
    actionMap.put(
      "cancel-or-clear",
      new javax.swing.AbstractAction() {
        def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
          if (popup.isVisible) {
            popup.hide()
          } else {
            val now = System.currentTimeMillis()
            if (AssistantDockable.isBusy) {
              AssistantDockable.cancel()
            } else if (chatInput.getText.trim.nonEmpty) {
              chatInput.setText("")
              inputHistory.resetNavigation()
              lastEscapeTime = now
            } else if (now - lastEscapeTime < 400) {
              clearChat()
              lastEscapeTime = 0L
            } else {
              // Input already empty, single Esc — still clear conversation for backward compat
              clearChat()
            }
          }
        }
      }
    )

    // Save original caret-up / caret-down actions for delegation
    val originalUp = actionMap.get("caret-up")
    val originalDown = actionMap.get("caret-down")

    inputMap.put(javax.swing.KeyStroke.getKeyStroke("UP"), "completion-or-history-up")
    actionMap.put("completion-or-history-up", new javax.swing.AbstractAction() {
      def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
        if (popup.isVisible) popup.navigateUp()
        else if (isCaretOnFirstLine) navigateHistoryBack()
        else if (originalUp != null) originalUp.actionPerformed(e)
      }
    })

    inputMap.put(javax.swing.KeyStroke.getKeyStroke("DOWN"), "completion-or-history-down")
    actionMap.put("completion-or-history-down", new javax.swing.AbstractAction() {
      def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
        if (popup.isVisible) popup.navigateDown()
        else if (isCaretOnLastLine) navigateHistoryForward()
        else if (originalDown != null) originalDown.actionPerformed(e)
      }
    })
  }

  private def setupAccessibilityHandlers(): Unit = {
    chatInput.getAccessibleContext.setAccessibleName("Chat input")
    chatInput.getAccessibleContext.setAccessibleDescription(
      "Type your message to the Isabelle Assistant. Enter sends, Shift+Enter for newline."
    )

    sendButton.getAccessibleContext.setAccessibleName("Send message")
    sendButton.getAccessibleContext.setAccessibleDescription(
      "Send your message to the AI assistant"
    )

    clearButton.getAccessibleContext.setAccessibleName("Clear conversation")
    clearButton.getAccessibleContext.setAccessibleDescription(
      "Clear the chat history and start fresh"
    )

    cancelButton.getAccessibleContext.setAccessibleName("Cancel operation")
    cancelButton.getAccessibleContext.setAccessibleDescription(
      "Cancel the current in-progress operation"
    )

    htmlPane.getAccessibleContext.setAccessibleName("Conversation display")
    htmlPane.getAccessibleContext.setAccessibleDescription(
      "Shows the conversation history and AI responses"
    )

    statusLabel.getAccessibleContext.setAccessibleName("Status")
    statusLabel.getAccessibleContext.setAccessibleDescription(
      "Current status of the Isabelle Assistant"
    )

    modelLabel.getAccessibleContext.setAccessibleName("Model information")
    modelLabel.getAccessibleContext.setAccessibleDescription(
      "Currently selected AI model"
    )

    iqStatusLabel.getAccessibleContext.setAccessibleName("I/Q status")
    iqStatusLabel.getAccessibleContext.setAccessibleDescription(
      "Status of the I/Q integration. Click to view assistant capabilities."
    )

    contextBar.getAccessibleContext.setAccessibleName("Context usage meter")
    contextBar.getAccessibleContext.setAccessibleDescription(
      "Shows the fraction of the model's context budget used by the current conversation."
    )

    badgeContainer.getAccessibleContext.setAccessibleName("Verification status")
    badgeContainer.getAccessibleContext.setAccessibleDescription(
      "Shows the verification outcome of the most recent proof attempt."
    )

    // Mirror the status label's accessible description into a tooltip so
    // mouse and keyboard users see the same information.
    statusLabel.setToolTipText("Current status of the Isabelle Assistant")

    setFocusTraversalPolicy(new java.awt.DefaultFocusTraversalPolicy())
    setFocusCycleRoot(true)

    sendButton.setMnemonic('S')
    clearButton.setMnemonic('C')
  }

  private def setupStatusHandlers(): Unit = {
    iqStatusLabel.addMouseListener(new java.awt.event.MouseAdapter() {
      override def mouseClicked(e: java.awt.event.MouseEvent): Unit =
        showAssistantHelp()
    })

    statusSubscription.start()
  }

  private[assistant] def disposeDockable(): Unit = synchronized {
    if (!disposed) {
      disposed = true
      statusSubscription.stop()
      AssistantEventBus.unsubscribe(eventBusListener)
      MarkdownRenderer.setSyntheticImageReadyCallback(() => ())
      if (spinnerTimer.isRunning) spinnerTimer.stop()
    }
  }

  override def exit(): Unit = {
    disposeDockable()
    super.exit()
  }

  private def clearChat(): Unit = {
    ChatAction.clearHistory()
    AssistantDockable.clearInsertActions()
    ToolPermissions.clearSession()
    TaskList.clear()
    badgeContainer.setVisible(false)
    welcomeShown = false
    renderedMessageCount = 0
    inputHistory.clear()
    contextBar.reset()
    // Re-synchronise the status label with the empty conversation so
    // the previous operation's text (e.g. "Thinking…") doesn't linger
    // into the fresh session.
    lastStatusText = AssistantConstants.STATUS_READY
    updateStatus(lastStatusText)
    cardLayout.show(contentPanel, "html")
    // Re-render through the normal path so the welcome card comes back
    // and the document is rebuilt with our canonical CSS. Setting
    // htmlPane.setText("") directly leaves JEditorPane's HTMLEditorKit
    // with a default empty paragraph that styles through the prior CSS
    // and surfaces as an empty bubble.
    displayConversation(ChatAction.getHistory)
    chatInput.requestFocus()
  }

  // `getLineOfOffset` is the only documented failure path here; a typed
  // catch keeps us from swallowing unrelated bugs (NPE, etc.) as "caret
  // at edge". On BadLocationException the caret is in an undefined state
  // so defaulting to `true` (the caller then routes to history navigation)
  // is the safe choice.
  private def isCaretOnFirstLine: Boolean = {
    try {
      val caretPos = chatInput.getCaretPosition
      chatInput.getLineOfOffset(caretPos) == 0
    } catch { case _: javax.swing.text.BadLocationException => true }
  }

  private def isCaretOnLastLine: Boolean = {
    try {
      val caretPos = chatInput.getCaretPosition
      chatInput.getLineOfOffset(caretPos) == chatInput.getLineCount - 1
    } catch { case _: javax.swing.text.BadLocationException => true }
  }

  private def navigateHistoryBack(): Unit =
    inputHistory.navigateBack(chatInput.getText).foreach { entry =>
      chatInput.setText(entry)
      chatInput.setCaretPosition(entry.length)
    }

  private def navigateHistoryForward(): Unit =
    inputHistory.navigateForward().foreach { entry =>
      chatInput.setText(entry)
      chatInput.setCaretPosition(entry.length)
    }

  private val maxInputLength =
    AssistantConstants.MAX_CHAT_CONTEXT_CHARS / 2 // 50K chars max per message

  /** Rough chars-per-token heuristic shared with `ContextTracker` so
    * the near-limit warning agrees with the context bar. Actual tokens
    * depend on the tokenizer, but within 20% is fine for a non-blocking
    * hint. */
  private val charsPerTokenHeuristic = 4

  private def sendChat(): Unit = {
    val message = chatInput.getText.trim
    if (message.nonEmpty) {
      if (message.length > maxInputLength) {
        javax.swing.JOptionPane.showMessageDialog(
          this,
          s"Message too long (${"%,d".format(message.length)} chars, max ${"%,d".format(maxInputLength)}). Please shorten your message.",
          "Isabelle Assistant",
          javax.swing.JOptionPane.WARNING_MESSAGE
        )
      } else {
        val modelCtxTokens = AssistantOptions.getMaxContextTokens
        val estTokens = message.length / charsPerTokenHeuristic
        if (modelCtxTokens > 0 && estTokens > 0.8 * modelCtxTokens) {
          // Non-blocking tooltip update: no modal dialog, no send block.
          // If the user proceeds, the backend will still apply its own
          // truncation.
          val warn =
            s"Near context limit: ~${"%,d".format(estTokens)} tokens / ${"%,d".format(modelCtxTokens)}"
          statusLabel.setToolTipText(warn)
          ErrorHandler.safeLog(s"[Assistant] $warn")
        }
        chatInput.setText("")
        inputHistory.record(message)
        AssistantDockable.resetCancel()
        ChatAction.chat(view, message)
      }
    }
  }

  def updateBadge(badge: VerificationBadge.BadgeType): Unit = {
    badgeWidget.updateBadge(badge)
    badgeContainer.setVisible(true)
    statusLabel.setText(VerificationBadge.toStatus(badge))
  }

  /** Render a single chat message to HTML. Shared by incremental and full render. */
  private def renderSingleMessage(
      msg: ChatAction.Message,
      registerAction: String => String
  ): String = {
    msg.role match {
      case ChatAction.User =>
        ConversationRenderer.createUserMessageHtml(
          msg.content,
          ChatAction.formatTime(msg.timestamp)
        )
      case ChatAction.Widget =>
        msg.content // Widget role: raw HTML, no wrapper
      case ChatAction.Tool =>
        // Parse tool message content: "toolName|||{json params}"
        val parts = msg.content.split("\\|\\|\\|", 2)
        if (parts.length == 2) {
          try {
            val toolName = parts(0)
            val paramsJson = parts(1)
            val params =
              ResponseParser.parseToolArgsJsonObject(paramsJson)
            ConversationRenderer.createToolMessageHtml(
              toolName,
              params,
              ChatAction.formatTime(msg.timestamp)
            )
          } catch {
            case _: Exception =>
              ConversationRenderer.createAssistantMessageHtml(
                msg.content,
                ChatAction.formatTime(msg.timestamp),
                msg.rawHtml,
                registerAction,
                msg.kind
              )
          }
        } else
          ConversationRenderer.createAssistantMessageHtml(
            msg.content,
            ChatAction.formatTime(msg.timestamp),
            msg.rawHtml,
            registerAction,
            msg.kind
          )
      case _ =>
        ConversationRenderer.createAssistantMessageHtml(
          msg.content,
          ChatAction.formatTime(msg.timestamp),
          msg.rawHtml,
          registerAction,
          msg.kind
        )
    }
  }

  def displayConversation(history: List[ChatAction.Message]): Unit =
    displayLock.synchronized {
      badgeContainer.setVisible(false)

      // Render the welcome card whenever the conversation is empty (fresh
      // session, after :clear, or simply reopening the dockable) rather than
      // only on first load. `welcomeShown` still guards the per-reopen state
      // used by the incremental-append path below so we don't render it
      // twice when a message lands.
      val welcome = if (history.isEmpty) {
        welcomeShown = true
        ConversationRenderer.createWelcomeHtml(
          () => AssistantDockable.registerAction(() => ChatAction.chat(view, ":help")),
          Some((cmd: String) => AssistantDockable.registerAction(() => ChatAction.chat(view, cmd)))
        )
      } else ""

      // Incremental append: if we have a prefix match, append only new messages
      // Synchronized to prevent concurrent updates from desynchronizing count vs. DOM
      val canIncrement =
        renderedMessageCount > 0 && history.length > renderedMessageCount

      if (canIncrement) {
        val registerAction = (code: String) =>
          AssistantDockable.registerAction(
            InsertHelper.createInsertAction(view, code)
          )
        val newMessages = history.drop(renderedMessageCount)
        val newHtml = newMessages.map(renderSingleMessage(_, registerAction)).mkString

        // Sanity-parse the fragment into a scratch document before we
        // splice it into the live DOM. Unclosed tags or other malformed
        // markup can otherwise leave the live HTMLDocument in a
        // half-constructed state that no subsequent render can recover.
        if (!isParsableFragment(newHtml)) {
          fullRender(history, welcome)
        } else {
          val doc =
            htmlPane.getDocument.asInstanceOf[javax.swing.text.html.HTMLDocument]
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
        }
      } else {
        fullRender(history, welcome)
      }

      // Update context bar
      updateContextBar(history)

      javax.swing.SwingUtilities.invokeLater(() =>
        htmlPane.setCaretPosition(htmlPane.getDocument.getLength)
      )
      cardLayout.show(contentPanel, "html")
    }

  /** Pre-flight check for `HTMLDocument.insertBeforeEnd`. Parses the
    * fragment into a throwaway document wrapped in an HTML shell; if the
    * parse throws, we fall back to a full re-render rather than risk
    * corrupting the live DOM with an unclosed tag. Always returns true on
    * empty input — there's nothing to splice. */
  private def isParsableFragment(fragment: String): Boolean = {
    if (fragment == null || fragment.isEmpty) true
    else {
      try {
        val kit = new javax.swing.text.html.HTMLEditorKit()
        val scratch = kit.createDefaultDocument()
        val wrapped = s"<html><body>$fragment</body></html>"
        kit.read(new java.io.StringReader(wrapped), scratch, 0)
        true
      } catch {
        case _: Exception => false
      }
    }
  }

  private def fullRender(
      history: List[ChatAction.Message],
      welcome: String
  ): Unit = {
    val registerAction = (code: String) =>
      AssistantDockable.registerAction(
        InsertHelper.createInsertAction(view, code)
      )
    val htmlContent = history.map(renderSingleMessage(_, registerAction)).mkString

    val fullHtml = s"""<html><head><style>
      |body { font-family: 'Segoe UI', 'Helvetica Neue', sans-serif; font-size: ${UIDesign.FontSize.md};
      |       margin: 0; padding: ${UIDesign.Space.md}; overflow-x: hidden; }
      |a { color: ${UIColors.linkColor}; text-decoration: none; }
      |a:hover { text-decoration: underline; }
      |img { max-width: 100%; }
      |table { max-width: 100%; }
      |pre { max-width: 100%; overflow-x: auto; }
      |</style></head><body>$welcome$htmlContent</body></html>""".stripMargin

    htmlPane.setText(fullHtml)
    renderedMessageCount = history.length
  }

  def updateStatus(status: String): Unit = {
    lastStatusText = status
    val snapshot = AssistantDockable.currentBusyState
    val displayStatus =
      if (snapshot.busy && snapshot.busyStartMs > 0) {
        val elapsed = (System.currentTimeMillis() - snapshot.busyStartMs) / 1000
        if (elapsed >= 2) s"$status (${elapsed}s)" else status
      } else status

    // Per-state glyph gives colorblind + screen-reader users a second channel
    // alongside colour. Busy states animate through a braille spinner driven
    // by spinnerTimer; idle states are static glyphs.
    val isError = status.startsWith("Error") || status.startsWith("[FAIL]")
    val isReady = status == AssistantConstants.STATUS_READY ||
      status == AssistantConstants.STATUS_CANCELLED
    val (glyph, color) =
      if (isError) ("✖", UIColors.StatusDot.error)
      else if (isReady) ("✓", UIColors.StatusDot.ready)
      else (SpinnerFrames(spinnerFrame), UIColors.StatusDot.busy)

    if (snapshot.busy && !spinnerTimer.isRunning) spinnerTimer.start()
    else if (!snapshot.busy && spinnerTimer.isRunning) spinnerTimer.stop()

    val htmlStatus =
      s"<html><span style='color:$color;font-weight:bold;'>$glyph</span> $displayStatus</html>"
    statusLabel.setText(htmlStatus)
    cancelButton.setVisible(snapshot.busy)
  }

  def updateAssistantStatus(): Unit = {
    val buffer = view.getBuffer
    val status = AssistantSupport.getStatus(buffer)
    // Use modern light-tinted badge style instead of solid color blocks
    val (bgColor, textColor, borderColor) = status match {
      case AssistantSupport.FullSupport =>
        (
          UIColors.Badge.successBackground,
          UIColors.Badge.successText,
          UIColors.Badge.successBorder
        )
      case AssistantSupport.PartialSupport =>
        (
          UIColors.Badge.warningBackground,
          UIColors.Badge.warningText,
          UIColors.Badge.warningBorder
        )
      case AssistantSupport.NoSupport =>
        (
          UIColors.Badge.neutralBackground,
          UIColors.Badge.neutralText,
          UIColors.Badge.neutralBorder
        )
    }
    iqStatusLabel.setBackground(Color.decode(bgColor))
    iqStatusLabel.setForeground(Color.decode(textColor))
    iqStatusLabel.setBorder(
      BorderFactory.createCompoundBorder(
        BorderFactory.createLineBorder(Color.decode(borderColor), 1, true),
        BorderFactory.createEmptyBorder(3, 8, 3, 8)
      )
    )
    iqStatusLabel.setText(AssistantSupport.statusText(status))
  }

  private def showAssistantHelp(): Unit = {
    val buffer = view.getBuffer
    val body = AssistantSupport.helpText(buffer) +
      "\n\nKeyboard shortcuts: Enter sends, Shift+Enter for newline, Ctrl+. to cancel a running operation."
    JOptionPane.showMessageDialog(
      this,
      body,
      "Isabelle Assistant Help",
      JOptionPane.INFORMATION_MESSAGE
    )
  }

  def updateModelLabel(): Unit = {
    val modelId = AssistantOptions.getModelId
    val (display, tooltip) = if (modelId.nonEmpty) {
      // Strip CRIS prefix (us./eu./ap.) and provider prefix, show the model name portion
      val stripped =
        if (modelId.matches("^(us|eu|ap)\\..*"))
          modelId.dropWhile(_ != '.').drop(1)
        else modelId
      val afterProvider =
        if (stripped.contains("."))
          stripped.substring(stripped.indexOf('.') + 1)
        else stripped
      val shortName = HtmlUtil.escapeHtml(afterProvider.take(30))
      val escapedModelId = HtmlUtil.escapeHtml(modelId)
      val mutedColor = UIColors.ModelLabel.muted
      val sz = UIDesign.FontSize.sm
      (
        s"<html><span style='color:$mutedColor;font-size:$sz;'>Model:</span> <b style='font-size:$sz;'>$shortName</b></html>",
        s"Model: $escapedModelId"
      )
    } else {
      val mutedColor = UIColors.ModelLabel.muted
      val unconfiguredColor = UIColors.ModelLabel.unconfigured
      val sz = UIDesign.FontSize.sm
      (
        s"<html><span style='color:$mutedColor;font-size:$sz;'>Model:</span> <b style='font-size:$sz;color:$unconfiguredColor;'>Not configured</b></html>",
        "No model configured — use :set model <id>"
      )
    }
    modelLabel.setText(display)
    modelLabel.setToolTipText(tooltip)
  }

  override def focusOnDefaultComponent(): Unit = chatInput.requestFocus()

  /** Update the context bar with current conversation usage. */
  private def updateContextBar(history: List[ChatAction.Message]): Unit = {
    try {
      val modelId = AssistantOptions.getModelId
      val usage = ContextTracker.calculate(history, modelId)
      contextBar.updateUsage(usage)
    } catch {
      case ex: Exception =>
        Output.warning(s"[Assistant] Failed to update context bar: ${ex.getMessage}")
    }
  }
}

/** Custom panel for displaying context usage as a progress bar.
  * 
  * Shows token usage with semantic color coding (green → amber → red).
  * Displays both percentage and fraction (e.g., "68% ~14K/200K").
  * Click to show detailed breakdown in chat.
  */
class ContextBarPanel extends JPanel {
  private var usage: Option[ContextTracker.ContextUsage] = None
  
  setPreferredSize(new java.awt.Dimension(160, 20))
  setMinimumSize(new java.awt.Dimension(140, 20))
  setMaximumSize(new java.awt.Dimension(180, 20))
  setOpaque(false)
  setCursor(java.awt.Cursor.getPredefinedCursor(java.awt.Cursor.HAND_CURSOR))
  
  // Click to show detailed stats in chat
  addMouseListener(new java.awt.event.MouseAdapter {
    override def mouseClicked(e: java.awt.event.MouseEvent): Unit = {
      usage.foreach { u =>
        val details = s"""**Context Usage Details**
          |
          |* Used: ~${ContextTracker.formatThousands(u.usedTokens)} tokens
          |* Model limit: ~${ContextTracker.formatThousands(u.maxTokens)} tokens
          |* Budget limit: ~${ContextTracker.formatThousands(u.budgetTokens)} tokens (internal)
          |* Messages: ${u.messageCount} total${if (u.truncatedCount > 0) s", ${u.truncatedCount} truncated" else ""}
          |* System prompt: ~${ContextTracker.formatThousands(u.systemPromptTokens)} tokens
          |* Percentage: ${(u.percentage * 100).toInt}%
          |
          |**Note:** Token estimates use a ~3.5 chars/token heuristic. Actual usage may vary slightly.
          |Context management will be improved in future updates with auto-compaction.""".stripMargin
        ChatAction.addResponse(details)
      }
    }
  })
  
  override def paintComponent(g: java.awt.Graphics): Unit = {
    super.paintComponent(g)
    val g2 = g.asInstanceOf[java.awt.Graphics2D]
    g2.setRenderingHint(
      java.awt.RenderingHints.KEY_ANTIALIASING,
      java.awt.RenderingHints.VALUE_ANTIALIAS_ON
    )
    
    val w = getWidth
    val h = getHeight
    val radius = 4
    
    // Background track
    g2.setColor(java.awt.Color.decode(UIColors.ContextBar.background))
    g2.fillRoundRect(0, 0, w, h, radius, radius)
    
    // Border
    g2.setColor(java.awt.Color.decode(UIColors.ContextBar.border))
    g2.drawRoundRect(0, 0, w - 1, h - 1, radius, radius)
    
    usage.foreach { u =>
      val pct = u.percentage
      if (pct > 0) {
        // Determine fill color based on percentage
        val fillColor = if (pct < 0.60) {
          UIColors.ContextBar.fillHealthy
        } else if (pct < 0.85) {
          UIColors.ContextBar.fillWarning
        } else {
          UIColors.ContextBar.fillDanger
        }
        
        g2.setColor(java.awt.Color.decode(fillColor))
        val fillWidth = math.min(w - 2, ((w - 2) * pct).toInt)
        g2.fillRoundRect(1, 1, fillWidth, h - 2, radius - 1, radius - 1)
      }
      
      // Text overlay: "68% ~14K/200K"
      val text = s"${u.formatPercentage} ~${ContextTracker.formatThousands(u.usedTokens)}/${ContextTracker.formatThousands(u.maxTokens)}"
      g2.setColor(java.awt.Color.decode(UIColors.ContextBar.text))
      g2.setFont(g2.getFont.deriveFont(9f))
      val fm = g2.getFontMetrics
      val textWidth = fm.stringWidth(text)
      val textHeight = fm.getHeight
      val x = (w - textWidth) / 2
      val y = (h + textHeight) / 2 - fm.getDescent
      g2.drawString(text, x, y)
    }
  }
  
  /** Update the context bar with new usage data */
  def updateUsage(newUsage: ContextTracker.ContextUsage): Unit = {
    usage = Some(newUsage)
    setToolTipText(newUsage.formatTooltip)
    repaint()
  }
  
  /** Reset the context bar to empty state */
  def reset(): Unit = {
    usage = None
    setToolTipText(null)
    repaint()
  }
}

/** HTMLEditorKit that resolves synthetic image URLs (latex://, mermaid://)
  * from MarkdownRenderer's
  * cache.
  */
class SyntheticImageAwareEditorKit extends javax.swing.text.html.HTMLEditorKit {
  override def getViewFactory: javax.swing.text.ViewFactory =
    new SyntheticImageViewFactory(super.getViewFactory)
}

class SyntheticImageViewFactory(delegate: javax.swing.text.ViewFactory)
    extends javax.swing.text.ViewFactory {
  def create(elem: javax.swing.text.Element): javax.swing.text.View = {
    val kind = elem.getName
    if (kind != null && kind.equalsIgnoreCase("img")) {
      val src = elem.getAttributes.getAttribute(
        javax.swing.text.html.HTML.Attribute.SRC
      )
      if (src != null && MarkdownRenderer.isSyntheticImageUrl(src.toString)) {
        new SyntheticImageView(elem)
      } else delegate.create(elem)
    } else delegate.create(elem)
  }
}

class SyntheticImageView(elem: javax.swing.text.Element)
    extends javax.swing.text.View(elem) {
  private val src = elem.getAttributes
    .getAttribute(javax.swing.text.html.HTML.Attribute.SRC)
    .toString

  private def currentImage: java.awt.Image =
    MarkdownRenderer.getCachedImage(src).orNull

  override def getPreferredSpan(axis: Int): Float = {
    val img = currentImage
    if (img == null) 0f
    else if (axis == javax.swing.text.View.X_AXIS) img.getWidth(null).toFloat
    else img.getHeight(null).toFloat
  }

  override def getMinimumSpan(axis: Int): Float = getPreferredSpan(axis)
  override def getMaximumSpan(axis: Int): Float = getPreferredSpan(axis)

  override def paint(g: java.awt.Graphics, allocation: java.awt.Shape): Unit = {
    val img = currentImage
    if (img != null) {
      val rect = allocation.getBounds
      val _ = g.drawImage(img, rect.x, rect.y, null)
    }
  }

  override def modelToView(
      pos: Int,
      a: java.awt.Shape,
      bias: javax.swing.text.Position.Bias
  ): java.awt.Shape = {
    val rect = a.getBounds
    if (pos <= getStartOffset)
      new java.awt.Rectangle(rect.x, rect.y, 0, rect.height)
    else new java.awt.Rectangle(rect.x + rect.width, rect.y, 0, rect.height)
  }

  override def viewToModel(
      x: Float,
      y: Float,
      a: java.awt.Shape,
      biasReturn: Array[javax.swing.text.Position.Bias]
  ): Int = {
    val rect = a.getBounds
    biasReturn(0) = javax.swing.text.Position.Bias.Forward
    if (x < rect.x + rect.width / 2) getStartOffset else getEndOffset
  }
}
