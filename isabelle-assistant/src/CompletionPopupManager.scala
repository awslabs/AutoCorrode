/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.awt.Color
import javax.swing.{
  BorderFactory,
  JList,
  JPanel,
  JScrollPane,
  JTextArea,
  JWindow,
  ListSelectionModel,
  SwingUtilities
}

/** Owns the non-focus-stealing command-completion popup attached to the
  * Assistant chat input. All methods are EDT-affine; `updateCompletions` may
  * be called from any thread and schedules the repopulation on the EDT.
  *
  * The popup is lazily created on first show. Keeping it bound to a manager
  * (rather than scattered across AssistantDockable) lets the input handlers
  * treat "is a completion visible?" / "advance selection" as opaque calls,
  * and keeps the window lifecycle in one place.
  */
private[assistant] class CompletionPopupManager(
    chatInput: JTextArea,
    inputPanel: JPanel,
    ownerProvider: () => java.awt.Window
) {
  private var window: Option[JWindow] = None
  private var list: Option[JList[String]] = None

  /** Build the popup window and list. Called lazily before first show. */
  private def ensureInitialized(): Unit = {
    if (window.isEmpty) {
      val w = new JWindow(ownerProvider())
      w.setFocusableWindowState(false) // critical: prevents focus stealing
      w.setAlwaysOnTop(true)

      val l = new JList[String]()
      l.setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
      l.setVisibleRowCount(8)
      l.setFont(chatInput.getFont)

      val scrollPane = new JScrollPane(l)
      scrollPane.setBorder(BorderFactory.createLineBorder(Color.GRAY, 1))
      w.add(scrollPane)

      window = Some(w)
      list = Some(l)
    }
  }

  /** Update completion popup based on current chat input text. Schedules the
    * repopulation on the EDT, so this may be called from document listeners. */
  def updateCompletions(): Unit = {
    SwingUtilities.invokeLater { () =>
      val text = chatInput.getText
      // Only show completions for command prefixes (starts with : and no space yet).
      if (text.startsWith(":") && text.length >= 2 && !text.contains(" ")) {
        val prefix = text.drop(1).toLowerCase
        val commands = ChatAction.commandNames
          .filter(_.startsWith(prefix))
          .sorted
          .take(8)
        if (commands.nonEmpty) show(commands.map(":" + _).toArray)
        else hide()
      } else hide()
    }
  }

  private def show(completions: Array[String]): Unit = {
    ensureInitialized()
    val locationOpt =
      try Some((inputPanel.getLocationOnScreen, inputPanel.getHeight))
      catch { case _: java.awt.IllegalComponentStateException => None }

    locationOpt.foreach { case (inputLocation, inputHeight) =>
      for {
        w <- window
        l <- list
      } {
        l.setListData(completions)
        l.setSelectedIndex(0)

        w.setLocation(inputLocation.x, inputLocation.y + inputHeight)

        w.pack()
        val preferredWidth = Math.max(200, inputPanel.getWidth / 2)
        w.setSize(preferredWidth, w.getHeight)

        if (!w.isVisible) w.setVisible(true)
      }
    }
  }

  def hide(): Unit = window.foreach(_.setVisible(false))

  def isVisible: Boolean = window.exists(_.isVisible)

  def navigateUp(): Unit = list.foreach { l =>
    val currentIndex = l.getSelectedIndex
    if (currentIndex > 0) {
      l.setSelectedIndex(currentIndex - 1)
      l.ensureIndexIsVisible(currentIndex - 1)
    }
  }

  def navigateDown(): Unit = list.foreach { l =>
    val currentIndex = l.getSelectedIndex
    if (currentIndex < l.getModel.getSize - 1) {
      l.setSelectedIndex(currentIndex + 1)
      l.ensureIndexIsVisible(currentIndex + 1)
    }
  }

  /** Insert the highlighted completion into the chat input and hide the popup.
    * No-op when nothing is selected. */
  def acceptSelected(): Unit = list.foreach { l =>
    val selected = l.getSelectedValue
    if (selected != null) {
      chatInput.setText(selected + " ")
      chatInput.setCaretPosition(chatInput.getText.length)
      hide()
    }
  }
}
