/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.AbstractOptionPane
import javax.swing.{BoxLayout, JButton, JComboBox, JLabel, JPanel, JTextField, JTextArea, JScrollPane}
import javax.swing.event.{DocumentEvent, DocumentListener}
import java.awt.{Dimension, FlowLayout, GridBagConstraints, GridBagLayout, Insets}

/** Dedicated options pane for configuring assistant tool permissions.
  *
  * Provides a live filter over the tool list (by tool name or description)
  * and a read-only audit summary of the tools currently session-allowed or
  * session-denied. Sorted alphabetically within the pane; users who know a
  * tool by name can jump to it with the search box rather than scrolling the
  * ~50-item registry.
  */
class AssistantToolPermissionsOptions
    extends AbstractOptionPane("assistant-tool-permissions-options") {

  private case class ToolRow(
      toolName: String,
      displayName: String,
      descriptionLower: String,
      combo: JComboBox[String],
      labelComp: JLabel,
      panelComp: JPanel
  )

  private val toolRows = scala.collection.mutable.Buffer.empty[ToolRow]
  private val rowsContainer = new JPanel()
  rowsContainer.setLayout(new BoxLayout(rowsContainer, BoxLayout.Y_AXIS))

  override def _init(): Unit = {
    addSeparator("Tool Permissions")

    toolRows.clear()
    rowsContainer.removeAll()

    val filterField = new JTextField(20)
    filterField.setToolTipText("Filter tools by name or description")
    val filterLabel = new JLabel("Search:")
    val filterPanel = new JPanel(new FlowLayout(FlowLayout.LEFT, 4, 0))
    filterPanel.add(filterLabel)
    filterPanel.add(filterField)
    addComponent("", filterPanel)

    for (tool <- AssistantTools.tools.sortBy(_.name)) {
      val combo = new JComboBox(ToolPermissions.PermissionLevel.displayOptions)
      val configured =
        ToolPermissions.getConfiguredLevel(tool.name).toDisplayString
      combo.setSelectedItem(configured)

      val displayName = tool.name.split("_").map(_.capitalize).mkString(" ")
      val description = ToolPermissions.getToolDescription(tool.id)
      val tooltipBase = if (tool.name == "ask_user") {
        "This tool allows the assistant to ask you questions. Must always be allowed (locked)."
      } else {
        s"Allows the assistant to $description"
      }
      val tooltip = s"$tooltipBase\nTool ID: ${tool.name}"

      combo.setEnabled(tool.name != "ask_user")
      combo.setToolTipText(tooltip)

      val label = new JLabel(displayName + ":")
      val rowPanel = new JPanel(new GridBagLayout())
      val gc = new GridBagConstraints()
      gc.anchor = GridBagConstraints.WEST
      gc.insets = new Insets(2, 0, 2, 8)
      gc.gridx = 0; gc.weightx = 0
      rowPanel.add(label, gc)
      gc.gridx = 1; gc.weightx = 1; gc.fill = GridBagConstraints.HORIZONTAL
      rowPanel.add(combo, gc)
      rowsContainer.add(rowPanel)

      toolRows += ToolRow(
        tool.name,
        displayName,
        description.toLowerCase,
        combo,
        label,
        rowPanel
      )
    }

    filterField.getDocument.addDocumentListener(new DocumentListener {
      private def refresh(): Unit = applyFilter(filterField.getText)
      override def insertUpdate(e: DocumentEvent): Unit = refresh()
      override def removeUpdate(e: DocumentEvent): Unit = refresh()
      override def changedUpdate(e: DocumentEvent): Unit = refresh()
    })

    val scroll = new JScrollPane(rowsContainer)
    scroll.setPreferredSize(new Dimension(520, 320))
    scroll.setBorder(javax.swing.BorderFactory.createEmptyBorder())
    addComponent("", scroll)

    val resetButton = new JButton("Reset to Defaults")
    resetButton.addActionListener(_ => {
      for (tool <- AssistantTools.tools) {
        toolRows.find(_.toolName == tool.name).foreach { row =>
          val defaultLevel = ToolPermissions.getDefaultLevel(tool.id)
          row.combo.setSelectedItem(defaultLevel.toDisplayString)
        }
      }
    })
    addComponent("", resetButton)

    // Session-state audit: lists tools granted/denied for the current
    // session so a user can see what has been approved without digging
    // through the permission prompts.
    addSeparator("Session Audit")
    val audit = buildSessionAudit()
    val auditArea = new JTextArea(audit)
    auditArea.setEditable(false)
    auditArea.setLineWrap(true)
    auditArea.setWrapStyleWord(true)
    auditArea.setBackground(rowsContainer.getBackground)
    val auditScroll = new JScrollPane(auditArea)
    auditScroll.setPreferredSize(new Dimension(520, 100))
    addComponent("", auditScroll)
  }

  private def applyFilter(raw: String): Unit = {
    val q = raw.trim.toLowerCase
    for (row <- toolRows) {
      val matches =
        q.isEmpty ||
          row.toolName.toLowerCase.contains(q) ||
          row.displayName.toLowerCase.contains(q) ||
          row.descriptionLower.contains(q)
      row.panelComp.setVisible(matches)
    }
    rowsContainer.revalidate()
    rowsContainer.repaint()
  }

  private def buildSessionAudit(): String = {
    val allowed = ToolPermissions.sessionAllowedToolNames
    val denied = ToolPermissions.sessionDeniedToolNames
    val allowedText =
      if (allowed.isEmpty) "Session allows: (none)"
      else s"Session allows (${allowed.size}): ${allowed.mkString(", ")}"
    val deniedText =
      if (denied.isEmpty) "Session denies: (none)"
      else s"Session denies (${denied.size}): ${denied.mkString(", ")}"
    allowedText + "\n\n" + deniedText
  }

  override def _save(): Unit = {
    for (tool <- AssistantTools.tools) {
      toolRows.find(_.toolName == tool.name).foreach { row =>
        val displayLabel =
          Option(row.combo.getSelectedItem).map(_.toString).getOrElse("Ask at First Use")
        ToolPermissions.PermissionLevel.fromDisplayString(displayLabel).foreach {
          permLevel => ToolPermissions.setConfiguredLevel(tool.name, permLevel)
        }
      }
    }
  }
}
