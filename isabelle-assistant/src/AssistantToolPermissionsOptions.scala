/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.AbstractOptionPane
import javax.swing.{JComboBox, JButton}

/** Dedicated options pane for configuring assistant tool permissions. */
class AssistantToolPermissionsOptions
    extends AbstractOptionPane("assistant-tool-permissions-options") {

  private var permissionCombos: scala.collection.mutable.Map[String, JComboBox[String]] = _

  override def _init(): Unit = {
    addSeparator("Tool Permissions")

    permissionCombos = scala.collection.mutable.Map[String, JComboBox[String]]()

    for (tool <- AssistantTools.tools.sortBy(_.name)) {
      val combo = new JComboBox(ToolPermissions.PermissionLevel.displayOptions)
      val configured =
        ToolPermissions.getConfiguredLevel(tool.name).toDisplayString
      combo.setSelectedItem(configured)

      val displayName = tool.name.split("_").map(_.capitalize).mkString(" ")
      val description =
        ToolPermissions.toolDescriptions.getOrElse(tool.name, tool.description)
      val tooltipBase = if (tool.name == "ask_user") {
        "This tool allows the assistant to ask you questions. Must always be allowed (locked)."
      } else {
        s"Allows the assistant to $description"
      }
      val tooltip = s"$tooltipBase\nTool ID: ${tool.name}"

      combo.setEnabled(tool.name != "ask_user")
      combo.setToolTipText(tooltip)
      permissionCombos(tool.name) = combo
      addComponent(displayName + ":", combo)
    }

    val resetButton = new JButton("Reset to Defaults")
    resetButton.addActionListener(_ => {
      ToolPermissions.resetToDefaults()
      for ((toolName, combo) <- permissionCombos) {
        val level = ToolPermissions.getConfiguredLevel(toolName).toDisplayString
        combo.setSelectedItem(level)
      }
    })
    addComponent("", resetButton)
  }

  override def _save(): Unit = {
    if (permissionCombos != null) {
      for ((toolName, combo) <- permissionCombos) {
        val displayLabel =
          Option(combo.getSelectedItem).map(_.toString).getOrElse("Ask at First Use")
        ToolPermissions.PermissionLevel.fromDisplayString(displayLabel).foreach {
          permLevel => ToolPermissions.setConfiguredLevel(toolName, permLevel)
        }
      }
    }
  }
}
