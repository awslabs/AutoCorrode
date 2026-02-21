/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import org.gjt.sp.jedit.{AbstractOptionPane, jEdit}
import javax.swing.{JCheckBox, JLabel, JScrollPane, JTextArea, JTextField}

/** jEdit options pane for I/Q UI settings. */
class IQOptions extends AbstractOptionPane("iq-options") {
  private var maxLogLinesField: JTextField = _
  private var maxExploreMessagesField: JTextField = _
  private var autoScrollLogsCheckbox: JCheckBox = _
  private var autoFillDefaultsCheckbox: JCheckBox = _
  private var exploreDebugLoggingCheckbox: JCheckBox = _
  private var allowedMutationRootsArea: JTextArea = _
  private var allowedReadRootsArea: JTextArea = _
  private var initialAllowedMutationRoots: String = ""
  private var initialAllowedReadRoots: String = ""

  override def _init(): Unit = {
    val settings = IQUISettings.current

    addSeparator("Dockables")
    maxLogLinesField = new JTextField(settings.maxLogLines.toString, 10)
    maxLogLinesField.setToolTipText(
      "Maximum number of lines kept in I/Q Server Log and I/Q PIDE Markup views."
    )
    addComponent("Max Log Lines:", maxLogLinesField)

    maxExploreMessagesField =
      new JTextField(settings.maxExploreMessages.toString, 10)
    maxExploreMessagesField.setToolTipText(
      "Maximum number of output message elements kept in I/Q Explore."
    )
    addComponent("Max Explore Messages:", maxExploreMessagesField)

    autoScrollLogsCheckbox = new JCheckBox(
      "Auto-scroll log/output panes",
      settings.autoScrollLogs
    )
    addComponent("", autoScrollLogsCheckbox)

    addSeparator("Explore")
    autoFillDefaultsCheckbox = new JCheckBox(
      "Auto-fill default arguments when query changes",
      settings.autoFillDefaults
    )
    autoFillDefaultsCheckbox.setToolTipText(
      "Only fills when the arguments field is empty or still at a previous default."
    )
    addComponent("", autoFillDefaultsCheckbox)

    exploreDebugLoggingCheckbox = new JCheckBox(
      "Enable verbose explore debug logging",
      settings.exploreDebugLogging
    )
    exploreDebugLoggingCheckbox.setToolTipText(
      "Writes detailed explore callback diagnostics to the Isabelle output."
    )
    addComponent("", exploreDebugLoggingCheckbox)

    addSeparator("Security")

    val securityInfo =
      new JLabel(
        "<html>Saving security roots restarts the I/Q MCP server.<br/>No Isabelle/jEdit restart is required.</html>"
      )
    securityInfo.setToolTipText(
      "Applies immediately by restarting only the I/Q MCP server. Existing MCP clients may need to reconnect."
    )
    addComponent("", securityInfo)

    initialAllowedMutationRoots = settings.allowedMutationRoots.trim
    allowedMutationRootsArea = new JTextArea(
      settings.allowedMutationRoots,
      4,
      60
    )
    allowedMutationRootsArea.setToolTipText(
      "Allowed mutation roots for write/create operations. Enter one absolute path per line. Saving applies immediately by restarting only the I/Q MCP server."
    )
    addComponent(
      "Allowed Mutation Roots:",
      new JScrollPane(allowedMutationRootsArea)
    )

    initialAllowedReadRoots = settings.allowedReadRoots.trim
    allowedReadRootsArea = new JTextArea(
      settings.allowedReadRoots,
      4,
      60
    )
    allowedReadRootsArea.setToolTipText(
      "Allowed read roots. Enter one absolute path per line. Leave empty to use mutation roots. Saving applies immediately by restarting only the I/Q MCP server."
    )
    addComponent("Allowed Read Roots:", new JScrollPane(allowedReadRootsArea))
  }

  override def _save(): Unit = {
    jEdit.setProperty(IQUISettings.MaxLogLinesKey, maxLogLinesField.getText)
    jEdit.setProperty(
      IQUISettings.MaxExploreMessagesKey,
      maxExploreMessagesField.getText
    )
    jEdit.setBooleanProperty(
      IQUISettings.AutoScrollLogsKey,
      autoScrollLogsCheckbox.isSelected
    )
    jEdit.setBooleanProperty(
      IQUISettings.AutoFillDefaultsKey,
      autoFillDefaultsCheckbox.isSelected
    )
    jEdit.setBooleanProperty(
      IQUISettings.ExploreDebugLoggingKey,
      exploreDebugLoggingCheckbox.isSelected
    )

    val newAllowedMutationRoots = allowedMutationRootsArea.getText.trim
    val newAllowedReadRoots = allowedReadRootsArea.getText.trim
    jEdit.setProperty(
      IQUISettings.AllowedMutationRootsKey,
      newAllowedMutationRoots
    )
    jEdit.setProperty(IQUISettings.AllowedReadRootsKey, newAllowedReadRoots)

    if (
      newAllowedMutationRoots != initialAllowedMutationRoots ||
      newAllowedReadRoots != initialAllowedReadRoots
    ) {
      IQPlugin.restartServerFromSettings()
    }
  }
}
