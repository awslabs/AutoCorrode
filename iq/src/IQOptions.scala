/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import org.gjt.sp.jedit.{AbstractOptionPane, jEdit}
import javax.swing.{JCheckBox, JTextField}

/** jEdit options pane for I/Q UI settings. */
class IQOptions extends AbstractOptionPane("iq-options") {
  private var maxLogLinesField: JTextField = _
  private var maxExploreMessagesField: JTextField = _
  private var autoScrollLogsCheckbox: JCheckBox = _
  private var autoFillDefaultsCheckbox: JCheckBox = _
  private var exploreDebugLoggingCheckbox: JCheckBox = _

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
  }
}
