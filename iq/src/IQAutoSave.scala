/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import org.gjt.sp.jedit.jEdit
import scala.jdk.CollectionConverters._

/**
 * Shared auto-save state for I/Q edits.
 *
 * When enabled, `write_file` edits are persisted to disk immediately after the
 * jEdit buffer is modified, so the buffer contents and the file-system state
 * never diverge. (Divergence is a frequent source of confusion for agents that
 * mix I/Q edits with direct file-system edits.)
 *
 * This object is the single source of truth for the setting. Both the MCP
 * `set_auto_save` tool and the I/Q dockable checkbox read and mutate it, and a
 * listener mechanism keeps the checkbox and the internal state in sync no
 * matter which side toggles it. The value is persisted across sessions as a
 * jEdit property.
 */
object IQAutoSave {
  final val EnabledKey = "iq.autosave.enabled"
  final val DefaultEnabled = true

  private val listeners =
    new java.util.concurrent.CopyOnWriteArrayList[Boolean => Unit]()

  @volatile private var enabledState: Boolean =
    jEdit.getBooleanProperty(EnabledKey, DefaultEnabled)

  /** Whether auto-save is currently enabled. */
  def enabled: Boolean = enabledState

  /**
   * Update the auto-save state. No-op if unchanged. Persists to jEdit
   * properties and notifies all listeners (e.g. the dockable checkbox) so the
   * UI and the internal state never drift apart.
   */
  def setEnabled(value: Boolean): Unit = {
    if (value == enabledState) return
    enabledState = value
    jEdit.setBooleanProperty(EnabledKey, value)
    listeners.asScala.foreach(listener => listener(value))
  }

  /**
   * Register a listener invoked whenever the state changes. The listener is
   * NOT called on registration; callers should initialise their view from
   * `enabled` first, then keep it in sync via the listener.
   */
  def addListener(listener: Boolean => Unit): Unit = {
    val _ = listeners.add(listener)
  }

  def removeListener(listener: Boolean => Unit): Unit = {
    val _ = listeners.remove(listener)
  }
}
