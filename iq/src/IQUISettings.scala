/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

import org.gjt.sp.jedit.jEdit

/**
 * Shared UI settings for I/Q dockables and options pane.
 *
 * Values are read from jEdit properties and clamped to safe ranges.
 */
object IQUISettings {
  final val MaxLogLinesKey = "iq.ui.max_log_lines"
  final val MaxExploreMessagesKey = "iq.ui.max_explore_messages"
  final val AutoScrollLogsKey = "iq.ui.auto_scroll_logs"
  final val AutoFillDefaultsKey = "iq.ui.autofill_defaults"
  final val ExploreDebugLoggingKey = "iq.ui.explore_debug_logging"

  final val DefaultMaxLogLines = 4000
  final val DefaultMaxExploreMessages = 1000
  final val DefaultAutoScrollLogs = true
  final val DefaultAutoFillDefaults = true
  final val DefaultExploreDebugLogging = false

  private final val MinLogLines = 200
  private final val MaxLogLines = 100000
  private final val MinExploreMessages = 100
  private final val MaxExploreMessages = 10000

  case class Settings(
      maxLogLines: Int,
      maxExploreMessages: Int,
      autoScrollLogs: Boolean,
      autoFillDefaults: Boolean,
      exploreDebugLogging: Boolean
  )

  private def clampInt(value: String, default: Int, min: Int, max: Int): Int =
    try {
      math.max(min, math.min(max, value.trim.toInt))
    } catch {
      case _: NumberFormatException => default
    }

  private def parse(
      prop: (String, String) => String,
      boolProp: (String, Boolean) => Boolean
  ): Settings =
    Settings(
      maxLogLines = clampInt(
        prop(MaxLogLinesKey, DefaultMaxLogLines.toString),
        DefaultMaxLogLines,
        MinLogLines,
        MaxLogLines
      ),
      maxExploreMessages = clampInt(
        prop(MaxExploreMessagesKey, DefaultMaxExploreMessages.toString),
        DefaultMaxExploreMessages,
        MinExploreMessages,
        MaxExploreMessages
      ),
      autoScrollLogs = boolProp(AutoScrollLogsKey, DefaultAutoScrollLogs),
      autoFillDefaults = boolProp(AutoFillDefaultsKey, DefaultAutoFillDefaults),
      exploreDebugLogging =
        boolProp(ExploreDebugLoggingKey, DefaultExploreDebugLogging)
    )

  def current: Settings =
    parse(
      (key, default) => jEdit.getProperty(key, default),
      (key, default) => jEdit.getBooleanProperty(key, default)
    )

  def parseForTest(
      prop: (String, String) => String,
      boolProp: (String, Boolean) => Boolean
  ): Settings = parse(prop, boolProp)
}
