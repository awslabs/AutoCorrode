/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.awt._
import javax.swing._

/** Verification status badges (Verified, Failed, Unverified, etc.) with colored Swing panels.
 *  Each badge type represents a verification outcome and maps to a display color and label. */
object VerificationBadge {
  /** Verification outcome for display in the dockable badge area and chat messages. */
  enum BadgeType {
    case Verified(timeMs: Option[Long] = None)
    case Failed(reason: String = "")
    case Unverified
    case Verifying
    case Sledgehammer(timeMs: Option[Long] = None)
    case EisbachMissing
  }
  export BadgeType._

  def toStatus(badge: BadgeType): String = badge match {
    case Verified(_) => AssistantConstants.STATUS_READY
    case Failed(_) => AssistantConstants.STATUS_READY
    case Unverified => AssistantConstants.STATUS_READY
    case Verifying => AssistantConstants.STATUS_VERIFYING
    case Sledgehammer(_) => AssistantConstants.STATUS_READY
    case EisbachMissing => AssistantConstants.STATUS_READY
  }

  /** Word-aware truncation for failure reasons: cut on whitespace before `max`
    * and append an ellipsis, so the badge never shows half a word. */
  private def truncateReason(reason: String, max: Int): String = {
    if (reason.length <= max) reason
    else {
      val cut = reason.take(max)
      val lastSpace = cut.lastIndexWhere(_.isWhitespace)
      val base =
        if (lastSpace > max / 2) cut.substring(0, lastSpace).trim
        else cut.trim
      base + "…"
    }
  }

  private def badgeInfo(badge: BadgeType): (String, String, String, String) = badge match {
    case Verified(t) => (UIColors.Badge.successBackground, UIColors.Badge.successText, UIColors.Badge.successBorder, "Verified" + t.map(ms => s" (${ms}ms)").getOrElse(""))
    case Failed(r) => (UIColors.Badge.errorBackground, UIColors.Badge.errorText, UIColors.Badge.errorBorder, "Failed" + (if (r.nonEmpty) s": ${truncateReason(r, 40)}" else ""))
    case Unverified => (UIColors.Badge.warningBackground, UIColors.Badge.warningText, UIColors.Badge.warningBorder, "Unverified")
    case Verifying => (UIColors.Badge.neutralBackground, UIColors.Badge.neutralText, UIColors.Badge.neutralBorder, "Verifying…")
    case Sledgehammer(t) => (UIColors.Badge.infoBackground, UIColors.Badge.infoText, UIColors.Badge.infoBorder, "Sledgehammer" + t.map(ms => s" (${ms}ms)").getOrElse(""))
    case EisbachMissing => (UIColors.Badge.accentBackground, UIColors.Badge.accentText, UIColors.Badge.accentBorder, "Eisbach not imported")
  }

  def createBadgePanel(badge: BadgeType): JPanel = {
    val widget = new BadgeWidget()
    widget.updateBadge(badge)
    widget
  }

  /** Reusable badge panel. A single instance can be mounted once and then
    * updated in place by calling [[updateBadge]], avoiding the cost of
    * rebuilding the component hierarchy on every verification event. */
  final class BadgeWidget extends JPanel(new FlowLayout(FlowLayout.LEFT, 10, 6)) {

    private var bgColor = Color.decode(UIColors.Badge.neutralBackground)
    private var borderColor = Color.decode(UIColors.Badge.neutralBorder)

    private val roundedPanel: JPanel = new JPanel() {
      override def paintComponent(g: java.awt.Graphics): Unit = {
        val g2 = g.asInstanceOf[java.awt.Graphics2D]
        g2.setRenderingHint(
          java.awt.RenderingHints.KEY_ANTIALIASING,
          java.awt.RenderingHints.VALUE_ANTIALIAS_ON
        )
        g2.setColor(bgColor)
        g2.fillRoundRect(0, 0, getWidth - 1, getHeight - 1, 4, 4)
        g2.setColor(borderColor)
        g2.drawRoundRect(0, 0, getWidth - 1, getHeight - 1, 4, 4)
      }
    }

    private val label = new JLabel()

    roundedPanel.setLayout(new FlowLayout(FlowLayout.CENTER, 0, 0))
    roundedPanel.setOpaque(false)

    label.setFont(UIManager.getFont("Label.font").deriveFont(Font.PLAIN, UIDesign.fp(11f)))
    label.setBorder(BorderFactory.createEmptyBorder(UIDesign.sp(4), UIDesign.sp(10), UIDesign.sp(4), UIDesign.sp(10)))
    label.setOpaque(false)

    roundedPanel.add(label)
    add(roundedPanel)

    def updateBadge(badge: BadgeType): Unit = {
      val (bg, text, border, labelText) = badgeInfo(badge)
      bgColor = Color.decode(bg)
      borderColor = Color.decode(border)
      label.setForeground(Color.decode(text))
      label.setText(labelText)
      roundedPanel.revalidate()
      roundedPanel.repaint()
    }
  }
}
