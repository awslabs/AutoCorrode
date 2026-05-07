/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Design tokens and shared UI primitives for the Assistant's HTML/Swing chrome.
  *
  *  A single source of truth for: type scale, spacing scale, corner radius,
  *  card elevation, and DPI scaling. HTML-builder code (ConversationRenderer,
  *  MarkdownRenderer, WidgetRenderer, VerificationBadge, ChatAction help) should
  *  compose string styles from these tokens rather than hand-picking literals,
  *  so elevation / radius / type ladder stay consistent across the surface.
  *
  *  Invariants this module defends:
  *    - One `box-shadow` declaration across the whole UI (`cardShadow`).
  *    - Two corner radii only (`Radius.sm`, `Radius.md`).
  *    - Six type-scale steps only; no hand-picked pt sizes in other files.
  *    - 4-px spacing grid (xs=2 is the one sub-grid exception for tight insets).
  */
object UIDesign {

  /** Type scale for HTML strings. Six steps, ~1.2× ratio. Use these instead
    * of hand-picked point sizes — they're tuned to read evenly with JEditorPane's
    * default font metrics. */
  object FontSize {
    val xs: String = "9pt"
    val sm: String = "10pt"
    val base: String = "11pt"
    val md: String = "12pt"
    val lg: String = "13pt"
    val xl: String = "15pt"
    /** Display size for headline LaTeX / top-level headings. Not for body text. */
    val display: String = "18pt"
  }

  /** Spacing scale (4-px grid). Use in HTML `padding` / `margin`. */
  object Space {
    val xs: String = "2px"
    val sm: String = "4px"
    val md: String = "8px"
    val lg: String = "12px"
    val xl: String = "16px"
  }

  /** Corner radius — exactly two canonical values. Any `border-radius` outside
    * `{sm, md}` is a bug. */
  object Radius {
    val sm: String = "3px"
    val md: String = "6px"
  }

  /** Single card elevation. Do not redeclare `box-shadow:…` elsewhere — use this. */
  val cardShadow: String = "0 1px 2px rgba(0,0,0,0.08)"

  /** DPI scale relative to the 96-DPI baseline Swing was designed for. Used
    * for *Swing* pixel arithmetic (borders, insets, button sizes). HTML font
    * sizes are left in pt and scale via the L&F.  */
  lazy val scale: Float = {
    try java.awt.Toolkit.getDefaultToolkit.getScreenResolution.toFloat / 96f
    catch { case _: Throwable => 1.0f }
  }

  /** Scale an integer pixel value by the current DPI. */
  def sp(px: Int): Int = (px * scale).round

  /** Scale a floating-point size (e.g., Swing font size) by the current DPI. */
  def fp(pt: Float): Float = pt * scale

  // --- Shared HTML card helpers ------------------------------------------------

  /** The canonical chat-card wrapper. All message bubbles and widget cards
    * funnel through this so elevation, radius, padding, and background are
    * consistent. `background:white` is intentional — `MarkdownRenderer.renderLatex`
    * fills LaTeX image backgrounds with white, so glyphs integrate cleanly only
    * on a white bubble.
    *
    * @param body       rendered inner HTML (already-escaped)
    * @param accent     left-border accent color (hex string)
    * @param extraStyle optional extra CSS (e.g., `position:relative;`)
    */
  def card(body: String, accent: String, extraStyle: String = ""): String =
    s"<div style='margin:${Space.xs} 0;padding:${Space.md} ${Space.md};background:white;" +
    s"border-left:4px solid $accent;border-radius:${Radius.sm};" +
    s"overflow-x:hidden;word-wrap:break-word;box-shadow:$cardShadow;$extraStyle'>" +
    body +
    "</div>"

  /** Info-card variant for welcome / help / info boxes. Softer tint background
    * (not white) because these panels don't host LaTeX and benefit from a
    * discrete surface.
    *
    * @param title       bold header text (plain string, not HTML)
    * @param bodyHtml    rendered body HTML
    * @param accent      accent color (header text + border)
    * @param background  card background tint
    * @param border      card border (thin, full outline)
    */
  def infoCard(
      title: String,
      bodyHtml: String,
      accent: String,
      background: String,
      border: String
  ): String = {
    val titleBlock =
      if (title.isEmpty) ""
      else
        s"<div style='font-weight:bold;font-size:${FontSize.base};color:$accent;margin-bottom:${Space.sm};'>" +
          HtmlUtil.escapeHtml(title) +
          "</div>"
    s"<div style='margin:${Space.md} 0;padding:${Space.md} ${Space.lg};background:$background;" +
      s"border:1px solid $border;border-radius:${Radius.md};'>" +
      titleBlock +
      bodyHtml +
      "</div>"
  }
}
