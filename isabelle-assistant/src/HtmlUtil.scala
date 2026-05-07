/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** HTML escaping utility for the Assistant plugin.
  *
  * Provides canonical HTML entity escaping used throughout all HTML generation
  * in chat messages, widgets, and code blocks. This ensures XSS-safe output when
  * displaying user-provided or LLM-generated content.
  */
object HtmlUtil {

  /** Escape HTML special characters for safe embedding in HTML documents.
    *
    * Converts & → &amp;, < → &lt;, > → &gt;, " → &quot;, ' → &#39; to prevent 
    * HTML injection and ensure special characters display correctly both in text 
    * content and attribute values.
    *
    * @param s The string to escape (may contain any characters)
    * @return HTML-safe string with special characters converted to entities
    */
  def escapeHtml(s: String): String =
    s.replace("&", "&amp;")
      .replace("<", "&lt;")
      .replace(">", "&gt;")
      .replace("\"", "&quot;")
      .replace("'", "&#39;")

  /** Render a decorative glyph (✓, ✗, ●, etc.) paired with a textual label
    * for screen readers. The glyph span is marked `aria-hidden="true"` so
    * a reader announces "Done" rather than "heavy check mark"; the label
    * span is visually hidden via a `clip-rect` trick so it doesn't affect
    * layout in the JEditorPane. Both spans receive the supplied `colorHex`
    * for the visible glyph; the label is layout-hidden and invisible.
    *
    * Use this helper anywhere a `✓`-style glyph carries meaning — task
    * lists, status lines, verification badges. Bare decorative glyphs in
    * HTML output are an accessibility smell and should be migrated to
    * `accessibleGlyph` over time.
    *
    * @param glyph   The visible glyph character(s) (e.g., "✓", "●", "✗")
    * @param label   The textual equivalent for screen readers (e.g., "Done")
    * @param colorHex Hex color for the glyph (no trailing styles)
    * @return Two adjacent `<span>`s: a visible, aria-hidden glyph followed
    *         by a layout-hidden textual label.
    */
  def accessibleGlyph(glyph: String, label: String, colorHex: String): String = {
    val escapedLabel = escapeHtml(label)
    val escapedGlyph = escapeHtml(glyph)
    s"<span aria-hidden='true' style='color:$colorHex;font-weight:bold;'>$escapedGlyph</span>" +
      s"<span style='position:absolute;width:1px;height:1px;overflow:hidden;clip:rect(0 0 0 0);'>$escapedLabel</span>"
  }

  /** Regexes used by [[sanitizeWidgetHtml]]. Each matches the dangerous
    * construct in a case-insensitive, whitespace-tolerant way; they are
    * compiled once at class-load time. Order matters: strip full elements
    * (with their payload) before neutralising attribute-level vectors. */
  private val scriptElementRe =
    java.util.regex.Pattern.compile(
      "(?is)<script\\b[^>]*>.*?</script\\s*>"
    )
  private val iframeElementRe =
    java.util.regex.Pattern.compile(
      "(?is)<iframe\\b[^>]*>.*?</iframe\\s*>"
    )
  // Open-only variants catch unterminated tags — these still register a
  // partial parse in the HTMLEditorKit and are worth stripping.
  private val openScriptRe =
    java.util.regex.Pattern.compile("(?is)<script\\b[^>]*>")
  private val openIframeRe =
    java.util.regex.Pattern.compile("(?is)<iframe\\b[^>]*>")
  private val javascriptSchemeRe =
    java.util.regex.Pattern.compile("(?i)javascript\\s*:")
  private val eventHandlerAttrRe =
    java.util.regex.Pattern.compile("(?i)\\son[a-z]+\\s*=")

  /** Defense-in-depth sanitiser for Widget-role messages that carry
    * `rawHtml = true` and bypass the top-level escape path. Widget
    * producers already escape user/LLM text before interpolation, but
    * this helper exists so a future producer that forgets does not open
    * an injection surface against `JEditorPane`'s HTMLEditorKit.
    *
    * The sanitiser strips `<script>`/`<iframe>` elements (and their
    * unterminated opens), neutralises `javascript:` URL schemes, and
    * removes inline `on…=` event-handler attributes. Legitimate
    * `action:insert:` / `action:copy:` links are preserved because they
    * don't match any of the patterns above. */
  def sanitizeWidgetHtml(html: String): String = {
    if (html == null || html.isEmpty) ""
    else {
      var out = scriptElementRe.matcher(html).replaceAll("")
      out = iframeElementRe.matcher(out).replaceAll("")
      out = openScriptRe.matcher(out).replaceAll("")
      out = openIframeRe.matcher(out).replaceAll("")
      out = javascriptSchemeRe.matcher(out).replaceAll("blocked:")
      out = eventHandlerAttrRe.matcher(out).replaceAll(" data-blocked=")
      out
    }
  }
}
