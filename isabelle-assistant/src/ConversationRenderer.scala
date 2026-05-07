/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Renders HTML for conversation message bubbles in the chat panel.
 * Extracted from AssistantDockable to separate rendering concerns from UI lifecycle.
 *
 * Bubble styling routes through `UIDesign.card` so radius, padding, elevation, and
 * the white background stay consistent with every other chat card. White is
 * intentional — LaTeX images are rendered with a white fill (see
 * `MarkdownRenderer.renderLatex`) and need a white bubble to integrate cleanly.
 */
object ConversationRenderer {

  /** Shared chat bubble wrapper used by user, assistant, and tool message renderers.
    *
    * Creates a styled message bubble with role-specific border color, header with timestamp,
    * body content, and optional copy button. Always uses the canonical card styling.
    *
    * @param border Hex color string for the left border (role indicator)
    * @param headerHtml Pre-rendered HTML for the message header (role name + timestamp)
    * @param bodyHtml Pre-rendered HTML for the message body content
    * @param copyContent Optional raw text content for the copy button
    * @return Complete HTML for the message bubble
    */
  def messageBubbleHtml(
      border: String,
      headerHtml: String,
      bodyHtml: String,
      copyContent: Option[String] = None
  ): String = {
    val (copyLink, extraStyle) = copyContent match {
      case Some(raw) =>
        val encoded = java.net.URLEncoder.encode(raw, "UTF-8")
        val link = copyButton(s"action:copy:$encoded", positioned = true)
        (link, "position:relative;")
      case None => ("", "")
    }
    val body = s"$copyLink$headerHtml<div>$bodyHtml</div>"
    UIDesign.card(body, border, extraStyle)
  }

  /** Small pill-styled copy button. Used by both the message-bubble header-overlay
    * (`positioned=true`) and, in the future, any inline copy actions. */
  private def copyButton(href: String, positioned: Boolean): String = {
    val posStyle =
      if (positioned) s"position:absolute;top:${UIDesign.Space.md};right:${UIDesign.Space.md};"
      else ""
    val bg = UIColors.CodeButton.background
    val text = UIColors.CodeButton.text
    val brdr = UIColors.CodeButton.border
    s"<a href='$href' title='Copy message' style='$posStyle" +
      s"display:inline-block;text-decoration:none;" +
      s"padding:${UIDesign.Space.xs} ${UIDesign.Space.md};" +
      s"background:$bg;color:$text;border:1px solid $brdr;" +
      s"border-radius:${UIDesign.Radius.sm};" +
      s"font-size:${UIDesign.FontSize.xs};font-weight:normal;'>Copy</a>"
  }

  /** Create HTML for a user message bubble.
    *
    * Renders with blue left border, "You" header, and Markdown-processed body.
    * Includes a copy button for the raw message content.
    *
    * @param content The user's message text (will be processed as Markdown)
    * @param timestamp Formatted timestamp string (HH:mm)
    * @return Complete HTML for the user message bubble
    */
  def createUserMessageHtml(
      content: String,
      timestamp: String
  ): String = {
    val tsColor = UIColors.ChatBubble.userTimestamp
    messageBubbleHtml(
      border = UIColors.ChatBubble.userBorder,
      headerHtml =
        s"<div style='font-size:${UIDesign.FontSize.sm};color:$tsColor;margin-bottom:${UIDesign.Space.xs};'><b>You</b> · $timestamp</div>",
      bodyHtml = MarkdownRenderer.toBodyHtml(content),
      copyContent = Some(content)
    )
  }

  /** Create HTML for an assistant message bubble.
    *
    * Renders with purple left border for normal messages; red for errors;
    * green for successes; neutral/info tint for info and summary kinds.
    * Processes Markdown with clickable Isabelle code blocks, handles
    * `{{INSERT:id}}` and `{{ACTION:id:label}}` placeholders, and includes
    * a copy button.
    *
    * The caller is expected to pass `kind` derived from
    * `ChatAction.Message.kind`. As a transitional fallback, legacy `Error:`
    * and `[FAIL]` string prefixes still get the error border so stored
    * messages written before `ResponseKind` existed keep rendering
    * correctly; this fallback can be removed one release after every
    * call site has migrated.
    *
    * @param content The assistant's message text (Markdown or raw HTML)
    * @param timestamp Formatted timestamp string (HH:mm)
    * @param rawHtml If true, content is already HTML and should not be processed
    * @param registerAction Function to register insert actions and return their IDs
    * @param kind Semantic tag for the message (error, success, info, …)
    * @return Complete HTML for the assistant message bubble
    */
  def createAssistantMessageHtml(
      content: String,
      timestamp: String,
      rawHtml: Boolean = false,
      registerAction: String => String,
      kind: ChatAction.ResponseKind = ChatAction.ResponseKind.Normal
  ): String = {
    val legacyErrorPrefix =
      content.startsWith("Error:") || content.startsWith("[FAIL]")
    val effectiveKind =
      if (kind == ChatAction.ResponseKind.Normal && legacyErrorPrefix)
        ChatAction.ResponseKind.Error
      else kind

    val body =
      if (rawHtml) content
      else {
        val rendered =
          MarkdownRenderer.toBodyHtmlWithActions(content, registerAction)
        val withLinks = "\\{\\{INSERT:([a-f0-9]+)\\}\\}".r.replaceAllIn(
          rendered,
          m =>
            java.util.regex.Matcher.quoteReplacement(
              s"<a href='action:insert:${m.group(1)}'>[Insert]</a>"
            )
        )
        "\\{\\{ACTION:([a-f0-9]+):([^}]+)\\}\\}".r.replaceAllIn(
          withLinks,
          m => {
            // group(2) has already passed through MarkdownRenderer, which
            // HTML-escapes angle brackets and ampersands, so we do not escape
            // it a second time here. quoteReplacement prevents any $/\
            // characters in the captured text from being interpreted as
            // Matcher backreferences.
            val label = m.group(2)
            val rendered =
              if (shouldPrependRun(label)) s"Run $label" else label
            java.util.regex.Matcher.quoteReplacement(
              s"<a href='action:insert:${m.group(1)}'>$rendered</a>"
            )
          }
        )
      }
    val tsColor = effectiveKind match {
      case ChatAction.ResponseKind.Error => UIColors.ChatBubble.errorTimestamp
      case _                             => UIColors.ChatBubble.assistantTimestamp
    }
    val border = effectiveKind match {
      case ChatAction.ResponseKind.Error   => UIColors.ChatBubble.errorBorder
      case ChatAction.ResponseKind.Success => UIColors.Badge.successBorder
      case ChatAction.ResponseKind.Info    => UIColors.Badge.infoBorder
      case ChatAction.ResponseKind.Summary => UIColors.Badge.infoBorder
      case _                               => UIColors.ChatBubble.assistantBorder
    }
    messageBubbleHtml(
      border = border,
      headerHtml =
        s"<div style='font-size:${UIDesign.FontSize.sm};color:$tsColor;margin-bottom:${UIDesign.Space.xs};'><b>Assistant</b> · $timestamp</div>",
      bodyHtml = body,
      copyContent = Some(content)
    )
  }

  /** Leading verbs for `{{ACTION:id:label}}` labels that already read as
    * imperative on their own; the renderer leaves them un-prefixed.
    * Labels outside this set still get a `Run ` prefix so "Continue" →
    * "Run Continue" for consistency with the legacy rendering. */
  private val actionLabelVerbPrefixes = Set(
    "Retry", "Run", "Show", "View", "Cancel", "Copy", "Open", "Insert",
    "Generate", "Suggest", "Verify", "Explain", "Extract", "Refactor",
    "Find", "Clear", "Dismiss", "Save", "Edit", "Delete"
  )

  private[assistant] def shouldPrependRun(label: String): Boolean = {
    val firstWord = label.trim.takeWhile(c => !c.isWhitespace)
    !actionLabelVerbPrefixes.contains(firstWord)
  }

  /** Create HTML for a tool-use message.
    *
    * Displays the tool being called with its parameters in a compact format with teal border.
    * Tool names are converted from snake_case to PascalCase for readability.
    *
    * @param toolName The tool's wire name (e.g., "read_theory")
    * @param params Tool arguments as parsed ToolArgs map
    * @param timestamp Formatted timestamp string (HH:mm)
    * @return Complete HTML for the tool message bubble
    */
  def createToolMessageHtml(
      toolName: String,
      params: ResponseParser.ToolArgs,
      timestamp: String
  ): String = {
    val border = UIColors.ToolMessage.border
    val tsColor = UIColors.ToolMessage.timestamp
    val paramColor = UIColors.ToolMessage.timestamp

    // Convert snake_case to PascalCase for display
    val displayName = toolName.split("_").map(_.capitalize).mkString

    // Format parameters for summary line
    val paramSummary =
      if (params.isEmpty) "()"
      else {
        val formatted = params
          .map { case (k, v) =>
            s"$k: ${HtmlUtil.escapeHtml(ResponseParser.toolValueToDisplay(v))}"
          }
          .mkString(", ")
        s"($formatted)"
      }

    val bodyHtml =
      s"<div style='font-family:${MarkdownRenderer.codeFont};font-size:${UIDesign.FontSize.base};'>" +
        s"<b>$displayName</b><span style='color:$paramColor;font-weight:normal;'>$paramSummary</span></div>"
    messageBubbleHtml(
      border = border,
      headerHtml =
        s"<div style='font-size:${UIDesign.FontSize.sm};color:$tsColor;margin-bottom:${UIDesign.Space.xs};'><b>Tool</b> · $timestamp</div>",
      bodyHtml = bodyHtml
    )
  }

  /** Create HTML for the welcome message shown when chat is empty.
    *
    * Displays a friendly introduction with a clickable `:help` link, three
    * example prompts the user can click to run (when a registrar is
    * supplied), and a warning banner if no model is configured. Routes
    * through `UIDesign.infoCard` colours so welcome / help / info surfaces
    * share one visual vocabulary.
    *
    * @param registerHelpAction Function to register the `:help` command action and return its ID
    * @param registerExampleAction Optional registrar for each example prompt.
    *   When `None`, the examples row is omitted. When supplied, it is called
    *   once per example with the command text, and must return the action id.
    * @return Complete HTML for the welcome message
    */
  def createWelcomeHtml(
      registerHelpAction: () => String,
      registerExampleAction: Option[String => String] = None
  ): String = {
    val helpId = registerHelpAction()
    val wBg = UIColors.Welcome.background
    val wBorder = UIColors.Welcome.border
    val wTitle = UIColors.Welcome.title
    val wText = UIColors.Welcome.text
    val wMuted = UIColors.Welcome.muted
    val codeBg = UIColors.Welcome.codeBackground
    val linkColor = UIColors.Welcome.linkColor

    val modelWarning = if (AssistantOptions.getModelId.isEmpty) {
      val eBg = UIColors.ErrorBox.background
      val eBorder = UIColors.ErrorBox.border
      val eText = UIColors.ErrorBox.text
      s"<div style='margin-top:${UIDesign.Space.md};padding:${UIDesign.Space.md} ${UIDesign.Space.md};" +
        s"background:$eBg;border:1px solid $eBorder;border-radius:${UIDesign.Radius.sm};" +
        s"font-size:${UIDesign.FontSize.base};color:$eText;'>" +
        s"No model configured. Use <code style='background:$codeBg;padding:1px ${UIDesign.Space.sm};" +
        s"border-radius:${UIDesign.Radius.sm};'>:set model &lt;model-id&gt;</code> or " +
        "<b>Plugins → Plugin Options → Isabelle Assistant</b> to set one. " +
        s"Run <code style='background:$codeBg;padding:1px ${UIDesign.Space.sm};" +
        s"border-radius:${UIDesign.Radius.sm};'>:models</code> to see available models.</div>"
    } else ""

    // Example prompts: each click enqueues the chat command as if the user
    // had typed it. Emitted only when a real registrar is supplied; tests
    // that don't pass one keep their old expectations.
    val examples = List(":explain", ":suggest", ":verify by simp")
    val examplesHtml = registerExampleAction match {
      case None => ""
      case Some(register) =>
        val links = examples.map { cmd =>
          val id = register(cmd)
          val safeCmd = HtmlUtil.escapeHtml(cmd)
          s"<a href='action:insert:$id' style='color:$linkColor;text-decoration:none;font-weight:bold;'>$safeCmd</a>"
        }.mkString(" · ")
        s"<div style='margin-top:${UIDesign.Space.sm};font-size:${UIDesign.FontSize.sm};color:$wMuted;'>" +
          s"Try: $links</div>"
    }

    val body =
      s"<div style='color:$wText;font-size:${UIDesign.FontSize.base};'>" +
        "AI assistant for Isabelle/HOL proofs, powered by AWS Bedrock.<br/>" +
        s"Type a message or click <a href='action:insert:$helpId' " +
        s"style='color:$linkColor;text-decoration:none;font-weight:bold;'>:help</a> " +
        "to see all available commands. " +
        s"<span style='font-size:${UIDesign.FontSize.sm};color:$wMuted;'>" +
        "(Enter sends, Shift+Enter for newline)</span></div>" +
        examplesHtml +
        modelWarning

    s"<div style='margin:${UIDesign.Space.md} 0;padding:${UIDesign.Space.md} ${UIDesign.Space.lg};" +
      s"background:$wBg;border:1px solid $wBorder;border-radius:${UIDesign.Radius.md};'>" +
      s"<div style='font-weight:bold;color:$wTitle;margin-bottom:${UIDesign.Space.sm};'>Isabelle Assistant</div>" +
      body +
      "</div>"
  }
}
