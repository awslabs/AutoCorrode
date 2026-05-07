/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import java.awt.{Color, Insets}
import java.awt.image.BufferedImage
import java.security.MessageDigest
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.util.Locale
import java.util.concurrent.{ConcurrentHashMap, Executors, ThreadFactory, TimeUnit}
import javax.imageio.ImageIO
import scala.util.control.NonFatal

/** Markdown-to-HTML renderer for the chat panel. Handles headings, bold,
  * italic, inline code, code fences (with clickable isabelle blocks),
  * bullet/numbered lists, markdown tables, Mermaid diagrams (via local mmdc),
  * and LaTeX math (via JLaTeXMath → BufferedImage).
  */
object MarkdownRenderer {

  @volatile private var syntheticImageReadyCallback: Option[() => Unit] = None

  /** Register a callback invoked when a deferred synthetic image render
    * (currently Mermaid) completes and the UI should refresh.
    */
  def setSyntheticImageReadyCallback(callback: () => Unit): Unit = synchronized {
    syntheticImageReadyCallback = Option(callback)
  }

  /** Code font family string for HTML. Always uses Source Code Pro as primary.
    */
  def codeFont: String =
    "'Source Code Pro', 'Menlo', 'Consolas', 'Monaco', monospace"

  def toHtml(markdown: String): String =
    s"<html><body style='font-family:sans-serif;font-size:${UIDesign.FontSize.md};padding:${UIDesign.Space.md};'>${toBodyHtml(markdown)}</body></html>"

  /** Render markdown to HTML body fragment (no clickable isabelle blocks). */
  def toBodyHtml(markdown: String): String = renderBody(markdown, None)

  /** Render markdown with clickable isabelle code blocks.
    * @param registerAction
    *   callback: takes code string, returns action ID
    */
  def toBodyHtmlWithActions(
      markdown: String,
      registerAction: String => String
  ): String =
    renderBody(markdown, Some(registerAction))

  private def renderBody(
      markdown: String,
      registerAction: Option[String => String]
  ): String = {
    val lines = markdown.split("\n", -1)
    val sb = new StringBuilder
    var i = 0
    while (i < lines.length) {
      val line = lines(i)
      if (line.trim.startsWith("```")) {
        i = renderCodeBlock(lines, i, sb, registerAction)
      } else if (
        line.trim.startsWith("|") && i + 1 < lines.length && lines(i + 1).trim
          .matches("""\|[\s:|-]+\|""")
      ) {
        i = renderTable(lines, i, sb)
      } else if (line.trim.startsWith("$$")) {
        i = renderDisplayMath(lines, i, sb)
      } else {
        sb.append(processLine(line))
        i += 1
      }
    }
    sb.toString
  }

  private def renderCodeBlock(
      lines: Array[String],
      start: Int,
      sb: StringBuilder,
      registerAction: Option[String => String]
  ): Int = {
    val tag = lines(start).trim.stripPrefix("```").trim
    val tagName = tag.takeWhile(!_.isWhitespace).toLowerCase(Locale.ROOT)
    val code = new StringBuilder
    var i = start + 1
    while (i < lines.length && !lines(i).trim.startsWith("```")) {
      if (code.nonEmpty) code.append("\n")
      code.append(lines(i))
      i += 1
    }
    // i now points at closing ``` or past end
    val codeStr = code.toString
    val escaped = escapeHtml(codeStr)

    if (tag.startsWith("action:")) {
      val id = tag.stripPrefix("action:")
      appendClickableBlock(sb, escaped, id)
    } else if (tagName == "isabelle") {
      registerAction match {
        case Some(register) =>
          val id = register(codeStr)
          appendClickableBlock(sb, escaped, id)
        case None =>
          val highlighted = highlightIsabelle(escaped)
          appendPreBlock(sb, highlighted)
      }
    } else if (tagName == "mermaid") {
      appendMermaidBlock(sb, codeStr)
    } else {
      // Apply syntax highlighting if it's an isabelle block
      val highlighted =
        if (tagName == "isabelle") highlightIsabelle(escaped) else escaped
      appendPreBlock(sb, highlighted)
    }
    i + 1 // skip closing ```
  }

  /** Standard `<pre>` code-block wrapper used by non-clickable code fences.
    * All tokens come from `UIDesign` so font/radius/padding stay consistent. */
  private def appendPreBlock(sb: StringBuilder, innerHtml: String): Unit = {
    val codeBg = UIColors.CodeBlock.background
    val codeBorder = UIColors.CodeBlock.border
    val codeFg = UIColors.CodeBlock.text
    sb.append(
      s"<pre style='font-family:$codeFont;font-size:${UIDesign.FontSize.lg};" +
        s"background:$codeBg;color:$codeFg;" +
        s"padding:${UIDesign.Space.lg} ${UIDesign.Space.lg};margin:${UIDesign.Space.sm} 0;" +
        s"border:1px solid $codeBorder;border-radius:${UIDesign.Radius.sm};" +
        "white-space:pre;overflow-x:auto;line-height:1.5;'>"
    )
    sb.append(innerHtml)
    sb.append("</pre>")
  }

  private case class RenderedImage(url: String, width: Int, height: Int)

  private sealed trait MermaidRenderState
  private case class MermaidReady(image: RenderedImage) extends MermaidRenderState
  private case object MermaidPending extends MermaidRenderState
  private case class MermaidUnavailable(reason: String) extends MermaidRenderState

  private def appendMermaidBlock(sb: StringBuilder, code: String): Unit = {
    val diagram = code.trim
    if (diagram.isEmpty) {
      sb.append(
        s"<div style='margin:${UIDesign.Space.sm} 0;color:${UIColors.Muted.text};font-style:italic;'>" +
          "Empty Mermaid diagram block.</div>"
      )
      return
    }

    resolveMermaid(diagram) match {
      case MermaidReady(img) =>
        sb.append(
          s"<div style='margin:${UIDesign.Space.md} 0;text-align:center;'>" +
            s"<img src='${img.url}' width='${img.width}' height='${img.height}' " +
            "style='max-width:100%;height:auto;' /></div>"
        )
      case MermaidPending =>
        sb.append(
          s"<div style='margin:${UIDesign.Space.sm} 0 ${UIDesign.Space.xs};" +
            s"color:${UIColors.Muted.text};font-size:${UIDesign.FontSize.sm};'>" +
            "<b>Mermaid:</b> rendering diagram…</div>"
        )
        appendPreBlock(sb, escapeHtml(code))
      case MermaidUnavailable(reason) =>
        sb.append(
          s"<div style='margin:${UIDesign.Space.sm} 0 ${UIDesign.Space.xs};" +
            s"color:${UIColors.Badge.accentText};font-size:${UIDesign.FontSize.sm};'>" +
            s"<b>Mermaid rendering unavailable:</b> ${escapeHtml(reason)}</div>"
        )
        appendPreBlock(sb, escapeHtml(code))
    }
  }

  private def appendClickableBlock(
      sb: StringBuilder,
      escapedCode: String,
      id: String
  ): Unit = {
    val rawCode = escapedCode
      .replace("&amp;", "&")
      .replace("&lt;", "<")
      .replace("&gt;", ">")
    val encodedForUrl = java.net.URLEncoder.encode(rawCode, "UTF-8")
    val codeBg = UIColors.CodeBlock.background
    val codeBorder = UIColors.CodeBlock.border
    val codeFg = UIColors.CodeBlock.text
    val actionBg = UIColors.CodeBlock.actionBackground
    val actionBorder = UIColors.CodeBlock.actionBorder

    // Apply Isabelle syntax highlighting
    val highlighted = highlightIsabelle(escapedCode)

    sb.append(
      s"<div style='margin:${UIDesign.Space.sm} 0 ${UIDesign.Space.md};" +
        s"border:1px solid $codeBorder;border-radius:${UIDesign.Radius.sm};overflow:hidden;'>"
    )
    // Code area without <a> wrapper — JEditorPane forces blue on links
    sb.append(
      s"<pre style='font-family:$codeFont;font-size:${UIDesign.FontSize.lg};" +
        s"background:$codeBg;color:$codeFg;" +
        s"padding:${UIDesign.Space.lg} ${UIDesign.Space.xl};margin:0;border:none;" +
        "white-space:pre;overflow-x:auto;line-height:1.5;'>"
    )
    sb.append(highlighted)
    sb.append("</pre>")
    // Action bar
    sb.append(
      s"<div style='padding:${UIDesign.Space.md} ${UIDesign.Space.lg};background:$actionBg;border-top:1px solid $actionBorder;'>"
    )
    sb.append(actionPill(s"action:insert:$id", "Insert"))
    sb.append("&nbsp;&nbsp;")
    sb.append(actionPill(s"action:copy:$encodedForUrl", "Copy"))
    sb.append("</div></div>")
  }

  /** Small pill-styled `<a>` button. Shared between the code-block action bar
    * and the message-bubble copy affordance for consistent affordance. */
  private def actionPill(href: String, label: String): String = {
    val bg = UIColors.CodeButton.background
    val text = UIColors.CodeButton.text
    val brdr = UIColors.CodeButton.border
    s"<a href='$href' style='display:inline-block;text-decoration:none;" +
      s"padding:${UIDesign.Space.sm} ${UIDesign.Space.lg};background:$bg;color:$text;" +
      s"border:1px solid $brdr;border-radius:${UIDesign.Radius.sm};" +
      s"font-weight:normal;font-size:${UIDesign.FontSize.base};'>$label</a>"
  }

  // Cached compiled patterns for syntax highlighting
  private lazy val keywordPattern: java.util.regex.Pattern = {
    val keywords = IsabelleKeywords.forSyntaxHighlighting.toList.sortBy(-_.length) // longest first
    val alternation = keywords.map(java.util.regex.Pattern.quote).mkString("\\b(", "|", ")\\b")
    java.util.regex.Pattern.compile(alternation)
  }

  private lazy val typePattern: java.util.regex.Pattern = {
    val types = IsabelleKeywords.builtinTypes.toList.sortBy(-_.length) // longest first
    val alternation = types.map(java.util.regex.Pattern.quote).mkString("\\b(", "|", ")\\b")
    java.util.regex.Pattern.compile(alternation)
  }

  private val entityProtectionPattern = java.util.regex.Pattern.compile("&[a-z]+;")
  private val stringLiteralPattern = java.util.regex.Pattern.compile("(&quot;[^&]*?&quot;)")
  private val commentPattern = java.util.regex.Pattern.compile("(\\(\\*.*?\\*\\))")

  /** Highlight Isabelle code with syntax coloring. Input is already
    * HTML-escaped. Protects HTML entities from highlighting to avoid corruption.
    * Uses compiled regex patterns for O(text) performance instead of O(keywords × text).
    */
  private def highlightIsabelle(escaped: String): String = {
    val keywordColor = UIColors.Syntax.keyword
    val typeColor = UIColors.Syntax.typeColor
    val commentColor = UIColors.Syntax.comment
    val stringColor = UIColors.Syntax.stringLiteral

    // Step 1: Extract and protect HTML entities
    val entityMap = scala.collection.mutable.Map[String, String]()
    var entityCounter = 0
    val matcher1 = entityProtectionPattern.matcher(escaped)
    val result1 = new StringBuffer()
    while (matcher1.find()) {
      val placeholder = s"\u0003E${entityCounter}\u0003"
      entityMap(placeholder) = matcher1.group()
      entityCounter += 1
      val _ = matcher1.appendReplacement(result1, java.util.regex.Matcher.quoteReplacement(placeholder))
    }
    val _ = matcher1.appendTail(result1)
    var result = result1.toString

    // Step 2: Apply syntax highlighting on entity-protected text
    // Highlight keywords using single compiled pattern
    result = keywordPattern.matcher(result).replaceAll(
      s"<span style='color:$keywordColor;'>$$1</span>"
    )

    // Highlight types using single compiled pattern
    result = typePattern.matcher(result).replaceAll(
      s"<span style='color:$typeColor;'>$$1</span>"
    )

    // Highlight string literals "..." (already entity-protected above)
    result = stringLiteralPattern.matcher(result).replaceAll(
      s"<span style='color:$stringColor;'>$$1</span>"
    )

    // Highlight comments (*...*) - already escaped as &lt;...&gt; but entity-protected
    result = commentPattern.matcher(result).replaceAll(
      s"<span style='color:$commentColor;font-style:italic;'>$$1</span>"
    )

    // Step 3: Restore HTML entities
    for ((placeholder, entity) <- entityMap) {
      result = result.replace(placeholder, entity)
    }

    result
  }

  /** Render a markdown table starting at line index `start`. Returns next line
    * index.
    */
  private def renderTable(
      lines: Array[String],
      start: Int,
      sb: StringBuilder
  ): Int = {
    val headerCells = parseTableRow(lines(start))
    val tableBorder = UIColors.Table.border
    val headerBg = UIColors.Table.headerBackground
    // Skip separator row (line start+1)
    var i = start + 2
    sb.append(
      s"<table style='border-collapse:collapse;margin:${UIDesign.Space.sm} 0;table-layout:fixed;width:100%;word-wrap:break-word;'>"
    )
    sb.append("<tr>")
    for (cell <- headerCells)
      sb.append(
        s"<th style='border:1px solid $tableBorder;padding:${UIDesign.Space.sm} ${UIDesign.Space.md};" +
          s"background:$headerBg;font-size:${UIDesign.FontSize.base};text-align:left;'>${processInline(cell)}</th>"
      )
    sb.append("</tr>")
    while (i < lines.length && lines(i).trim.startsWith("|")) {
      val cells = parseTableRow(lines(i))
      sb.append("<tr>")
      for (cell <- cells)
        sb.append(
          s"<td style='border:1px solid $tableBorder;padding:${UIDesign.Space.sm} ${UIDesign.Space.md};" +
            s"font-size:${UIDesign.FontSize.base};'>${processInline(cell)}</td>"
        )
      sb.append("</tr>")
      i += 1
    }
    sb.append("</table>")
    i
  }

  private def parseTableRow(line: String): List[String] = {
    val trimmed = line.trim.stripPrefix("|").stripSuffix("|")
    trimmed.split("\\|").map(_.trim).toList
  }

  /** Render $$...$$ display math block. Returns next line index. */
  private def renderDisplayMath(
      lines: Array[String],
      start: Int,
      sb: StringBuilder
  ): Int = {
    val first = lines(start).trim.stripPrefix("$$").trim
    if (first.endsWith("$$") && first.length > 2) {
      // Single-line: $$formula$$
      val formula = first.stripSuffix("$$").trim
      sb.append(
        s"<div style='text-align:center;margin:${UIDesign.Space.md} 0;'>${renderLatex(formula, UIDesign.fp(18f))}</div>"
      )
      start + 1
    } else {
      // Multi-line: collect until $$, with a cap so a malformed response
      // (unmatched opening $$) cannot consume the remainder of the message
      // as a single formula.
      val formulaParts = new StringBuilder
      if (first.nonEmpty) formulaParts.append(first)
      var i = start + 1
      val hardStop = math.min(lines.length, start + 1 + maxMultilineFormulaLines)
      while (i < hardStop && !lines(i).trim.startsWith("$$")) {
        if (formulaParts.nonEmpty) formulaParts.append(" ")
        formulaParts.append(lines(i).trim)
        i += 1
      }
      val foundClose = i < lines.length && lines(i).trim.startsWith("$$")
      if (foundClose) {
        sb.append(
          s"<div style='text-align:center;margin:${UIDesign.Space.md} 0;'>${renderLatex(formulaParts.toString, 18f)}</div>"
        )
        i + 1 // skip closing $$
      } else {
        // No closing $$ within the cap — emit the consumed lines as literal
        // text so the rest of the message is still rendered normally.
        sb.append(s"<div>${escapeHtml("$$")}</div>")
        for (j <- start + 1 until i) {
          sb.append(processLine(lines(j)))
        }
        i
      }
    }
  }

  private def processLine(line: String): String = {
    if (line.startsWith("### "))
      s"<h3 style='margin:${UIDesign.Space.md} 0 ${UIDesign.Space.xs};font-size:${UIDesign.FontSize.lg};'>${processInline(line.drop(4))}</h3>"
    else if (line.startsWith("## "))
      s"<h2 style='margin:${UIDesign.Space.md} 0 ${UIDesign.Space.xs};font-size:${UIDesign.FontSize.lg};font-weight:bold;'>${processInline(line.drop(3))}</h2>"
    else if (line.startsWith("# "))
      s"<h1 style='margin:${UIDesign.Space.md} 0 ${UIDesign.Space.sm};font-size:${UIDesign.FontSize.xl};'>${processInline(line.drop(2))}</h1>"
    else if (line.startsWith("- "))
      s"<div style='margin:1px 0;padding-left:${UIDesign.Space.lg};'>• ${processInline(line.drop(2))}</div>"
    else if (line.matches("""^\d+\.\s.*""")) {
      val content = line.replaceFirst("""^\d+\.\s""", "")
      s"<div style='margin:1px 0;padding-left:${UIDesign.Space.lg};'>${line.takeWhile(_ != ' ')} ${processInline(content)}</div>"
    } else if (line.trim.isEmpty) s"<div style='height:${UIDesign.Space.md};'></div>"
    else
      s"<div style='margin:1px 0;line-height:1.4;'>${processInline(line)}</div>"
  }

  /** Process inline formatting in a single pass: inline code, inline LaTeX
    * math, bold, italic. The scanner walks the string once, emitting either a
    * ready-made HTML fragment (for code / latex / bold / italic) or an
    * escaped literal slice (for plain text). Unmatched delimiters fall back
    * to literal text, mirroring the previous regex-based behavior for inputs
    * that don't contain inline formatting at all.
    */
  private def processInline(text: String): String = {
    val out = new StringBuilder(text.length + 16)
    val literal = new StringBuilder
    def flushLiteral(): Unit = {
      if (literal.nonEmpty) {
        out.append(escapeHtml(literal.toString))
        literal.setLength(0)
      }
    }
    val inlineCodeBg = UIColors.inlineCodeBackground
    val codeOpen =
      s"<code style='background:$inlineCodeBg;padding:1px ${UIDesign.Space.sm};font-family:$codeFont;" +
        s"font-size:${UIDesign.FontSize.base};border-radius:${UIDesign.Radius.sm};'>"
    val codeClose = "</code>"

    val n = text.length
    var i = 0
    while (i < n) {
      val c = text.charAt(i)
      c match {
        case '`' =>
          val end = text.indexOf('`', i + 1)
          if (end > i) {
            flushLiteral()
            out.append(codeOpen)
            out.append(escapeHtml(text.substring(i + 1, end)))
            out.append(codeClose)
            i = end + 1
          } else {
            literal.append(c)
            i += 1
          }
        case '$' if i + 1 < n && text.charAt(i + 1) != '$' &&
          (i == 0 || text.charAt(i - 1) != '$') =>
          var j = i + 1
          var closing = -1
          while (j < n && closing < 0) {
            val ch = text.charAt(j)
            if (ch == '$' && (j + 1 >= n || text.charAt(j + 1) != '$') &&
              text.charAt(j - 1) != '$') {
              closing = j
            } else {
              j += 1
            }
          }
          if (closing > i + 1) {
            flushLiteral()
            out.append(renderLatex(text.substring(i + 1, closing), UIDesign.fp(13f)))
            i = closing + 1
          } else {
            literal.append(c)
            i += 1
          }
        case '*' if i + 1 < n && text.charAt(i + 1) == '*' =>
          val close = text.indexOf("**", i + 2)
          if (close > i + 1) {
            flushLiteral()
            out.append("<b>")
            out.append(processInline(text.substring(i + 2, close)))
            out.append("</b>")
            i = close + 2
          } else {
            literal.append(c)
            i += 1
          }
        case '*' =>
          val close = text.indexOf('*', i + 1)
          if (close > i) {
            flushLiteral()
            out.append("<i>")
            out.append(processInline(text.substring(i + 1, close)))
            out.append("</i>")
            i = close + 1
          } else {
            literal.append(c)
            i += 1
          }
        case _ =>
          literal.append(c)
          i += 1
      }
    }
    flushLiteral()
    out.toString
  }

  /** LRU cache of rendered synthetic images, keyed by synthetic URL for
    * JEditorPane.
    */
  private val maxImageCacheSize = 200
  private val imageCache = new java.util.LinkedHashMap[String, java.awt.Image](
    maxImageCacheSize + 1,
    0.75f,
    true
  ) {
    override def removeEldestEntry(
        eldest: java.util.Map.Entry[String, java.awt.Image]
    ): Boolean =
      size() > maxImageCacheSize
  }
  private val imageCounter = new java.util.concurrent.atomic.AtomicInteger(0)

  /** Get a cached image by its synthetic URL. Called by the HTMLDocument's
    * image loading.
    */
  def getCachedImage(url: String): Option[java.awt.Image] = synchronized {
    Option(imageCache.get(url))
  }

  def isSyntheticImageUrl(url: String): Boolean =
    url.startsWith("latex://") || url.startsWith("mermaid://")

  private def cacheSyntheticImage(
      scheme: String,
      image: java.awt.Image
  ): String = synchronized {
    val id = s"$scheme://${imageCounter.getAndIncrement()}"
    imageCache.put(id, image)
    id
  }

  private def cacheSyntheticImageWithId(
      id: String,
      image: java.awt.Image
  ): String = synchronized {
    imageCache.put(id, image)
    id
  }

  @volatile private var mermaidCliAvailability: Option[Boolean] = None
  private val mermaidRenderFailures =
    new ConcurrentHashMap[String, String]()
  private val mermaidRenderInProgress =
    new ConcurrentHashMap[String, java.lang.Boolean]()
  private val mermaidRenderExecutor = Executors.newSingleThreadExecutor(
    new ThreadFactory {
      override def newThread(r: Runnable): Thread = {
        val t = new Thread(r, "assistant-mermaid-render")
        t.setDaemon(true)
        t
      }
    }
  )
  private val mermaidDisableSubprocessProp =
    "assistant.mermaid.disable_subprocess"
  private val maxMermaidChars = 20000
  private val maxMermaidPixels = 8_000_000
  private val mermaidRenderTimeoutSeconds = 20

  /** Hard cap on how many lines a multi-line `$$...$$` formula may span.
    * Without this a malformed message (unmatched opening `$$`) would swallow
    * the remainder of the response as a single formula. */
  private val maxMultilineFormulaLines = 200

  private def isMermaidSubprocessDisabled: Boolean =
    java.lang.Boolean.getBoolean(mermaidDisableSubprocessProp)

  private def isMermaidCliAvailable: Boolean = mermaidCliAvailability match {
    case Some(v) => v
    case None =>
      synchronized {
        mermaidCliAvailability match {
          case Some(v) => v
          case None    =>
            val available = try {
              val process = new ProcessBuilder("mmdc", "--version")
                .redirectErrorStream(true)
                .start()
              val finished = process.waitFor(2, TimeUnit.SECONDS)
              if (!finished) {
                process.destroyForcibly()
                false
              } else {
                process.exitValue() == 0
              }
            } catch {
              case _: Exception => false
            }
            mermaidCliAvailability = Some(available)
            available
        }
      }
  }

  private def mermaidCacheId(diagram: String): String = {
    val digest = MessageDigest.getInstance("SHA-256")
      .digest(diagram.getBytes(StandardCharsets.UTF_8))
    val hex = digest.take(12).map { b =>
      f"${b & 0xff}%02x"
    }.mkString
    s"mermaid://$hex"
  }

  private def notifySyntheticImageReady(): Unit =
    syntheticImageReadyCallback.foreach { cb =>
      try cb()
      catch {
        case ex: Exception =>
          Output.warning(
            s"[Assistant] Mermaid refresh callback failed: ${ex.getMessage}"
          )
      }
    }

  private def resolveMermaid(diagram: String): MermaidRenderState = {
    if (isMermaidSubprocessDisabled)
      return MermaidUnavailable(
        s"subprocess execution disabled via -D$mermaidDisableSubprocessProp=true"
      )

    if (diagram.length > maxMermaidChars)
      return MermaidUnavailable(
        s"diagram is too large (${diagram.length} chars, limit: $maxMermaidChars)"
      )

    if (!isMermaidCliAvailable)
      return MermaidUnavailable(
        "local Mermaid CLI (`mmdc`) not found in PATH. Install mermaid-cli for offline diagram rendering."
      )

    val cacheId = mermaidCacheId(diagram)
    getCachedImage(cacheId) match {
      case Some(img) =>
        MermaidReady(
          RenderedImage(cacheId, img.getWidth(null), img.getHeight(null))
        )
      case None =>
        Option(mermaidRenderFailures.get(cacheId)) match {
          case Some(reason) =>
            MermaidUnavailable(reason)
          case None =>
            scheduleMermaidRender(cacheId, diagram)
            MermaidPending
        }
    }
  }

  private def scheduleMermaidRender(cacheId: String, diagram: String): Unit = {
    if (
      mermaidRenderInProgress.putIfAbsent(cacheId, java.lang.Boolean.TRUE) != null
    ) return

    mermaidRenderExecutor.execute(new Runnable {
      override def run(): Unit = {
        try {
          renderMermaidImage(diagram) match {
            case Right(image) =>
              val _ = mermaidRenderFailures.remove(cacheId)
              val _ = cacheSyntheticImageWithId(cacheId, image)
            case Left(reason) =>
              val _ = mermaidRenderFailures.put(cacheId, reason)
          }
        } finally {
          mermaidRenderInProgress.remove(cacheId)
          notifySyntheticImageReady()
        }
      }
    })
  }

  private def renderMermaidImage(diagram: String): Either[String, BufferedImage] = {
    val tempDir = Files.createTempDirectory("assistant-mermaid-")
    val input = tempDir.resolve("diagram.mmd")
    val output = tempDir.resolve("diagram.png")
    try {
      Files.write(input, diagram.getBytes(StandardCharsets.UTF_8))
      val process = new ProcessBuilder(
        "mmdc",
        "--input",
        input.toString,
        "--output",
        output.toString,
        "--backgroundColor",
        "transparent"
      ).redirectErrorStream(true).start()

      val finished = process.waitFor(mermaidRenderTimeoutSeconds.toLong, TimeUnit.SECONDS)
      if (!finished) {
        process.destroyForcibly()
        Left(s"render timed out after ${mermaidRenderTimeoutSeconds}s")
      } else {
        val processOutput = {
          // Cap the read so a pathological mmdc invocation cannot
          // balloon the JVM heap by streaming unbounded output at us.
          // The actual payload we care about is a short error message;
          // anything longer is noise.
          val cap = 8192
          val in = process.getInputStream
          try {
            val buf = new Array[Byte](cap)
            var total = 0
            var done = false
            while (!done && total < cap) {
              val n = in.read(buf, total, cap - total)
              if (n < 0) done = true else total += n
            }
            new String(buf, 0, total, StandardCharsets.UTF_8).trim
          } finally {
            in.close()
          }
        }
        if (process.exitValue() != 0) {
          val msg =
            if (processOutput.isEmpty)
              s"mmdc exited with code ${process.exitValue()}"
            else processOutput.take(400)
          Left(msg)
        } else if (!Files.exists(output)) {
          Left("mmdc completed but produced no output image")
        } else {
          val image = ImageIO.read(output.toFile)
          if (image == null) Left("could not decode Mermaid output image")
          else if (image.getWidth.toLong * image.getHeight.toLong > maxMermaidPixels)
            Left(
              s"rendered Mermaid image is too large (${image.getWidth}x${image.getHeight})"
            )
          else Right(image)
        }
      }
    } catch {
      case ex: Exception => Left(ex.getMessage)
    } finally {
      try Files.deleteIfExists(input)
      catch { case NonFatal(_) => () }
      try Files.deleteIfExists(output)
      catch { case NonFatal(_) => () }
      try {
        val _ = Files.deleteIfExists(tempDir)
      }
      catch { case NonFatal(_) => () }
    }
  }

  /** Render a LaTeX formula to an img tag with a synthetic URL. The image is
    * stored in imageCache and loaded by SyntheticImageView.
    */
  private def renderLatex(formula: String, size: Float): String = {
    try {
      val icon = new org.scilab.forge.jlatexmath.TeXFormula(formula)
        .createTeXIcon(
          org.scilab.forge.jlatexmath.TeXConstants.STYLE_DISPLAY,
          size
        )
      icon.setInsets(new Insets(2, 2, 2, 2))
      val w = icon.getIconWidth
      val h = icon.getIconHeight
      if (w <= 0 || h <= 0) {
        escapeHtml("$" + formula + "$")
      } else {
        val img = new BufferedImage(w, h, BufferedImage.TYPE_INT_ARGB)
        val g2 = img.createGraphics()
        g2.setColor(Color.WHITE)
        g2.fillRect(0, 0, w, h)
        icon.paintIcon(null, g2, 0, 0)
        g2.dispose()
        val id = cacheSyntheticImage("latex", img)
        s"<img src='$id' width='$w' height='$h' style='vertical-align:middle;' />"
      }
    } catch {
      case _: Exception =>
        s"<i style='color:${UIColors.Muted.text};'>${escapeHtml(formula)}</i>"
    }
  }

  private def escapeHtml(s: String): String = HtmlUtil.escapeHtml(s)
}
