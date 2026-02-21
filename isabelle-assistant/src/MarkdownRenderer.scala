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
    s"<html><body style='font-family:sans-serif;font-size:12pt;padding:8px;'>${toBodyHtml(markdown)}</body></html>"

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
    } else if (tagName == "isabelle" && registerAction.isDefined) {
      val id = registerAction.get(codeStr)
      appendClickableBlock(sb, escaped, id)
    } else if (tagName == "mermaid") {
      appendMermaidBlock(sb, codeStr)
    } else {
      val codeBg = UIColors.CodeBlock.background
      val codeBorder = UIColors.CodeBlock.border
      // Apply syntax highlighting if it's an isabelle block
      val highlighted =
        if (tagName == "isabelle") highlightIsabelle(escaped) else escaped
      sb.append(
        s"<pre style='font-family:$codeFont;font-size:13pt;background:$codeBg;"
      )
      sb.append(
        s"padding:12px 14px;margin:4px 0;border:1px solid $codeBorder;border-radius:3px;"
      )
      sb.append("white-space:pre;overflow-x:auto;line-height:1.5;'>")
      sb.append(highlighted)
      sb.append("</pre>")
    }
    i + 1 // skip closing ```
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
        "<div style='margin:4px 0;color:#666;font-style:italic;'>Empty Mermaid diagram block.</div>"
      )
      return
    }

    resolveMermaid(diagram) match {
      case MermaidReady(img) =>
        sb.append(
          s"<div style='margin:8px 0;text-align:center;'><img src='${img.url}' width='${img.width}' height='${img.height}' style='max-width:100%;height:auto;' /></div>"
        )
      case MermaidPending =>
        val codeBg = UIColors.CodeBlock.background
        val codeBorder = UIColors.CodeBlock.border
        sb.append(
          "<div style='margin:4px 0 2px;color:#666;font-size:10.5pt;'><b>Mermaid:</b> rendering diagram...</div>"
        )
        sb.append(
          s"<pre style='font-family:$codeFont;font-size:13pt;background:$codeBg;padding:12px 14px;margin:4px 0;border:1px solid $codeBorder;border-radius:3px;white-space:pre;overflow-x:auto;line-height:1.5;'>"
        )
        sb.append(escapeHtml(code))
        sb.append("</pre>")
      case MermaidUnavailable(reason) =>
        val codeBg = UIColors.CodeBlock.background
        val codeBorder = UIColors.CodeBlock.border
        sb.append(
          s"<div style='margin:4px 0 2px;color:#8a3b00;font-size:10.5pt;'><b>Mermaid rendering unavailable:</b> ${escapeHtml(reason)}</div>"
        )
        sb.append(
          s"<pre style='font-family:$codeFont;font-size:13pt;background:$codeBg;padding:12px 14px;margin:4px 0;border:1px solid $codeBorder;border-radius:3px;white-space:pre;overflow-x:auto;line-height:1.5;'>"
        )
        sb.append(escapeHtml(code))
        sb.append("</pre>")
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
    // Unified code block with integrated action bar
    val codeBg = UIColors.CodeBlock.background
    val codeBorder = UIColors.CodeBlock.border
    val actionBg = UIColors.CodeBlock.actionBackground
    val actionBorder = UIColors.CodeBlock.actionBorder
    val btnBg = UIColors.CodeButton.background
    val btnText = UIColors.CodeButton.text
    val btnBorder = UIColors.CodeButton.border

    // Apply Isabelle syntax highlighting
    val highlighted = highlightIsabelle(escapedCode)

    sb.append(
      s"<div style='margin:4px 0 6px;border:1px solid $codeBorder;border-radius:4px;overflow:hidden;'>"
    )
    // Code area without <a> wrapper - JEditorPane forces blue on links
    sb.append(
      s"<pre style='font-family:$codeFont;font-size:13pt;background:$codeBg;color:#383a42;"
    )
    sb.append(
      "padding:14px 18px;margin:0;border:none;white-space:pre;overflow-x:auto;line-height:1.5;'>"
    )
    sb.append(highlighted)
    sb.append("</pre>")
    // Action bar with minimal button styling
    sb.append(
      s"<div style='padding:8px 14px;background:$actionBg;border-top:1px solid $actionBorder;'>"
    )
    // Insert button
    sb.append(
      s"<a href='action:insert:$id' style='display:inline-block;text-decoration:none;"
    )
    sb.append(s"padding:5px 14px;background:$btnBg;color:$btnText;")
    sb.append(
      s"border:1px solid $btnBorder;border-radius:3px;font-weight:normal;font-size:11pt;'>Insert</a>"
    )
    // Spacer between buttons
    sb.append("&nbsp;&nbsp;")
    // Copy button
    sb.append(
      s"<a href='action:copy:$encodedForUrl' style='display:inline-block;text-decoration:none;"
    )
    sb.append(s"padding:5px 14px;background:$btnBg;color:$btnText;")
    sb.append(
      s"border:1px solid $btnBorder;border-radius:3px;font-weight:normal;font-size:11pt;'>Copy</a>"
    )
    sb.append("</div></div>")
  }

  /** Highlight Isabelle code with syntax coloring. Input is already
    * HTML-escaped.
    */
  private def highlightIsabelle(escaped: String): String = {
    // Use canonical keyword database
    val keywords = IsabelleKeywords.forSyntaxHighlighting
    val types = IsabelleKeywords.builtinTypes

    val keywordColor = UIColors.Syntax.keyword
    val typeColor = UIColors.Syntax.typeColor
    val commentColor = UIColors.Syntax.comment
    val stringColor = UIColors.Syntax.stringLiteral

    var result = escaped

    // Highlight keywords using word boundaries (subtle, no bold)
    for (kw <- keywords) {
      val pattern = s"\\b($kw)\\b"
      result = result.replaceAll(
        pattern,
        s"<span style='color:$keywordColor;'>$$1</span>"
      )
    }

    // Highlight types
    for (typ <- types) {
      val pattern = s"\\b($typ)\\b"
      result = result.replaceAll(
        pattern,
        s"<span style='color:$typeColor;'>$$1</span>"
      )
    }

    // Highlight string literals "..."
    result = result.replaceAll(
      "(&quot;[^&]*?&quot;)",
      s"<span style='color:$stringColor;'>$$1</span>"
    )

    // Highlight comments (*...*) - already escaped as &lt;...&gt;
    result = result.replaceAll(
      "(\\(\\*.*?\\*\\))",
      s"<span style='color:$commentColor;font-style:italic;'>$$1</span>"
    )

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
      "<table style='border-collapse:collapse;margin:4px 0;table-layout:fixed;width:100%;word-wrap:break-word;'>"
    )
    sb.append("<tr>")
    for (cell <- headerCells)
      sb.append(
        s"<th style='border:1px solid $tableBorder;padding:4px 8px;background:$headerBg;font-size:11pt;text-align:left;'>${processInline(cell)}</th>"
      )
    sb.append("</tr>")
    while (i < lines.length && lines(i).trim.startsWith("|")) {
      val cells = parseTableRow(lines(i))
      sb.append("<tr>")
      for (cell <- cells)
        sb.append(
          s"<td style='border:1px solid $tableBorder;padding:4px 8px;font-size:11pt;'>${processInline(cell)}</td>"
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
        s"<div style='text-align:center;margin:6px 0;'>${renderLatex(formula, 18f)}</div>"
      )
      start + 1
    } else {
      // Multi-line: collect until $$
      val formulaParts = new StringBuilder
      if (first.nonEmpty) formulaParts.append(first)
      var i = start + 1
      while (i < lines.length && !lines(i).trim.startsWith("$$")) {
        if (formulaParts.nonEmpty) formulaParts.append(" ")
        formulaParts.append(lines(i).trim)
        i += 1
      }
      sb.append(
        s"<div style='text-align:center;margin:6px 0;'>${renderLatex(formulaParts.toString, 18f)}</div>"
      )
      i + 1 // skip closing $$
    }
  }

  private def processLine(line: String): String = {
    if (line.startsWith("### "))
      s"<h3 style='margin:6px 0 2px;font-size:13pt;'>${processInline(line.drop(4))}</h3>"
    else if (line.startsWith("## "))
      s"<h2 style='margin:8px 0 2px;font-size:14pt;'>${processInline(line.drop(3))}</h2>"
    else if (line.startsWith("# "))
      s"<h1 style='margin:8px 0 4px;font-size:15pt;'>${processInline(line.drop(2))}</h1>"
    else if (line.startsWith("- "))
      s"<div style='margin:1px 0;padding-left:12px;'>• ${processInline(line.drop(2))}</div>"
    else if (line.matches("""^\d+\.\s.*""")) {
      val content = line.replaceFirst("""^\d+\.\s""", "")
      s"<div style='margin:1px 0;padding-left:12px;'>${line.takeWhile(_ != ' ')} ${processInline(content)}</div>"
    } else if (line.trim.isEmpty) "<div style='height:6px;'></div>"
    else
      s"<div style='margin:1px 0;line-height:1.4;'>${processInline(line)}</div>"
  }

  /** Process inline formatting: bold, italic, inline code, inline LaTeX math.
    * NOTE: This uses multiple sequential regex passes. A single-pass state
    * machine would be faster for very large responses, but the current approach
    * is simpler and adequate for typical LLM response sizes (<10K chars).
    */
  private def processInline(text: String): String = {
    var result = text
    // Inline code first — protect contents from other processing
    result = result.replaceAll("""`([^`]+)`""", "\u0001C$1\u0001c")
    // Inline LaTeX: $...$ (not $$) — render and protect from HTML escaping
    val latexRendered = new java.util.concurrent.atomic.AtomicInteger(0)
    val latexMap = scala.collection.mutable.Map[String, String]()
    result = inlineLatexPattern.replaceAllIn(
      result,
      m => {
        val formula = m.group(1)
        val key = s"\u0002L${latexRendered.getAndIncrement()}\u0002"
        latexMap(key) = renderLatex(formula, 13f)
        java.util.regex.Matcher.quoteReplacement(key)
      }
    )
    // Bold
    result = result.replaceAll("""\*\*([\s\S]+?)\*\*""", "\u0001B$1\u0001b")
    // Italic
    result = result.replaceAll("""\*([^*]+)\*""", "\u0001I$1\u0001i")
    result = escapeHtml(result)
    result = result.replace("\u0001B", "<b>").replace("\u0001b", "</b>")
    result = result.replace("\u0001I", "<i>").replace("\u0001i", "</i>")
    val inlineCodeBg = UIColors.inlineCodeBackground
    result = result
      .replace(
        "\u0001C",
        s"<code style='background:$inlineCodeBg;padding:1px 4px;font-family:$codeFont;font-size:11pt;border-radius:2px;'>"
      )
      .replace("\u0001c", "</code>")
    // Restore LaTeX images (already HTML, must not be escaped)
    for ((key, html) <- latexMap) result = result.replace(key, html)
    result
  }

  // Match $...$ but not $$ (display math) and not escaped \$
  private val inlineLatexPattern = """(?<!\$)\$(?!\$)(.+?)(?<!\$)\$(?!\$)""".r

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
              mermaidRenderFailures.remove(cacheId)
              cacheSyntheticImageWithId(cacheId, image)
            case Left(reason) =>
              mermaidRenderFailures.put(cacheId, reason)
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

      val finished = process.waitFor(20, TimeUnit.SECONDS)
      if (!finished) {
        process.destroyForcibly()
        Left("render timed out after 20s")
      } else {
        val processOutput = {
          val in = process.getInputStream
          try new String(in.readAllBytes(), StandardCharsets.UTF_8).trim
          finally in.close()
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
      catch { case _: Throwable => }
      try Files.deleteIfExists(output)
      catch { case _: Throwable => }
      try Files.deleteIfExists(tempDir)
      catch { case _: Throwable => }
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
        s"<i style='color:#666;'>${escapeHtml(formula)}</i>"
    }
  }

  private def escapeHtml(s: String): String = HtmlUtil.escapeHtml(s)
}
