/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import scala.annotation.unused

import ToolArgs._

/** Executes the memory_* tools that back the assistant's persistent memory
  * store. Each handler here takes the raw ToolArgs + View, performs the
  * MemoryStore operation, and optionally injects a rich HTML widget into the
  * chat view. Split out of AssistantTools to keep tool-group code cohesive.
  */
private[assistant] object MemoryToolHandler {

  def execMemoryAdd(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val topic = safeStringArg(args, "topic", 100)
    val title = safeStringArg(args, "title", 200)
    val body = safeStringArg(args, "body", 2000)
    val result = MemoryStore.addMemory(topic, title, body)
    GUI_Thread.later {
      val html = buildMemoryAddedHtml(topic, title, body)
      ChatAction.addMessage(
        ChatAction.Message(
          ChatAction.Widget,
          html,
          java.time.LocalDateTime.now(),
          rawHtml = true,
          transient = true
        )
      )
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    result
  }

  def execMemoryDelete(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val memoryId = intArg(args, "memory_id", -1)
    val result = MemoryStore.deleteMemory(memoryId)
    postMemoryWidget(buildMemoryStatusHtml("deleted", result))
    result
  }

  def execMemoryDeleteTopic(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val topic = safeStringArg(args, "topic", 100)
    val result = MemoryStore.deleteTopic(topic)
    postMemoryWidget(buildMemoryStatusHtml("topic_deleted", result))
    result
  }

  def execMemoryListTopics(@unused view: View): String =
    MemoryStore.listTopics()

  def execMemoryList(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val topic = safeStringArg(args, "topic", 100)
    MemoryStore.listMemories(topic)
  }

  def execMemoryGet(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val memoryId = intArg(args, "memory_id", -1)
    MemoryStore.getMemory(memoryId)
  }

  def execMemorySearch(args: ResponseParser.ToolArgs, @unused view: View): String = {
    val query = safeStringArg(args, "query", 500)
    MemoryStore.searchMemories(query)
  }

  private def postMemoryWidget(html: String): Unit = {
    GUI_Thread.later {
      ChatAction.addMessage(
        ChatAction.Message(
          ChatAction.Widget,
          html,
          java.time.LocalDateTime.now(),
          rawHtml = true,
          transient = true
        )
      )
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
  }

  /** Word-aware truncation: cut on the nearest whitespace before `max`
    * and append an ellipsis. Falls back to a hard cut if there's no whitespace. */
  private def truncateWord(s: String, max: Int): String = {
    if (s.length <= max) s
    else {
      val cut = s.take(max)
      val lastSpace = cut.lastIndexWhere(_.isWhitespace)
      val base =
        if (lastSpace > max / 2) cut.substring(0, lastSpace).trim
        else cut.trim
      base + "…"
    }
  }

  private def buildMemoryAddedHtml(topic: String, title: String, body: String): String = {
    val border = UIColors.Memory.border
    val headerText = UIColors.Memory.headerText
    val labelColor = UIColors.Memory.labelColor
    val memoryText = UIColors.Memory.memoryText
    val truncBody = truncateWord(body, 100)

    val inner =
      s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.xs};font-weight:bold;'>Memory Added</div>" +
        s"<div style='font-size:${UIDesign.FontSize.base};color:$memoryText;margin-bottom:${UIDesign.Space.xs};'>" +
        s"&ldquo;${HtmlUtil.escapeHtml(title)}&rdquo;</div>" +
        s"<div style='font-size:${UIDesign.FontSize.xs};color:$labelColor;margin-top:${UIDesign.Space.sm};'>" +
        s"Topic: <span style='color:$memoryText;'>${HtmlUtil.escapeHtml(topic)}</span></div>" +
        s"<div style='font-size:${UIDesign.FontSize.xs};color:$labelColor;'>" +
        HtmlUtil.escapeHtml(truncBody) +
        "</div>"

    UIDesign.card(inner, border)
  }

  private def buildMemoryStatusHtml(status: String, result: String): String = {
    val border = UIColors.Memory.border
    val headerText = UIColors.Memory.headerText
    val memoryText = UIColors.Memory.memoryText
    val action = status match {
      case "deleted"       => "Memory deleted"
      case "topic_deleted" => "Topic deleted"
      case _               => "Memory operation"
    }

    val inner =
      s"<div style='font-size:${UIDesign.FontSize.sm};color:$headerText;margin-bottom:${UIDesign.Space.xs};font-weight:bold;'>" +
        action +
        "</div>" +
        s"<div style='font-size:${UIDesign.FontSize.sm};color:$memoryText;margin-top:${UIDesign.Space.xs};'>" +
        HtmlUtil.escapeHtml(result) +
        "</div>"

    UIDesign.card(inner, border)
  }
}
