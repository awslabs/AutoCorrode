/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.buffer.JEditBuffer

import scala.collection.mutable
import scala.jdk.CollectionConverters._

/** Lightweight theory-header parsing without direct Isabelle runtime traversal. */
object TheoryMetadata {
  private final case class Header(name: Option[String], imports: List[String])

  private val TheoryPattern = """(?m)^\s*theory\s+([^\s]+)""".r
  private val ImportsPattern = """(?s)\bimports\b\s+(.*?)(?:\bbegin\b|\z)""".r
  private val ImportTokenPattern = """"[^"]+"|[^\s"]+""".r

  private def source(buffer: JEditBuffer): String =
    buffer.getText(0, buffer.getLength)

  private def normalizeTheoryId(raw: String): String = {
    val trimmed = Option(raw).map(_.trim).getOrElse("")
    val unquoted =
      if (trimmed.startsWith("\"") && trimmed.endsWith("\"") && trimmed.length >= 2)
        trimmed.substring(1, trimmed.length - 1)
      else trimmed
    unquoted
      .stripSuffix(".thy")
      .replace('\\', '.')
      .replace('/', '.')
      .trim
  }

  private def parseHeader(text: String): Header = {
    val name = TheoryPattern.findFirstMatchIn(text).map(m =>
      normalizeTheoryId(m.group(1))
    ).filter(_.nonEmpty)
    val imports = ImportsPattern
      .findFirstMatchIn(text)
      .map(_.group(1))
      .map { block =>
        ImportTokenPattern
          .findAllIn(block)
          .map(normalizeTheoryId)
          .filter(_.nonEmpty)
          .toList
      }
      .getOrElse(Nil)
    Header(name = name, imports = imports)
  }

  private def parseHeader(buffer: JEditBuffer): Header = parseHeader(source(buffer))

  private def openTheoryBuffers(): List[JEditBuffer] =
    org.gjt.sp.jedit.jEdit
      .getBufferManager()
      .getBuffers()
      .asScala
      .toList
      .filter { b =>
        val path = Option(b.asInstanceOf[org.gjt.sp.jedit.Buffer].getPath)
          .map(_.trim)
          .getOrElse("")
        path.endsWith(".thy") || parseHeader(b).name.nonEmpty
      }

  private def theoryIndex(): Map[String, Header] = {
    val entries = mutable.Map.empty[String, Header]
    openTheoryBuffers().foreach { b =>
      val header = parseHeader(b)
      header.name.foreach(name => entries.update(name, header))
      val path = Option(b.asInstanceOf[org.gjt.sp.jedit.Buffer].getPath)
        .map(_.trim)
        .getOrElse("")
      if (path.nonEmpty) {
        val fileName = java.io.File(path).getName
        val normalizedFile = normalizeTheoryId(fileName)
        if (normalizedFile.nonEmpty && !entries.contains(normalizedFile))
          entries.update(normalizedFile, header)
      }
    }
    entries.toMap
  }

  private def matchesTheory(importId: String, target: String): Boolean = {
    val normalizedImport = normalizeTheoryId(importId)
    val normalizedTarget = normalizeTheoryId(target)
    normalizedImport == normalizedTarget ||
    normalizedImport.endsWith("." + normalizedTarget)
  }

  def theoryName(buffer: JEditBuffer): Option[String] =
    parseHeader(buffer).name

  def imports(buffer: JEditBuffer): List[String] =
    parseHeader(buffer).imports

  def hasImport(buffer: JEditBuffer, theoryName: String): Boolean = {
    val header = parseHeader(buffer)
    val direct = header.imports.exists(matchesTheory(_, theoryName))
    if (direct) true
    else {
      val index = theoryIndex()
      val seen = mutable.Set.empty[String]
      val queue = mutable.Queue.empty[String]
      header.imports.foreach(queue.enqueue(_))

      while (queue.nonEmpty) {
        val raw = queue.dequeue()
        val normalized = normalizeTheoryId(raw)
        if (!seen.contains(normalized)) {
          val _ = seen.add(normalized)
          if (matchesTheory(normalized, theoryName)) return true
          index.get(normalized).foreach { next =>
            next.imports.foreach(queue.enqueue(_))
          }
        }
      }
      false
    }
  }
}
