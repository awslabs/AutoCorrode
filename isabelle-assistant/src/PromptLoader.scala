/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import com.samskivert.mustache.Mustache
import scala.jdk.CollectionConverters._
import scala.io.Source

/**
 * Loads Mustache prompt templates from the prompts/ directory.
 * Caches auto-discovered system prompts from prompts/system/ for reuse.
 * Falls back to classpath-packaged prompts (and finally a built-in baseline)
 * so prompt delivery remains reliable even if ISABELLE_ASSISTANT_HOME is unset.
 */
object PromptLoader {
  @volatile private var cachedSystemPrompt: Option[String] = None
  private val cacheLock = new Object()
  private val defaultSystemPromptFiles = List(
    "00_core_operating_rules.md",
    "01_isabelle_style.md",
    "02_tools.md",
    "03_task_planning.md"
  )
  private val builtInSystemPrompt =
    """You are an Isabelle/HOL proof assistant.
      |
      |Use tools to inspect real proof state before proposing edits.
      |Do not claim success until there are no errors in the processed theory.
      |Return executable Isabelle code when suggesting proof text.""".stripMargin

  /** Resolve ISABELLE_ASSISTANT_HOME, returning None with a warning if unset. */
  private def assistantHome: Option[String] = {
    assistantHomeFrom(
      key => Isabelle_System.getenv(key),
      msg => Output.warning(msg)
    )
  }

  private[assistant] def assistantHomeFrom(
    getenv: String => String,
    warn: String => Unit
  ): Option[String] = {
    val home = getenv("ISABELLE_ASSISTANT_HOME")
    if (home.isEmpty) {
      warn("[Assistant] ISABELLE_ASSISTANT_HOME not set. Install the plugin via 'make install' or set the variable manually.")
      None
    } else Some(home)
  }

  private[assistant] def readClasspathResource(resourcePath: String): Option[String] = {
    val classLoader = Option(getClass.getClassLoader)
      .orElse(Option(Thread.currentThread().getContextClassLoader))
    classLoader.flatMap(cl => Option(cl.getResourceAsStream(resourcePath))).map { in =>
      val src = Source.fromInputStream(in, "UTF-8")
      try src.mkString
      finally src.close()
    }
  }

  private def loadFromHome(home: Option[String], name: String): Option[String] =
    home.flatMap { root =>
      val path = Path.explode(root) + Path.explode("prompts") + Path.explode(name)
      if (path.is_file) Some(File.read(path)) else None
    }

  def load(name: String, substitutions: Map[String, String]): String = {
    val template = loadFromHome(assistantHome, name)
      .orElse(readClasspathResource(s"prompts/$name"))
      .getOrElse(error(
        s"Prompt file not found: prompts/$name (checked ISABELLE_ASSISTANT_HOME and classpath)"
      ))
    renderTemplate(template, substitutions)
  }

  private[assistant] def renderTemplate(templateText: String, substitutions: Map[String, String]): String = {
    val template = Mustache.compiler().compile(templateText)
    template.execute(substitutions.asJava)
  }

  /** Load and cache all system prompts from prompts/system/ directory */
  def getSystemPrompt: String = cacheLock.synchronized {
    cachedSystemPrompt.getOrElse {
      val prompt = loadSystemPromptFromSources(
        assistantHome,
        _.is_dir,
        dir => File.read_dir(dir),
        path => File.read(path),
        readClasspathResource,
        msg => Output.warning(msg)
      )
      cachedSystemPrompt = Some(prompt)
      prompt
    }
  }

  private[assistant] def parseSystemPromptIndex(content: String): List[String] =
    content.linesIterator
      .map(_.trim)
      .filter(line => line.nonEmpty && !line.startsWith("#"))
      .toList

  private[assistant] def loadSystemPromptFromSources(
    home: Option[String],
    isDir: Path => Boolean,
    readDir: Path => List[String],
    readFile: Path => String,
    readResource: String => Option[String],
    warn: String => Unit
  ): String = {
    val fromHome = loadSystemPromptFromHome(home, isDir, readDir, readFile)
    if (fromHome.nonEmpty) fromHome
    else {
      val classpathIndex = readResource("prompts/system/_index.txt")
        .map(parseSystemPromptIndex)
        .filter(_.nonEmpty)
        .getOrElse(defaultSystemPromptFiles)

      val classpathPrompts = classpathIndex
        .flatMap(name => readResource(s"prompts/system/$name"))
        .map(_.trim)
        .filter(_.nonEmpty)

      if (classpathPrompts.nonEmpty) {
        warn("[Assistant] Using classpath fallback for system prompts")
        classpathPrompts.mkString("\n\n")
      } else {
        warn("[Assistant] No system prompt files found; using built-in fallback prompt")
        builtInSystemPrompt
      }
    }
  }

  private[assistant] def loadSystemPromptFromHome(
    home: Option[String],
    isDir: Path => Boolean,
    readDir: Path => List[String],
    readFile: Path => String
  ): String = {
    home match {
      case None => ""
      case Some(root) =>
        val systemDir = Path.explode(root) + Path.explode("prompts") + Path.explode("system")
        if (!isDir(systemDir)) ""
        else {
          val dirEntries = readDir(systemDir)
          val indexPath = systemDir + Path.explode("_index.txt")
          val files =
            if (dirEntries.contains("_index.txt")) {
              val ordered = parseSystemPromptIndex(readFile(indexPath))
                .filter(_.endsWith(".md"))
              val existing = ordered.filter(dirEntries.contains)
              if (existing.nonEmpty) existing
              else dirEntries.filter(_.endsWith(".md")).sorted
            } else dirEntries.filter(_.endsWith(".md")).sorted
          files.map(name => readFile(systemDir + Path.explode(name))).mkString("\n\n")
        }
    }
  }

  /** Clear cached system prompt (for development/testing) */
  def clearCache(): Unit = cacheLock.synchronized { cachedSystemPrompt = None }
}
