/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import com.samskivert.mustache.Mustache
import scala.jdk.CollectionConverters._

/**
 * Loads Mustache prompt templates from the prompts/ directory.
 * Caches auto-discovered system prompts from prompts/system/ for reuse.
 */
object PromptLoader {
  @volatile private var cachedSystemPrompt: Option[String] = None
  private val cacheLock = new Object()

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

  def load(name: String, substitutions: Map[String, String]): String = {
    val home = assistantHome.getOrElse(
      error("ISABELLE_ASSISTANT_HOME not set — install the plugin via 'make install' or add init_component to settings"))

    val path = Path.explode(home) + Path.explode("prompts") + Path.explode(name)
    if (!path.is_file)
      error("Prompt file not found: " + path)

    renderTemplate(File.read(path), substitutions)
  }

  private[assistant] def renderTemplate(templateText: String, substitutions: Map[String, String]): String = {
    val template = Mustache.compiler().compile(templateText)
    template.execute(substitutions.asJava)
  }

  /** Load and cache all system prompts from prompts/system/ directory */
  def getSystemPrompt: String = cacheLock.synchronized {
    cachedSystemPrompt.getOrElse {
      val prompt = loadSystemPromptFromHome(
        assistantHome,
        _.is_dir,
        dir => File.read_dir(dir),
        path => File.read(path)
      )
      cachedSystemPrompt = Some(prompt)
      prompt
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
          val files = readDir(systemDir).filter(_.endsWith(".md")).sorted
          files.map(name => readFile(systemDir + Path.explode(name))).mkString("\n\n")
        }
    }
  }

  /** Clear cached system prompt (for development/testing) */
  def clearCache(): Unit = cacheLock.synchronized { cachedSystemPrompt = None }
}
