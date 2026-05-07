/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Plugin identity — name and version — read from the packaged
  * `plugin.props` resource. This is the source of truth for the `:version`
  * chat command and for surfaces that want to display the plugin's
  * version (e.g., future "About" dialog).
  *
  * Lookup is resilient: if `plugin.props` is not on the classpath (notably
  * during unit tests, which run without the packaged JAR), the accessors
  * fall back to sensible defaults so tests and ad-hoc runs don't fail.
  */
object BuildInfo {
  private val NameKey    = "plugin.isabelle.assistant.AssistantPlugin.name"
  private val VersionKey = "plugin.isabelle.assistant.AssistantPlugin.version"

  private lazy val props: java.util.Properties = {
    val p = new java.util.Properties()
    val stream = getClass.getClassLoader.getResourceAsStream("plugin.props")
    if (stream != null) {
      try p.load(stream)
      catch { case _: Throwable => () }
      finally stream.close()
    }
    p
  }

  /** Plugin display name. Defaults to "Isabelle Assistant" when
    * `plugin.props` is not on the classpath. */
  def name: String =
    Option(props.getProperty(NameKey)).filter(_.nonEmpty).getOrElse("Isabelle Assistant")

  /** Plugin version string. Defaults to "dev" when `plugin.props` is not
    * on the classpath. */
  def version: String =
    Option(props.getProperty(VersionKey)).filter(_.nonEmpty).getOrElse("dev")

  /** Formatted short identity: "Isabelle Assistant 0.1". */
  def identity: String = s"$name $version"
}
