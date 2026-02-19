/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Shared HTML utility methods to prevent duplication. */
object HtmlUtil {

  /** Escape &, <, > in a string for safe HTML embedding. */
  def escapeHtml(s: String): String =
    s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
}
