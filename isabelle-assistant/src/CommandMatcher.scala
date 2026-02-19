// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

package isabelle.assistant

object CommandMatcher {

  /** Safely checks if a string starts with a specific keyword, respecting token
    * boundaries.
    */
  def startsWithKeyword(text: String, keyword: String): Boolean = {
    val t = text.trim
    t == keyword ||
    t.startsWith(keyword + " ") ||
    t.startsWith(keyword + "(") ||
    t.startsWith(keyword + "\"") ||
    t.startsWith(keyword + "\t") ||
    t.startsWith(keyword + "\n")
  }

  /** Finds the first keyword from a set that the text starts with. */
  def findMatchingKeyword(
      text: String,
      keywords: Set[String]
  ): Option[String] = {
    keywords.find(kw => startsWithKeyword(text, kw))
  }
}
