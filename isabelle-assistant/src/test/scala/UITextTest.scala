/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Contracts for the `AssistantConstants.UIText` canonical phrases. The
  * purpose is to guard against future drift: if someone reverts one
  * constant to the old "No X at cursor position." wording, or removes the
  * terminating period, this suite fails loudly rather than letting the
  * phrasing bifurcate across call sites again.
  */
class UITextTest extends AnyFunSuite with Matchers {

  import AssistantConstants.UIText._

  private val cursorPhrases = List(
    "NO_COMMAND_AT_CURSOR"     -> NO_COMMAND_AT_CURSOR,
    "NO_GOAL_AT_CURSOR"        -> NO_GOAL_AT_CURSOR,
    "NO_ERROR_AT_CURSOR"       -> NO_ERROR_AT_CURSOR,
    "NO_DEFINITION_AT_CURSOR"  -> NO_DEFINITION_AT_CURSOR,
    "NO_PROOF_BLOCK_AT_CURSOR" -> NO_PROOF_BLOCK_AT_CURSOR,
    "NO_TYPE_AT_CURSOR"        -> NO_TYPE_AT_CURSOR,
    "NO_PROOF_PATTERN"         -> NO_PROOF_PATTERN
  )

  test("every cursor phrase ends with a period") {
    for ((name, phrase) <- cursorPhrases)
      withClue(s"$name = '$phrase': ") {
        phrase should endWith(".")
      }
  }

  test("every cursor phrase ends with the word 'cursor.' — no 'position', no 'found at'") {
    for ((name, phrase) <- cursorPhrases)
      withClue(s"$name = '$phrase': ") {
        phrase should endWith("cursor.")
        phrase should not include "cursor position"
        phrase should not include "found at"
      }
  }

  test("NO_SUGGESTIONS has its own canonical phrasing") {
    NO_SUGGESTIONS shouldBe "No suggestions found."
  }

  test("phrases do not contain three-dot ellipses") {
    val all = cursorPhrases.map(_._2) :+ NO_SUGGESTIONS
    for (phrase <- all)
      withClue(s"'$phrase': ") {
        phrase should not include "..."
      }
  }

  test("TOOL_IQ_UNAVAILABLE is the canonical I/Q-missing tool error") {
    // Pinning the exact string matters: the LLM must see byte-for-byte the
    // same message from every tool handler that depends on the I/Q
    // backplane, otherwise it can't reliably classify this failure class.
    AssistantConstants.TOOL_IQ_UNAVAILABLE shouldBe "I/Q plugin not available."
  }
}
