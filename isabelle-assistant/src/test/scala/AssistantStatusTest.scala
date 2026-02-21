/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class AssistantStatusTest extends AnyFunSuite with Matchers {

  test("fromText should preserve non-empty status text") {
    AssistantStatus.fromText("Thinking...").text shouldBe "Thinking..."
  }

  test("fromText should trim surrounding whitespace") {
    AssistantStatus.fromText("  Working  ").text shouldBe "Working"
  }

  test("fromText should normalize blank input to ready status") {
    AssistantStatus.fromText("   ").text shouldBe AssistantConstants.STATUS_READY
    AssistantStatus.fromText(null).text shouldBe AssistantConstants.STATUS_READY
  }
}
