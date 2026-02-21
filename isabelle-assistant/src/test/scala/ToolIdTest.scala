/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ToolIdTest extends AnyFunSuite with Matchers {

  test("ToolId wire names should be unique") {
    val wireNames = ToolId.values.map(_.wireName)
    wireNames.distinct shouldBe wireNames
  }

  test("ToolId.fromWire should round-trip all tool IDs") {
    for (toolId <- ToolId.values) {
      ToolId.fromWire(toolId.wireName) shouldBe Some(toolId)
    }
  }

  test("ToolId.displayName should produce non-empty labels") {
    for (toolId <- ToolId.values) {
      ToolId.displayName(toolId) should not be empty
    }
  }
}
