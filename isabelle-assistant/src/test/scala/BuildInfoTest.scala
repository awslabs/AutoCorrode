/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Verifies that `BuildInfo` returns non-empty identity strings regardless
  * of whether `plugin.props` is on the classpath. Unit tests run without
  * the packaged JAR, so the fallback ("Isabelle Assistant dev") is
  * exercised here. If the classpath includes the packaged resource (e.g.,
  * running in-process inside jEdit), the actual plugin.props values are
  * returned instead — both paths must yield non-empty strings.
  */
class BuildInfoTest extends AnyFunSuite with Matchers {

  test("name returns a non-empty string") {
    BuildInfo.name should not be empty
  }

  test("version returns a non-empty string") {
    BuildInfo.version should not be empty
  }

  test("identity concatenates name and version with a space") {
    BuildInfo.identity shouldBe s"${BuildInfo.name} ${BuildInfo.version}"
  }
}
