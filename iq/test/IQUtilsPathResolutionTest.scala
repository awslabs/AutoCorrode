/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

object IQUtilsPathResolutionTest extends App {

  private def assertEqual[A](actual: A, expected: A, context: String): Unit = {
    if (actual != expected) {
      throw new RuntimeException(
        s"$context failed.\nExpected: $expected\nActual:   $actual"
      )
    }
  }

  private def assertLeftContains(actual: Either[String, String], expectedSubstring: String, context: String): Unit = {
    actual match {
      case Left(msg) =>
        if (!msg.contains(expectedSubstring)) {
          throw new RuntimeException(
            s"$context failed.\nExpected Left containing: $expectedSubstring\nActual Left:              $msg"
          )
        }
      case Right(value) =>
        throw new RuntimeException(s"$context failed.\nExpected Left but got Right($value)")
    }
  }

  // stripExtension should remove only the final extension segment.
  assertEqual(
    IQUtils.stripExtension("/tmp/project/Foo.Bar.thy"),
    "/tmp/project/Foo.Bar",
    "stripExtension multi-dot"
  )
  assertEqual(
    IQUtils.stripExtension("/tmp/project/Foo"),
    "/tmp/project/Foo",
    "stripExtension no extension"
  )

  // Multi-dot partial path should resolve correctly when there is one candidate.
  val uniqueCandidates = List(
    "/tmp/project/Foo.Bar.thy",
    "/tmp/project/Other.thy"
  )
  assertEqual(
    IQUtils.autoCompleteFilePathFromCandidates("Foo.Bar.thy", uniqueCandidates),
    Right("/tmp/project/Foo.Bar.thy"),
    "unique multi-dot resolution"
  )

  // Prevent false matches: Foo.Baz should not match only Foo.Bar.
  assertLeftContains(
    IQUtils.autoCompleteFilePathFromCandidates("Foo.Baz.thy", List("/tmp/project/Foo.Bar.thy")),
    "No file found matching 'Foo.Baz.thy'",
    "false match prevention"
  )

  // Ambiguities should include all candidates deterministically.
  val ambiguous = IQUtils.autoCompleteFilePathFromCandidates(
    "Foo.Bar.thy",
    List("/tmp/b/Foo.Bar.thy", "/tmp/a/Foo.Bar.thy")
  )
  assertEqual(
    ambiguous,
    Left("Multiple files found matching 'Foo.Bar.thy': /tmp/a/Foo.Bar.thy, /tmp/b/Foo.Bar.thy"),
    "deterministic ambiguity reporting"
  )

  // trackedOnly = false should return the input path if no tracked match exists.
  assertEqual(
    IQUtils.autoCompleteFilePathFromCandidates("Untracked/Thing.thy", Nil, trackedOnly = false),
    Right("Untracked/Thing.thy"),
    "untracked fallback when trackedOnly=false"
  )

  println("IQUtilsPathResolutionTest: all tests passed")
}
