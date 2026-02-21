/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

object IQUISettingsTest {
  private def assertThat(condition: Boolean, message: String): Unit = {
    if (!condition) throw new RuntimeException(message)
  }

  private def testDefaults(): Unit = {
    val settings = IQUISettings.parseForTest(
      (k, d) => d,
      (_, d) => d
    )
    assertThat(
      settings.maxLogLines == IQUISettings.DefaultMaxLogLines,
      s"default maxLogLines mismatch: ${settings.maxLogLines}"
    )
    assertThat(
      settings.maxExploreMessages == IQUISettings.DefaultMaxExploreMessages,
      s"default maxExploreMessages mismatch: ${settings.maxExploreMessages}"
    )
    assertThat(settings.autoScrollLogs, "default autoScrollLogs should be true")
    assertThat(settings.autoFillDefaults, "default autoFillDefaults should be true")
    assertThat(
      !settings.exploreDebugLogging,
      "default exploreDebugLogging should be false"
    )
  }

  private def testClampingAndBooleans(): Unit = {
    val settings = IQUISettings.parseForTest(
      (k, d) =>
        k match {
          case IQUISettings.MaxLogLinesKey        => "999999999"
          case IQUISettings.MaxExploreMessagesKey => "-1"
          case _                                  => d
        },
      (k, d) =>
        k match {
          case IQUISettings.AutoScrollLogsKey      => false
          case IQUISettings.AutoFillDefaultsKey    => false
          case IQUISettings.ExploreDebugLoggingKey => true
          case _                                   => d
        }
    )

    assertThat(
      settings.maxLogLines == 100000,
      s"maxLogLines should clamp to upper bound: ${settings.maxLogLines}"
    )
    assertThat(
      settings.maxExploreMessages == 100,
      s"maxExploreMessages should clamp to lower bound: ${settings.maxExploreMessages}"
    )
    assertThat(!settings.autoScrollLogs, "autoScrollLogs should be false")
    assertThat(!settings.autoFillDefaults, "autoFillDefaults should be false")
    assertThat(settings.exploreDebugLogging, "exploreDebugLogging should be true")
  }

  def main(args: Array[String]): Unit = {
    testDefaults()
    testClampingAndBooleans()
    println("IQUISettingsTest: all tests passed")
  }
}
