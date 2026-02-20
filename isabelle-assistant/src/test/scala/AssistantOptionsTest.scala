/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for AssistantOptions pure parsing and key resolution helpers.
 */
class AssistantOptionsTest extends AnyFunSuite with Matchers {

  private def parse(
    props: Map[String, String] = Map.empty,
    bools: Map[String, Boolean] = Map.empty
  ): AssistantOptions.SettingsSnapshot =
    AssistantOptions.parseSnapshot(
      (k, d) => props.getOrElse(k, d),
      (k, d) => bools.getOrElse(k, d)
    )

  test("normalizeKey should lowercase and convert hyphens to underscores") {
    AssistantOptions.normalizeKeyForTest("VERIFY-TIMEOUT") shouldBe "verify_timeout"
    AssistantOptions.normalizeKeyForTest("Max_Tokens") shouldBe "max_tokens"
  }

  test("known settings and aliases should resolve") {
    AssistantOptions.hasSettingKey("region") shouldBe true
    AssistantOptions.hasSettingKey("verify-timeout") shouldBe true
    AssistantOptions.hasSettingKey("use_cris") shouldBe true
    AssistantOptions.hasSettingKey("sledgehammer") shouldBe true
    AssistantOptions.hasSettingKey("does_not_exist") shouldBe false
  }

  test("parseSnapshot should sanitize invalid region/model values") {
    val snapshot = parse(Map(
      "assistant.aws.region" -> "!!!",
      "assistant.model.id" -> "bad model id with spaces"
    ))
    snapshot.region shouldBe "us-east-1"
    snapshot.baseModelId shouldBe ""
  }

  test("parseSnapshot should clamp numeric values to configured bounds") {
    val snapshot = parse(Map(
      "assistant.temperature" -> "-1.0",
      "assistant.max.tokens" -> "99999999",
      "assistant.prove.branches" -> "0",
      "assistant.verify.timeout" -> "1"
    ))
    snapshot.temperature shouldBe AssistantConstants.MIN_TEMPERATURE
    snapshot.maxTokens shouldBe AssistantConstants.MAX_MAX_TOKENS
    snapshot.proveBranches shouldBe 1
    snapshot.verifyTimeout shouldBe 5000L
  }

  test("parseSnapshot should fall back to defaults for non-numeric values") {
    val snapshot = parse(Map(
      "assistant.temperature" -> "not-a-number",
      "assistant.max.tokens" -> "nan",
      "assistant.prove.timeout" -> "oops"
    ))
    snapshot.temperature shouldBe AssistantConstants.DEFAULT_TEMPERATURE
    snapshot.maxTokens shouldBe AssistantConstants.DEFAULT_MAX_TOKENS
    snapshot.proveTimeout shouldBe AssistantConstants.DEFAULT_PROVE_TIMEOUT
  }

  test("parseSnapshot should honor boolean flags and defaults") {
    val defaults = parse()
    defaults.useCris shouldBe true
    defaults.verifySuggestions shouldBe true
    defaults.useSledgehammer shouldBe false

    val overridden = parse(
      bools = Map(
        "assistant.use.cris" -> false,
        "assistant.verify.suggestions" -> false,
        "assistant.use.sledgehammer" -> true
      )
    )
    overridden.useCris shouldBe false
    overridden.verifySuggestions shouldBe false
    overridden.useSledgehammer shouldBe true
  }

  test("parseSnapshot should default maxToolIterations to configured default") {
    val defaults = parse()
    defaults.maxToolIterations shouldBe Some(AssistantConstants.DEFAULT_MAX_TOOL_ITERATIONS)
  }

  test("parseSnapshot should parse valid maxToolIterations values") {
    val withLimit = parse(Map("assistant.max.tool.iterations" -> "25"))
    withLimit.maxToolIterations shouldBe Some(25)
  }

  test("parseSnapshot should treat empty/0/none/unlimited as unlimited") {
    parse(Map("assistant.max.tool.iterations" -> "")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "0")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "none")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "unlimited")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "UNLIMITED")).maxToolIterations shouldBe None
  }

  test("parseSnapshot should clamp maxToolIterations to valid range") {
    parse(Map("assistant.max.tool.iterations" -> "100")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "-5")).maxToolIterations shouldBe None
  }
}
