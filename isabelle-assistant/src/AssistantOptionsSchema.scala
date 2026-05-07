/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Pure data + parsing for AssistantOptions.
  *
  * This module owns three things that used to live inside the
  * AssistantOptions companion object:
  *
  *   - SettingsSnapshot — the immutable record of a parsed settings view
  *   - parseSnapshot    — read properties into a snapshot with clamping
  *   - region / model-id validation helpers
  *
  * The extraction keeps AssistantOptions.scala focused on the Swing option
  * pane (the `class`) and the typed accessor facade (the `object`), while
  * this file captures the schema in a place that is easy to test in
  * isolation and that doesn't depend on jEdit at all.
  */
object AssistantOptionsSchema {

  val REGIONS: Array[String] = Array(
    "us-east-1",
    "us-east-2",
    "us-west-1",
    "us-west-2",
    "eu-west-1",
    "eu-west-2",
    "eu-west-3",
    "eu-central-1",
    "eu-north-1",
    "ap-southeast-1",
    "ap-southeast-2",
    "ap-northeast-1",
    "ap-northeast-2",
    "ap-south-1",
    "ca-central-1",
    "sa-east-1"
  )

  private val modelIdPattern = "^[a-zA-Z0-9._:/-]*$"
  private val regionPattern = "^[a-z]{2}(?:-[a-z]+)+-\\d+$"

  def isValidBaseModelId(modelId: String): Boolean =
    modelId.matches(modelIdPattern) &&
      (modelId.isEmpty || BedrockModels.isAnthropicModelId(modelId))

  def isValidRegion(region: String): Boolean =
    region.matches(regionPattern)

  /** All parsed settings in a single immutable snapshot, cached atomically.
    * Boolean settings are included here (not read from jEdit directly) to
    * ensure a consistent view across all settings.
    */
  case class SettingsSnapshot(
      region: String,
      baseModelId: String,
      maxTokens: Int,
      maxContextTokens: Int,
      maxToolIterations: Option[Int],
      maxRetries: Int,
      verifyTimeout: Long,
      sledgehammerTimeout: Long,
      quickcheckTimeout: Long,
      nitpickTimeout: Long,
      maxVerifyCandidates: Int,
      findTheoremsLimit: Int,
      findTheoremsTimeout: Long,
      traceTimeout: Int,
      traceDepth: Int,
      useCris: Boolean,
      verifySuggestions: Boolean,
      useSledgehammer: Boolean,
      planningBaseModelId: String,
      summarizationBaseModelId: String,
      autoSummarize: Boolean,
      summarizationThreshold: Double
  )

  /** Parse a snapshot given readers for string and boolean properties. Used
    * both from AssistantOptions (production, via jEdit) and from tests (with
    * an in-memory map).
    */
  def parseSnapshot(
      prop: (String, String) => String,
      boolProp: (String, Boolean) => Boolean
  ): SettingsSnapshot = {
    def intProp(key: String, default: Int, min: Int, max: Int): Int =
      try { math.max(min, math.min(max, prop(key, default.toString).toInt)) }
      catch { case _: NumberFormatException => default }
    def longProp(key: String, default: Long, min: Long, max: Long): Long =
      try { math.max(min, math.min(max, prop(key, default.toString).toLong)) }
      catch { case _: NumberFormatException => default }
    def doubleProp(
        key: String,
        default: Double,
        min: Double,
        max: Double
    ): Double =
      try { math.max(min, math.min(max, prop(key, default.toString).toDouble)) }
      catch { case _: NumberFormatException => default }
    def optIntProp(
        key: String,
        min: Int,
        max: Int,
        default: Option[Int]
    ): Option[Int] = {
      val defaultText = default.map(_.toString).getOrElse("")
      val value = prop(key, defaultText).trim.toLowerCase
      if (
        value.isEmpty || value == "0" || value == "none" || value == "unlimited"
      ) None
      else
        try {
          val n = value.toInt
          if (n >= min && n <= max) Some(n) else None
        } catch { case _: NumberFormatException => None }
    }

    val region = prop("assistant.aws.region", "us-east-1")
    val modelId = prop("assistant.model.id", "")
    val planningModelId = prop("assistant.planning.model.id", "")
    val summarizationModelId = prop("assistant.summarization.model.id", "")

    SettingsSnapshot(
      region =
        if (isValidRegion(region)) region
        else "us-east-1",
      baseModelId = if (isValidBaseModelId(modelId)) modelId else "",
      maxTokens = intProp(
        "assistant.max.tokens",
        AssistantConstants.DEFAULT_MAX_TOKENS,
        AssistantConstants.MIN_MAX_TOKENS,
        Int.MaxValue
      ),
      maxContextTokens = intProp(
        "assistant.max.context.tokens",
        AssistantConstants.DEFAULT_MAX_CONTEXT_TOKENS,
        AssistantConstants.MIN_MAX_CONTEXT_TOKENS,
        Int.MaxValue
      ),
      maxToolIterations =
        optIntProp(
          "assistant.max.tool.iterations",
          1,
          50,
          Some(AssistantConstants.DEFAULT_MAX_TOOL_ITERATIONS)
        ),
      maxRetries = intProp(
        "assistant.verify.max.retries",
        AssistantConstants.DEFAULT_MAX_VERIFICATION_RETRIES,
        1,
        10
      ),
      verifyTimeout = longProp(
        "assistant.verify.timeout",
        AssistantConstants.DEFAULT_VERIFICATION_TIMEOUT,
        5000L,
        300000L
      ),
      sledgehammerTimeout = longProp(
        "assistant.sledgehammer.timeout",
        AssistantConstants.DEFAULT_SLEDGEHAMMER_TIMEOUT,
        1000L,
        300000L
      ),
      quickcheckTimeout = longProp(
        "assistant.quickcheck.timeout",
        AssistantConstants.DEFAULT_QUICKCHECK_TIMEOUT,
        1000L,
        300000L
      ),
      nitpickTimeout = longProp(
        "assistant.nitpick.timeout",
        AssistantConstants.DEFAULT_NITPICK_TIMEOUT,
        1000L,
        300000L
      ),
      maxVerifyCandidates = intProp(
        "assistant.max.verify.candidates",
        AssistantConstants.DEFAULT_MAX_VERIFY_CANDIDATES,
        1,
        20
      ),
      findTheoremsLimit = intProp(
        "assistant.find.theorems.limit",
        AssistantConstants.DEFAULT_FIND_THEOREMS_LIMIT,
        1,
        100
      ),
      findTheoremsTimeout = longProp(
        "assistant.find.theorems.timeout",
        AssistantConstants.DEFAULT_FIND_THEOREMS_TIMEOUT,
        1000L,
        300000L
      ),
      traceTimeout = intProp(
        "assistant.trace.timeout",
        AssistantConstants.DEFAULT_TRACE_TIMEOUT,
        1,
        300
      ),
      traceDepth = intProp(
        "assistant.trace.depth",
        AssistantConstants.DEFAULT_TRACE_DEPTH,
        1,
        50
      ),
      useCris = boolProp("assistant.use.cris", true),
      verifySuggestions = boolProp("assistant.verify.suggestions", true),
      useSledgehammer = boolProp("assistant.use.sledgehammer", false),
      planningBaseModelId = if (isValidBaseModelId(planningModelId)) planningModelId else "",
      summarizationBaseModelId = if (isValidBaseModelId(summarizationModelId)) summarizationModelId else "",
      autoSummarize = boolProp("assistant.auto.summarize", true),
      summarizationThreshold = doubleProp(
        "assistant.summarization.threshold",
        AssistantConstants.DEFAULT_SUMMARIZATION_THRESHOLD,
        AssistantConstants.MIN_SUMMARIZATION_THRESHOLD,
        AssistantConstants.MAX_SUMMARIZATION_THRESHOLD
      )
    )
  }
}
