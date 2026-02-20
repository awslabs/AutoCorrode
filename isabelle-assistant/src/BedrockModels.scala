/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import software.amazon.awssdk.services.bedrock.BedrockClient
import software.amazon.awssdk.services.bedrock.model.{ListFoundationModelsRequest, ListInferenceProfilesRequest, ModelModality}
import software.amazon.awssdk.regions.Region
import scala.jdk.CollectionConverters._
import java.nio.file.{Files, Path, Paths}

/** Lists and refreshes available Bedrock Anthropic models, with local file caching and CRIS prefix support. */
object BedrockModels {
  private val cacheFile: Path =
    Paths.get(System.getProperty("user.home"), ".isabelle", "assistant_models.txt")

  private val crisProviders = Set("anthropic")
  private val modelIdPattern = "^[a-zA-Z0-9._:/-]+$"
  private val anthropicModelPattern = "^(?:(?:us|eu|ap|global)\\.)?anthropic\\..+$"

  def isAnthropicModelId(modelId: String): Boolean = {
    val trimmed = modelId.trim
    trimmed.nonEmpty &&
    trimmed.matches(modelIdPattern) &&
    trimmed.toLowerCase.matches(anthropicModelPattern)
  }

  private[assistant] def filterAnthropicModels(modelIds: Iterable[String]): Array[String] = {
    modelIds.iterator.map(_.trim).filter(isAnthropicModelId).toSet.toArray.sorted
  }

  def getModels: Array[String] = {
    if (Files.exists(cacheFile)) {
      val cached = Files.readAllLines(cacheFile).asScala.toList
      val filtered = filterAnthropicModels(cached)
      if (filtered.length != cached.length)
        Output.warning(
          s"[Assistant] Filtered out ${cached.length - filtered.length} non-Anthropic cached model(s)"
        )
      filtered
    } else {
      Array.empty
    }
  }

  def refreshModels(region: String): Array[String] = {
    Output.writeln(s"[Assistant] Refreshing models from region: $region")
    
    val client = BedrockClient.builder()
      .region(Region.of(region))
      .build()
    // Don't register with ErrorHandler - we manage this client's lifecycle locally (closed in finally)
    try {
      // Get foundation models (text output only)
      val foundationResponse = client.listFoundationModels(
        ListFoundationModelsRequest.builder()
          .byInferenceType("ON_DEMAND")
          .byOutputModality(ModelModality.TEXT)
          .build()
      )
      val foundationModels = foundationResponse.modelSummaries().asScala
        .map(_.modelId())
        .toList
      Output.writeln(s"[Assistant] Found ${foundationModels.size} foundation models")

      // Get inference profiles (includes newer models like Claude 3.5 Sonnet v2, Claude 4, etc.)
      // Filter out image/embedding models by name
      val imageModelPatterns = Set("stable-diffusion", "titan-image", "titan-embed", "nova-canvas", "nova-reel")
      val profileResponse = client.listInferenceProfiles(
        ListInferenceProfilesRequest.builder().build()
      )
      val profileModels = profileResponse.inferenceProfileSummaries().asScala
        .map(_.inferenceProfileId())
        .filterNot(id => imageModelPatterns.exists(p => id.toLowerCase.contains(p)))
        .toList
      Output.writeln(s"[Assistant] Found ${profileModels.size} inference profiles")

      // Keep Anthropic-only model identifiers, then deduplicate and sort.
      val allModels = filterAnthropicModels(foundationModels ++ profileModels)
      Output.writeln(s"[Assistant] Total Anthropic models/profiles: ${allModels.length}")

      // Write cache
      Files.createDirectories(cacheFile.getParent)
      Files.write(cacheFile, allModels.toSeq.asJava)
      Output.writeln(s"[Assistant] Models cached to: $cacheFile")

      allModels
    } catch {
      case ex: Exception =>
        Output.writeln(s"[Assistant] Error refreshing models: ${ex.getMessage}")
        throw ex
    } finally {
      client.close()
    }
  }

  def applyCrisPrefix(modelId: String, region: String): String = {
    // Don't add prefix if it already has one (e.g., us.anthropic.*, eu.anthropic.*, ap.anthropic.*, global.anthropic.*)
    if (modelId.startsWith("us.") || modelId.startsWith("eu.") || modelId.startsWith("ap.") || modelId.startsWith("global.")) {
      modelId
    } else {
      val provider = modelId.split("\\.").headOption.getOrElse("")
      if (crisProviders.contains(provider)) {
        val prefix = if (region.startsWith("eu-")) "eu"
          else if (region.startsWith("ap-")) "ap"
          else "us"
        s"$prefix.$modelId"
      } else {
        modelId
      }
    }
  }
}
