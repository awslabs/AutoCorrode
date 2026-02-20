/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import software.amazon.awssdk.services.bedrock.BedrockClient
import software.amazon.awssdk.services.bedrock.model.{ListFoundationModelsRequest, ListInferenceProfilesRequest, ModelModality}
import software.amazon.awssdk.regions.Region
import scala.jdk.CollectionConverters._
import java.nio.file.{Files, Path, Paths}

/** Lists and refreshes available Bedrock models, with local file caching and CRIS prefix support. */
object BedrockModels {
  private val cacheFile: Path =
    Paths.get(System.getProperty("user.home"), ".isabelle", "assistant_models.txt")

  private val crisProviders = Set("anthropic", "meta", "mistral")

  def getModels: Array[String] = {
    if (Files.exists(cacheFile)) {
      Files.readAllLines(cacheFile).asScala.toArray
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

      // Combine, deduplicate, and sort text-capable model identifiers.
      val allModels = (foundationModels ++ profileModels)
        .distinct.sorted.toArray
      Output.writeln(s"[Assistant] Total text models/profiles: ${allModels.length}")

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
