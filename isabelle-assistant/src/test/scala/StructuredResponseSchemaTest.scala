/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import software.amazon.awssdk.thirdparty.jackson.core.JsonFactory

/**
 * Tests for the JSON schemas used with Anthropic's forced tool_choice to
 * guarantee parseable structured responses.
 *
 * The bodies of these schemas are string-templated JSON; we round-trip
 * them through a parser to confirm they're well-formed, and we make a
 * couple of cross-schema assertions (e.g. brainstorm and select agree on
 * the shape of an approach).
 */
class StructuredResponseSchemaTest extends AnyFunSuite with Matchers {

  private val jsonFactory = new JsonFactory()

  test("PlanningBrainstorm schema should be well-formed JSON") {
    noException should be thrownBy {
      val parser = jsonFactory.createParser(
        StructuredResponseSchema.PlanningBrainstorm.jsonSchema
      )
      try {
        while (parser.nextToken() != null) ()
      } finally parser.close()
    }
  }

  test("PlanningSelect schema should be well-formed JSON") {
    noException should be thrownBy {
      val parser = jsonFactory.createParser(
        StructuredResponseSchema.PlanningSelect.jsonSchema
      )
      try {
        while (parser.nextToken() != null) ()
      } finally parser.close()
    }
  }

  test("ContextSummary schema should be well-formed JSON") {
    noException should be thrownBy {
      val parser = jsonFactory.createParser(
        StructuredResponseSchema.ContextSummary.jsonSchema
      )
      try {
        while (parser.nextToken() != null) ()
      } finally parser.close()
    }
  }

  test("PlanningBrainstorm schema should declare the configured number of approaches") {
    val schema = StructuredResponseSchema.PlanningBrainstorm.jsonSchema
    val n = AssistantConstants.PLANNING_NUM_APPROACHES
    schema should include(s""""minItems": $n""")
    schema should include(s""""maxItems": $n""")
  }

  test("PlanningBrainstorm description should reference the configured number") {
    val n = AssistantConstants.PLANNING_NUM_APPROACHES
    StructuredResponseSchema.PlanningBrainstorm.description should include(n.toString)
  }

  test("PlanningBrainstorm approaches must require id, title, summary, key_idea, exploration_hints") {
    val schema = StructuredResponseSchema.PlanningBrainstorm.jsonSchema
    // All five fields must appear in the `required` array of the approach item.
    schema should include(""""id"""")
    schema should include(""""title"""")
    schema should include(""""summary"""")
    schema should include(""""key_idea"""")
    schema should include(""""exploration_hints"""")
  }

  test("PlanningSelect must require selected_approach, reasoning, plan") {
    val schema = StructuredResponseSchema.PlanningSelect.jsonSchema
    schema should include(""""selected_approach"""")
    schema should include(""""reasoning"""")
    schema should include(""""plan"""")
  }

  test("schemas should have non-empty names and descriptions") {
    for (s <- List(
           StructuredResponseSchema.PlanningBrainstorm,
           StructuredResponseSchema.PlanningSelect,
           StructuredResponseSchema.ContextSummary
         )) {
      s.name should not be empty
      s.description should not be empty
    }
  }

  test("schema names should match across the three planning-related schemas") {
    StructuredResponseSchema.PlanningBrainstorm.name shouldBe "brainstorm_approaches"
    StructuredResponseSchema.PlanningSelect.name shouldBe "select_best_plan"
    StructuredResponseSchema.ContextSummary.name shouldBe "summarize_context"
  }
}
