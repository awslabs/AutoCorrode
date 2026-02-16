/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import isabelle.assistant.IQIntegration.VerificationResult
import isabelle.assistant.IQIntegration.VerificationResult._
import isabelle.assistant.IQIntegration.IQStatus
import isabelle.assistant.IQIntegration.IQStatus._

/**
 * Tests for IQIntegration — proof verification, sledgehammer, find_theorems.
 * 
 * Note: These tests verify the logic and structure without requiring actual
 * I/Q plugin runtime. Mock-based tests would require complex jEdit/PIDE mocking,
 * which is out of scope. Integration tests that require actual I/Q are in
 * AssistantIntegrationTest.
 */
class IQIntegrationTest extends AnyFunSuite with Matchers {

  test("VerificationResult enum should have all expected cases") {
    // Verify all cases exist and are distinct types
    val success: VerificationResult = ProofSuccess(100)
    val failure: VerificationResult = ProofFailure("error")
    val timeout: VerificationResult = ProofTimeout
    val unavailable: VerificationResult = IQUnavailable
    val missingImport: VerificationResult = MissingImport("suggestion")
    
    success should not be failure
    failure should not be timeout
    timeout should not be unavailable
    unavailable should not be missingImport
  }

  test("ProofSuccess should store timing information") {
    val result = ProofSuccess(150, "state text")
    result match {
      case ProofSuccess(timeMs, resultState) =>
        timeMs shouldBe 150
        resultState shouldBe "state text"
      case _ => fail("Should be ProofSuccess")
    }
  }

  test("ProofFailure should store error message") {
    val result = ProofFailure("syntax error")
    result match {
      case ProofFailure(error) => error shouldBe "syntax error"
      case _ => fail("Should be ProofFailure")
    }
  }

  test("SledgehammerResult should store method and timing") {
    val result = IQIntegration.SledgehammerResult("by (metis foo)", 500)
    result.proofMethod shouldBe "by (metis foo)"
    result.timeMs shouldBe 500
  }

  test("ProofStepResult should track completion status") {
    val complete = IQIntegration.ProofStepResult(
      complete = true, 
      numSubgoals = 0, 
      stateText = "No subgoals", 
      timeMs = 200
    )
    complete.complete shouldBe true
    complete.numSubgoals shouldBe 0
    
    val incomplete = IQIntegration.ProofStepResult(
      complete = false, 
      numSubgoals = 3, 
      stateText = "3 subgoals", 
      timeMs = 150
    )
    incomplete.complete shouldBe false
    incomplete.numSubgoals shouldBe 3
  }

  test("getIsarExploreImportSuggestion should provide helpful guidance") {
    val suggestion = IQIntegration.getIsarExploreImportSuggestion
    suggestion should include("Isar_Explore")
    suggestion should include("import")
    suggestion should include("$IQ_HOME")
  }

  test("IQStatus enum should have connected and disconnected states") {
    val connected: IQStatus = IQConnected
    val disconnected: IQStatus = IQDisconnected
    
    connected should not be disconnected
  }

  test("parseStepResult should parse PROOF_COMPLETE header") {
    val result = IQIntegration.parseStepResult(
      "PROOF_COMPLETE\nNo subgoals",
      timeMs = 123L
    )
    result.complete shouldBe true
    result.numSubgoals shouldBe 0
    result.stateText shouldBe "No subgoals"
    result.timeMs shouldBe 123L
  }

  test("parseStepResult should parse PROOF_STATE header with subgoal count") {
    val result = IQIntegration.parseStepResult(
      "PROOF_STATE 3\n1. P\n2. Q\n3. R",
      timeMs = 88L
    )
    result.complete shouldBe false
    result.numSubgoals shouldBe 3
    result.stateText shouldBe "1. P\n2. Q\n3. R"
    result.timeMs shouldBe 88L
  }

  test("parseStepResult should return opaque legacy result without PROOF_* header") {
    val text = "goal (1 subgoal):\n 1. P ⟹ Q"
    val result = IQIntegration.parseStepResult(text, timeMs = 42L)
    result.complete shouldBe false
    result.numSubgoals shouldBe -1
    result.stateText shouldBe text
    result.timeMs shouldBe 42L
  }

  test("parseStepResult should handle malformed PROOF_STATE header") {
    val result = IQIntegration.parseStepResult(
      "PROOF_STATE abc\nstate",
      timeMs = 17L
    )
    result.complete shouldBe false
    result.numSubgoals shouldBe -1
    result.stateText shouldBe "state"
  }

  test("parseStepResult should treat empty output as completed proof") {
    val result = IQIntegration.parseStepResult("", timeMs = 9L)
    result.complete shouldBe true
    result.numSubgoals shouldBe 0
    result.stateText shouldBe ""
  }
}
