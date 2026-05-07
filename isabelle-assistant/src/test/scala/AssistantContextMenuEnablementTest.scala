/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Pins the menu-enablement decisions of the Isabelle Assistant context
  * menu. Exercises pure booleans so we can assert each branch without
  * standing up a Swing JEditTextArea. */
class AssistantContextMenuEnablementTest extends AnyFunSuite with Matchers {

  import AssistantContextMenuEnablement._

  private def ctx(
    inProof: Boolean = false,
    hasGoal: Boolean = false,
    onError: Boolean = false,
    onWarning: Boolean = false,
    hasSelection: Boolean = false,
    hasCommand: Boolean = false,
    hasTypeInfo: Boolean = false,
    hasApplyProof: Boolean = false,
    onDefinition: Boolean = false,
    iqAvailable: Boolean = false
  ): MenuContext.Context =
    MenuContext.Context(
      inProof = inProof,
      hasGoal = hasGoal,
      onError = onError,
      onWarning = onWarning,
      hasSelection = hasSelection,
      hasCommand = hasCommand,
      hasTypeInfo = hasTypeInfo,
      hasApplyProof = hasApplyProof,
      onDefinition = onDefinition,
      iqAvailable = iqAvailable
    )

  // === Understanding ===

  test("Explain shows when a command or a selection is present") {
    showExplain(ctx(hasCommand = true)) shouldBe true
    showExplain(ctx(hasSelection = true)) shouldBe true
    showExplain(ctx(hasCommand = true, hasSelection = true)) shouldBe true
    showExplain(ctx()) shouldBe false
  }

  test("Explain Error follows onError") {
    showExplainError(ctx(onError = true)) shouldBe true
    showExplainError(ctx()) shouldBe false
  }

  test("Show Type follows hasTypeInfo") {
    showShowType(ctx(hasTypeInfo = true)) shouldBe true
    showShowType(ctx()) shouldBe false
  }

  // === Proof ===

  test("Proof submenu only shows inside a proof context") {
    showProofSubmenu(ctx(inProof = true)) shouldBe true
    showProofSubmenu(ctx()) shouldBe false
  }

  test("I/Q proof items require both proof context and I/Q availability") {
    showIQProofItems(ctx(inProof = true, iqAvailable = true)) shouldBe true
    showIQProofItems(ctx(inProof = true)) shouldBe false
    showIQProofItems(ctx(iqAvailable = true)) shouldBe false
    showIQProofItems(ctx()) shouldBe false
  }

  test("Extract Lemma needs both proof context and a selection") {
    showExtractLemma(ctx(inProof = true, hasSelection = true)) shouldBe true
    showExtractLemma(ctx(inProof = true)) shouldBe false
    showExtractLemma(ctx(hasSelection = true)) shouldBe false
  }

  test("Refactor to Isar needs proof context and apply-style proof") {
    showRefactorToIsar(ctx(inProof = true, hasApplyProof = true)) shouldBe true
    showRefactorToIsar(ctx(hasApplyProof = true)) shouldBe false
    showRefactorToIsar(ctx(inProof = true)) shouldBe false
  }

  // === Top-level Find Theorems ===

  test("Top-level Find Theorems shows when I/Q is available") {
    showFindTheoremsTop(ctx(iqAvailable = true)) shouldBe true
    showFindTheoremsTop(ctx()) shouldBe false
  }

  // === Generate ===

  test("Generate submenu shows when command or selection is present") {
    showGenerateSubmenu(ctx(hasCommand = true)) shouldBe true
    showGenerateSubmenu(ctx(hasSelection = true)) shouldBe true
    showGenerateSubmenu(ctx()) shouldBe false
  }

  test("Generate items tied to a definition require onDefinition and a command/selection") {
    showGenerateOnDefinition(ctx(hasCommand = true, onDefinition = true)) shouldBe true
    showGenerateOnDefinition(ctx(hasSelection = true, onDefinition = true)) shouldBe true
    showGenerateOnDefinition(ctx(hasCommand = true)) shouldBe false
    showGenerateOnDefinition(ctx(onDefinition = true)) shouldBe false

    showSuggestName(ctx(hasCommand = true, onDefinition = true)) shouldBe true
    showSuggestName(ctx(onDefinition = true)) shouldBe false
  }

  test("Tidy Up shows when in Generate submenu and either selection or proof is active") {
    showTidyUp(ctx(hasCommand = true, hasSelection = true)) shouldBe true
    showTidyUp(ctx(hasCommand = true, inProof = true)) shouldBe true
    showTidyUp(ctx(hasSelection = true, inProof = true)) shouldBe true
    showTidyUp(ctx(hasCommand = true)) shouldBe false
    // Selection alone also shows (the submenu is already enabled, and the inner
    // predicate holds via hasSelection).
    showTidyUp(ctx(hasSelection = true)) shouldBe true
    showTidyUp(ctx()) shouldBe false
  }

  test("Generate Tactic shows when Generate submenu is enabled and a selection exists") {
    showGenerateTactic(ctx(hasSelection = true)) shouldBe true
    showGenerateTactic(ctx(hasCommand = true, hasSelection = true)) shouldBe true
    showGenerateTactic(ctx(hasCommand = true)) shouldBe false
    showGenerateTactic(ctx()) shouldBe false
  }

  // === Analyze ===

  test("Analyze Patterns follows hasCommand regardless of selection") {
    showAnalyzePatterns(ctx(hasCommand = true)) shouldBe true
    showAnalyzePatterns(ctx(hasSelection = true)) shouldBe false
    showAnalyzePatterns(ctx()) shouldBe false
  }

  // === Empty-context regression ===

  test("Totally empty context enables no discoverable items") {
    val empty = ctx()
    showExplain(empty) shouldBe false
    showExplainError(empty) shouldBe false
    showShowType(empty) shouldBe false
    showProofSubmenu(empty) shouldBe false
    showIQProofItems(empty) shouldBe false
    showFindTheoremsTop(empty) shouldBe false
    showGenerateSubmenu(empty) shouldBe false
    showAnalyzePatterns(empty) shouldBe false
  }
}
