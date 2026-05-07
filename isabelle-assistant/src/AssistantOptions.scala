/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.{jEdit, AbstractOptionPane}
import javax.swing.{
  JComboBox,
  JTextField,
  JButton,
  JCheckBox,
  SwingWorker,
  JOptionPane
}
import scala.collection.mutable.ListBuffer

/** jEdit option pane for Assistant configuration. Provides GUI controls for AWS
  * region, model selection, verification settings, and tracing parameters.
  */
class AssistantOptions extends AbstractOptionPane("assistant-general-options") {
  private var regionCombo: Option[JComboBox[String]] = None
  private var modelCombo: Option[JComboBox[String]] = None
  private var crisCheckbox: Option[JCheckBox] = None
  private var refreshButton: Option[JButton] = None
  private var maxTokensField: Option[JTextField] = None
  private var maxContextTokensField: Option[JTextField] = None
  private var maxRetriesField: Option[JTextField] = None
  private var verifyTimeoutField: Option[JTextField] = None
  private var useSledgehammerCheckbox: Option[JCheckBox] = None
  private var verifySuggestionsCheckbox: Option[JCheckBox] = None
  private var sledgehammerTimeoutField: Option[JTextField] = None
  private var maxVerifyCandidatesField: Option[JTextField] = None
  private var findTheoremsLimitField: Option[JTextField] = None
  private var findTheoremsTimeoutField: Option[JTextField] = None
  private var quickcheckTimeoutField: Option[JTextField] = None
  private var nitpickTimeoutField: Option[JTextField] = None
  private var traceTimeoutField: Option[JTextField] = None
  private var traceDepthField: Option[JTextField] = None
  private var maxToolIterationsField: Option[JTextField] = None
  private var planningModelCombo: Option[JComboBox[String]] = None
  private var summarizationModelCombo: Option[JComboBox[String]] = None
  private var autoSummarizeCheckbox: Option[JCheckBox] = None
  private var summarizationThresholdField: Option[JTextField] = None

  private def requireUi[A](opt: Option[A], fieldName: String): A =
    opt.getOrElse(
      throw new IllegalStateException(
        s"AssistantOptions UI field '$fieldName' accessed before initialization"
      )
    )

  override def _init(): Unit = {
    addSeparator("AWS Configuration")

    val region = new JComboBox(AssistantOptions.REGIONS)
    region.setEditable(true)
    region.setSelectedItem(AssistantOptions.getRegion)
    regionCombo = Some(region)
    addComponent("AWS Region:", region)

    val model = new JComboBox[String]()
    modelCombo = Some(model)
    loadModelsFromCache()
    addComponent("Model:", model)

    val refresh = new JButton("Refresh Models")
    refresh.addActionListener(_ => refreshModelsAsync())
    refreshButton = Some(refresh)
    addComponent("", refresh)

    val cris = new JCheckBox(
      "Use Cross-Region Inference (CRIS)",
      AssistantOptions.getUseCris
    )
    cris.setToolTipText(
      "Prefix model ID with us./eu. for cross-region inference"
    )
    crisCheckbox = Some(cris)
    addComponent("", cris)

    addSeparator("Model Parameters")

    val maxTokens = new JTextField(AssistantOptions.getMaxTokens.toString, 10)
    maxTokens.setToolTipText(s"Maximum tokens in model's response (output length). Default: ${AssistantConstants.DEFAULT_MAX_TOKENS}.")
    maxTokensField = Some(maxTokens)
    addComponent(s"Max Output Tokens (default ${AssistantConstants.DEFAULT_MAX_TOKENS}):", maxTokens)

    val maxContextTokens = new JTextField(AssistantOptions.getMaxContextTokens.toString, 10)
    maxContextTokens.setToolTipText(
      "<html>Maximum tokens for conversation history sent to the model (input context budget).<br/>" +
      "This controls when older messages are truncated to fit within limits.<br/><br/>" +
      "<b>Not</b> the same as Max Output Tokens (response length).<br/><br/>" +
      "• Default: 60,000 tokens<br/>" +
      "• Claude models support up to 200,000 token context<br/>" +
      "• Higher = longer conversations before truncation<br/>" +
      "• Lower = reduces API costs and latency</html>"
    )
    maxContextTokensField = Some(maxContextTokens)
    addComponent(s"Max Context Tokens (default ${AssistantConstants.DEFAULT_MAX_CONTEXT_TOKENS}):", maxContextTokens)

    val toolIterText = AssistantOptions.getMaxToolIterations match {
      case Some(n) => n.toString
      case None    => ""
    }
    val maxToolIterations = new JTextField(toolIterText, 10)
    maxToolIterations.setToolTipText(
      s"Maximum tool-use iterations per LLM call. Leave empty or set to 0 for unlimited. Default: ${AssistantConstants.DEFAULT_MAX_TOOL_ITERATIONS}."
    )
    maxToolIterationsField = Some(maxToolIterations)
    addComponent(s"Max Tool Iterations (default ${AssistantConstants.DEFAULT_MAX_TOOL_ITERATIONS}):", maxToolIterations)

    addSeparator("Verification (I/Q Integration)")

    val maxRetries =
      new JTextField(AssistantOptions.getMaxVerificationRetries.toString, 10)
    maxRetries.setToolTipText(
      s"Maximum LLM retry attempts when proof verification fails. Default: ${AssistantConstants.DEFAULT_MAX_VERIFICATION_RETRIES}."
    )
    maxRetriesField = Some(maxRetries)
    addComponent(s"Max Retries (default ${AssistantConstants.DEFAULT_MAX_VERIFICATION_RETRIES}):", maxRetries)

    val verifyTimeout =
      new JTextField(AssistantOptions.getVerificationTimeout.toString, 10)
    verifyTimeout.setToolTipText(
      s"Timeout for proof verification in milliseconds. Default: ${AssistantConstants.DEFAULT_VERIFICATION_TIMEOUT}."
    )
    verifyTimeoutField = Some(verifyTimeout)
    addComponent(s"Timeout ms (default ${AssistantConstants.DEFAULT_VERIFICATION_TIMEOUT}):", verifyTimeout)

    addSeparator("Proof Suggestions")

    val verifySuggestions =
      new JCheckBox("Verify Suggestions", AssistantOptions.getVerifySuggestions)
    verifySuggestions.setToolTipText(
      "Verify proof suggestions using I/Q before display"
    )
    verifySuggestionsCheckbox = Some(verifySuggestions)
    addComponent("", verifySuggestions)

    val useSledgehammer =
      new JCheckBox("Use Sledgehammer", AssistantOptions.getUseSledgehammer)
    useSledgehammer.setToolTipText(
      "Run sledgehammer in parallel with LLM suggestions"
    )
    useSledgehammerCheckbox = Some(useSledgehammer)
    addComponent("", useSledgehammer)

    val sledgehammerTimeout =
      new JTextField(AssistantOptions.getSledgehammerTimeout.toString, 10)
    sledgehammerTimeout.setToolTipText(
      s"Timeout for sledgehammer in milliseconds. Default: ${AssistantConstants.DEFAULT_SLEDGEHAMMER_TIMEOUT}."
    )
    sledgehammerTimeoutField = Some(sledgehammerTimeout)
    addComponent(s"Sledgehammer Timeout ms (default ${AssistantConstants.DEFAULT_SLEDGEHAMMER_TIMEOUT}):", sledgehammerTimeout)

    val maxVerifyCandidates =
      new JTextField(AssistantOptions.getMaxVerifyCandidates.toString, 10)
    maxVerifyCandidates.setToolTipText(
      s"Maximum number of suggestions to verify. Default: ${AssistantConstants.DEFAULT_MAX_VERIFY_CANDIDATES}."
    )
    maxVerifyCandidatesField = Some(maxVerifyCandidates)
    addComponent(s"Max Verify Candidates (default ${AssistantConstants.DEFAULT_MAX_VERIFY_CANDIDATES}):", maxVerifyCandidates)

    val findTheoremsLimit =
      new JTextField(AssistantOptions.getFindTheoremsLimit.toString, 10)
    findTheoremsLimit.setToolTipText(
      s"Maximum theorems to find for LLM context. Default: ${AssistantConstants.DEFAULT_FIND_THEOREMS_LIMIT}."
    )
    findTheoremsLimitField = Some(findTheoremsLimit)
    addComponent(s"Find Theorems Limit (default ${AssistantConstants.DEFAULT_FIND_THEOREMS_LIMIT}):", findTheoremsLimit)

    val findTheoremsTimeout =
      new JTextField(AssistantOptions.getFindTheoremsTimeout.toString, 10)
    findTheoremsTimeout.setToolTipText(
      s"Timeout for find_theorems in milliseconds. Default: ${AssistantConstants.DEFAULT_FIND_THEOREMS_TIMEOUT}."
    )
    findTheoremsTimeoutField = Some(findTheoremsTimeout)
    addComponent(s"Find Theorems Timeout ms (default ${AssistantConstants.DEFAULT_FIND_THEOREMS_TIMEOUT}):", findTheoremsTimeout)

    addSeparator("Counterexample Search")

    val quickcheckTimeout =
      new JTextField(AssistantOptions.getQuickcheckTimeout.toString, 10)
    quickcheckTimeout.setToolTipText(
      s"Timeout for Quickcheck in milliseconds. Default: ${AssistantConstants.DEFAULT_QUICKCHECK_TIMEOUT}."
    )
    quickcheckTimeoutField = Some(quickcheckTimeout)
    addComponent(s"Quickcheck Timeout ms (default ${AssistantConstants.DEFAULT_QUICKCHECK_TIMEOUT}):", quickcheckTimeout)

    val nitpickTimeout =
      new JTextField(AssistantOptions.getNitpickTimeout.toString, 10)
    nitpickTimeout.setToolTipText(
      s"Timeout for Nitpick in milliseconds. Default: ${AssistantConstants.DEFAULT_NITPICK_TIMEOUT}."
    )
    nitpickTimeoutField = Some(nitpickTimeout)
    addComponent(s"Nitpick Timeout ms (default ${AssistantConstants.DEFAULT_NITPICK_TIMEOUT}):", nitpickTimeout)

    addSeparator("Simplifier Tracing")

    val traceTimeout = new JTextField(AssistantOptions.getTraceTimeout.toString, 10)
    traceTimeout.setToolTipText(s"Timeout for simp/auto tracing in seconds. Default: ${AssistantConstants.DEFAULT_TRACE_TIMEOUT}.")
    traceTimeoutField = Some(traceTimeout)
    addComponent(s"Trace Timeout s (default ${AssistantConstants.DEFAULT_TRACE_TIMEOUT}):", traceTimeout)

    val traceDepth = new JTextField(AssistantOptions.getTraceDepth.toString, 10)
    traceDepth.setToolTipText(s"Maximum depth for simplifier trace. Default: ${AssistantConstants.DEFAULT_TRACE_DEPTH}.")
    traceDepthField = Some(traceDepth)
    addComponent(s"Trace Depth (default ${AssistantConstants.DEFAULT_TRACE_DEPTH}):", traceDepth)

    addSeparator("Planning Agent")

    val planningModel = new JComboBox[String]()
    val models = BedrockModels.getModels
    AssistantOptions.populateOptionalModelCombo(
      planningModel, models, AssistantOptions.getPlanningBaseModelId
    )
    planningModel.setToolTipText(
      "Model for planning sub-agents (leave as 'use main model' to use the main model)"
    )
    planningModelCombo = Some(planningModel)
    addComponent("Planning Model:", planningModel)

    addSeparator("Context Summarization")

    val autoSummarize = new JCheckBox(
      "Auto-Summarize Context",
      AssistantOptions.getAutoSummarize
    )
    autoSummarize.setToolTipText(
      "<html>Automatically summarize conversation when context budget is reached.<br/>" +
      "When enabled, instead of truncating old messages, the assistant will<br/>" +
      "use a dedicated LLM call to compress the conversation history into a<br/>" +
      "structured summary that preserves task progress and key information.</html>"
    )
    autoSummarizeCheckbox = Some(autoSummarize)
    addComponent("", autoSummarize)

    val summarizationThreshold = new JTextField(
      AssistantOptions.getSummarizationThreshold.toString, 10
    )
    summarizationThreshold.setToolTipText(
      s"Context budget percentage (${AssistantConstants.MIN_SUMMARIZATION_THRESHOLD}-${AssistantConstants.MAX_SUMMARIZATION_THRESHOLD}) that triggers summarization. Default: ${AssistantConstants.DEFAULT_SUMMARIZATION_THRESHOLD}"
    )
    summarizationThresholdField = Some(summarizationThreshold)
    addComponent("Summarization Threshold:", summarizationThreshold)

    val summarizationModel = new JComboBox[String]()
    AssistantOptions.populateOptionalModelCombo(
      summarizationModel, models, AssistantOptions.getSummarizationBaseModelId
    )
    summarizationModel.setToolTipText(
      "<html>Model for context summarization (leave as 'use main model' to use the main model).<br/>" +
      "Consider using a faster/cheaper model like Haiku for summarization.</html>"
    )
    summarizationModelCombo = Some(summarizationModel)
    addComponent("Summarization Model:", summarizationModel)

  }

  private def loadModelsFromCache(): Unit = {
    val current = AssistantOptions.getBaseModelId
    val models = BedrockModels.getModels
    AssistantOptions.populateMainModelCombo(
      requireUi(modelCombo, "modelCombo"), models, current
    )
  }

  private def refreshModelsAsync(): Unit = {
    val regionCombo = requireUi(this.regionCombo, "regionCombo")
    val modelCombo = requireUi(this.modelCombo, "modelCombo")
    val planningModelCombo = requireUi(this.planningModelCombo, "planningModelCombo")
    val summarizationModelCombo = requireUi(this.summarizationModelCombo, "summarizationModelCombo")
    val refresh = requireUi(refreshButton, "refreshButton")
    val region =
      Option(regionCombo.getSelectedItem).map(_.toString).getOrElse("us-east-1")
    val current =
      Option(modelCombo.getSelectedItem).map(_.toString).getOrElse("")
    val currentPlanning =
      Option(planningModelCombo.getSelectedItem).map(_.toString).filter(_ != AssistantOptions.USE_MAIN_MODEL_LABEL).getOrElse("")
    val currentSummarization =
      Option(summarizationModelCombo.getSelectedItem).map(_.toString).filter(_ != AssistantOptions.USE_MAIN_MODEL_LABEL).getOrElse("")
    refresh.setEnabled(false)
    refresh.setText("Refreshing…")

    new SwingWorker[Array[String], Void] {
      override def doInBackground(): Array[String] =
        BedrockModels.refreshModels(region)
      override def done(): Unit = {
        refresh.setEnabled(true)
        refresh.setText("Refresh Models")
        try {
          val models = get()
          AssistantOptions.populateMainModelCombo(modelCombo, models, current)
          AssistantOptions.populateOptionalModelCombo(planningModelCombo, models, currentPlanning)
          AssistantOptions.populateOptionalModelCombo(summarizationModelCombo, models, currentSummarization)

          if (models.isEmpty) {
            JOptionPane.showMessageDialog(
              AssistantOptions.this,
              "No Anthropic models were returned for this region.",
              "Isabelle Assistant",
              JOptionPane.INFORMATION_MESSAGE
            )
          }
        } catch {
          case ex: Exception =>
            ErrorHandler.logSilentError("AssistantOptions", ex)
            JOptionPane.showMessageDialog(
              AssistantOptions.this,
              s"Failed to refresh model list: ${ex.getMessage}",
              "Isabelle Assistant",
              JOptionPane.ERROR_MESSAGE
            )
        }
      }
    }.execute()
  }

  override def _save(): Unit = {
    val fields = collectFields()
    val normalizer = new AssistantOptions.Normalizer
    val normalized = AssistantOptions.normalizeAll(fields, normalizer)

    AssistantOptions.writeJEditProperties(normalized)
    reflectNormalizedBack(fields, normalized)

    AssistantOptions.invalidateCache()
    AssistantDockable.refreshModelLabel()

    if (normalizer.warnings.nonEmpty) {
      val msg = normalizer.warnings.map(w => s"• $w").mkString("\n")
      JOptionPane.showMessageDialog(
        this,
        s"Some settings were adjusted while saving:\n\n$msg",
        "Isabelle Assistant",
        JOptionPane.WARNING_MESSAGE
      )
    }
  }

  private def collectFields(): AssistantOptions.UiFields =
    AssistantOptions.UiFields(
      regionCombo = requireUi(this.regionCombo, "regionCombo"),
      modelCombo = requireUi(this.modelCombo, "modelCombo"),
      crisCheckbox = requireUi(this.crisCheckbox, "crisCheckbox"),
      maxTokensField = requireUi(this.maxTokensField, "maxTokensField"),
      maxContextTokensField = requireUi(this.maxContextTokensField, "maxContextTokensField"),
      maxToolIterationsField = requireUi(this.maxToolIterationsField, "maxToolIterationsField"),
      maxRetriesField = requireUi(this.maxRetriesField, "maxRetriesField"),
      verifyTimeoutField = requireUi(this.verifyTimeoutField, "verifyTimeoutField"),
      verifySuggestionsCheckbox = requireUi(this.verifySuggestionsCheckbox, "verifySuggestionsCheckbox"),
      useSledgehammerCheckbox = requireUi(this.useSledgehammerCheckbox, "useSledgehammerCheckbox"),
      sledgehammerTimeoutField = requireUi(this.sledgehammerTimeoutField, "sledgehammerTimeoutField"),
      quickcheckTimeoutField = requireUi(this.quickcheckTimeoutField, "quickcheckTimeoutField"),
      nitpickTimeoutField = requireUi(this.nitpickTimeoutField, "nitpickTimeoutField"),
      maxVerifyCandidatesField = requireUi(this.maxVerifyCandidatesField, "maxVerifyCandidatesField"),
      findTheoremsLimitField = requireUi(this.findTheoremsLimitField, "findTheoremsLimitField"),
      findTheoremsTimeoutField = requireUi(this.findTheoremsTimeoutField, "findTheoremsTimeoutField"),
      traceTimeoutField = requireUi(this.traceTimeoutField, "traceTimeoutField"),
      traceDepthField = requireUi(this.traceDepthField, "traceDepthField"),
      planningModelCombo = requireUi(this.planningModelCombo, "planningModelCombo"),
      summarizationModelCombo = requireUi(this.summarizationModelCombo, "summarizationModelCombo"),
      autoSummarizeCheckbox = requireUi(this.autoSummarizeCheckbox, "autoSummarizeCheckbox"),
      summarizationThresholdField = requireUi(this.summarizationThresholdField, "summarizationThresholdField")
    )

  private def reflectNormalizedBack(
      f: AssistantOptions.UiFields,
      n: AssistantOptions.NormalizedSettings
  ): Unit = {
    f.regionCombo.setSelectedItem(n.region)
    f.modelCombo.setSelectedItem(n.model)
    f.maxTokensField.setText(n.maxTokens)
    f.maxContextTokensField.setText(n.maxContextTokens)
    f.maxToolIterationsField.setText(n.maxToolIterations)
    f.maxRetriesField.setText(n.maxRetries)
    f.verifyTimeoutField.setText(n.verifyTimeout)
    f.sledgehammerTimeoutField.setText(n.sledgehammerTimeout)
    f.quickcheckTimeoutField.setText(n.quickcheckTimeout)
    f.nitpickTimeoutField.setText(n.nitpickTimeout)
    f.maxVerifyCandidatesField.setText(n.maxVerifyCandidates)
    f.findTheoremsLimitField.setText(n.findTheoremsLimit)
    f.findTheoremsTimeoutField.setText(n.findTheoremsTimeout)
    f.traceTimeoutField.setText(n.traceTimeout)
    f.traceDepthField.setText(n.traceDepth)
    if (n.planningModel.isEmpty) f.planningModelCombo.setSelectedIndex(0)
    else f.planningModelCombo.setSelectedItem(n.planningModel)
    f.summarizationThresholdField.setText(n.summarizationThreshold)
    if (n.summarizationModel.isEmpty) f.summarizationModelCombo.setSelectedIndex(0)
    else f.summarizationModelCombo.setSelectedItem(n.summarizationModel)
  }
}

object AssistantOptions {
  // Schema — the snapshot shape and parsing rules — lives in
  // AssistantOptionsSchema.scala so that the pure data/validation layer is
  // decoupled from jEdit's Props API. The companion object below is a
  // jEdit-bound facade.
  val REGIONS: Array[String] = AssistantOptionsSchema.REGIONS
  type SettingsSnapshot = AssistantOptionsSchema.SettingsSnapshot
  val SettingsSnapshot = AssistantOptionsSchema.SettingsSnapshot

  // Label used by optional-model combo boxes to indicate "fall back to main model".
  private[assistant] val USE_MAIN_MODEL_LABEL = "(use main model)"

  /** Populate a main-model combo: no sentinel entry, empty base leaves first item
    * selected if any. */
  private[assistant] def populateMainModelCombo(
      combo: JComboBox[String],
      models: Array[String],
      current: String
  ): Unit = {
    combo.removeAllItems()
    models.foreach(combo.addItem)
    if (current.nonEmpty && !models.contains(current)) combo.addItem(current)
    if (current.nonEmpty) combo.setSelectedItem(current)
    else if (models.nonEmpty) combo.setSelectedIndex(0)
  }

  /** Populate an optional-model combo: prepends [[USE_MAIN_MODEL_LABEL]]; empty
    * `current` selects the sentinel so the main model is used. */
  private[assistant] def populateOptionalModelCombo(
      combo: JComboBox[String],
      models: Array[String],
      current: String
  ): Unit = {
    combo.removeAllItems()
    combo.addItem(USE_MAIN_MODEL_LABEL)
    models.foreach(combo.addItem)
    if (current.nonEmpty && !models.contains(current)) combo.addItem(current)
    if (current.nonEmpty) combo.setSelectedItem(current)
    else combo.setSelectedIndex(0)
  }

  // --- _save() support types: bundle UI fields and normalized values for
  // section-by-section processing without ballooning the save method. ---

  private case class UiFields(
      regionCombo: JComboBox[String],
      modelCombo: JComboBox[String],
      crisCheckbox: JCheckBox,
      maxTokensField: JTextField,
      maxContextTokensField: JTextField,
      maxToolIterationsField: JTextField,
      maxRetriesField: JTextField,
      verifyTimeoutField: JTextField,
      verifySuggestionsCheckbox: JCheckBox,
      useSledgehammerCheckbox: JCheckBox,
      sledgehammerTimeoutField: JTextField,
      quickcheckTimeoutField: JTextField,
      nitpickTimeoutField: JTextField,
      maxVerifyCandidatesField: JTextField,
      findTheoremsLimitField: JTextField,
      findTheoremsTimeoutField: JTextField,
      traceTimeoutField: JTextField,
      traceDepthField: JTextField,
      planningModelCombo: JComboBox[String],
      summarizationModelCombo: JComboBox[String],
      autoSummarizeCheckbox: JCheckBox,
      summarizationThresholdField: JTextField
  )

  private case class NormalizedSettings(
      region: String,
      model: String,
      useCris: Boolean,
      maxTokens: String,
      maxContextTokens: String,
      maxToolIterations: String,
      maxRetries: String,
      verifyTimeout: String,
      verifySuggestions: Boolean,
      useSledgehammer: Boolean,
      sledgehammerTimeout: String,
      quickcheckTimeout: String,
      nitpickTimeout: String,
      maxVerifyCandidates: String,
      findTheoremsLimit: String,
      findTheoremsTimeout: String,
      traceTimeout: String,
      traceDepth: String,
      planningModel: String,
      summarizationModel: String,
      autoSummarize: Boolean,
      summarizationThreshold: String
  )

  private class Normalizer {
    val warnings: ListBuffer[String] = ListBuffer.empty[String]
    def warn(msg: String): Unit = { val _ = warnings += msg }

    def normalizeInt(
        raw: String, label: String, default: Int, min: Int, max: Int
    ): String =
      try {
        val parsed = raw.trim.toInt
        val clamped = math.max(min, math.min(max, parsed))
        if (clamped != parsed)
          warn(s"$label was clamped to $clamped (valid range: $min-$max).")
        clamped.toString
      } catch {
        case _: NumberFormatException =>
          warn(s"$label was invalid and reset to $default.")
          default.toString
      }

    def normalizeLong(
        raw: String, label: String, default: Long, min: Long, max: Long
    ): String =
      try {
        val parsed = raw.trim.toLong
        val clamped = math.max(min, math.min(max, parsed))
        if (clamped != parsed)
          warn(s"$label was clamped to $clamped (valid range: $min-$max).")
        clamped.toString
      } catch {
        case _: NumberFormatException =>
          warn(s"$label was invalid and reset to $default.")
          default.toString
      }

    def normalizeDouble(
        raw: String, label: String, default: Double, min: Double, max: Double
    ): String =
      try {
        val parsed = raw.trim.toDouble
        val clamped = math.max(min, math.min(max, parsed))
        if (clamped != parsed)
          warn(s"$label was clamped to $clamped (valid range: $min-$max).")
        clamped.toString
      } catch {
        case _: NumberFormatException =>
          warn(s"$label was invalid and reset to $default.")
          default.toString
      }

    def normalizeOptionalInt(
        raw: String, label: String, default: Int, min: Int, max: Int
    ): String = {
      val normalized = raw.trim.toLowerCase
      if (normalized.isEmpty || normalized == "0" || normalized == "none" || normalized == "unlimited") ""
      else
        try {
          val parsed = normalized.toInt
          if (parsed < min || parsed > max) {
            warn(s"$label was invalid and reset to $default (or leave empty for unlimited).")
            default.toString
          } else parsed.toString
        } catch {
          case _: NumberFormatException =>
            warn(s"$label was invalid and reset to $default (or leave empty for unlimited).")
            default.toString
        }
    }
  }

  /** Validate AWS region text; falls back to us-east-1 with a warning if malformed. */
  private def validateRegion(raw: String, n: Normalizer): String =
    if (raw.matches("^[a-z]{2}(?:-[a-z]+)+-\\d+$")) raw
    else {
      n.warn("AWS Region had an invalid format and was reset to us-east-1.")
      "us-east-1"
    }

  /** Validate a main-model ID; clears and warns on invalid input. */
  private def validateMainModel(raw: String, n: Normalizer): String =
    if (raw.isEmpty || BedrockModels.isAnthropicModelId(raw)) raw
    else {
      n.warn("Model ID was invalid and has been cleared. Only Anthropic model IDs are supported.")
      ""
    }

  /** Validate an optional model combo selection; accepts empty or the "use main"
    * sentinel as "leave unset", and warns when a non-Anthropic value is entered.
    *
    * The warning distinguishes "user typed a non-Anthropic model" from "user
    * left the field blank" — the latter is the documented "use main model"
    * path and shouldn't surface any message. */
  private def validateOptionalModel(
      raw: String, name: String, n: Normalizer
  ): String =
    if (raw == USE_MAIN_MODEL_LABEL || raw.isEmpty) ""
    else if (BedrockModels.isAnthropicModelId(raw)) raw
    else {
      n.warn(
        s"$name Model ID '$raw' is not a valid Anthropic model and has been cleared. " +
          s"$name operations will use the main model."
      )
      ""
    }

  private def normalizeAwsSection(f: UiFields, n: Normalizer): (String, String) = {
    val region = validateRegion(
      Option(f.regionCombo.getSelectedItem).map(_.toString.trim).getOrElse(""), n
    )
    val model = validateMainModel(
      Option(f.modelCombo.getSelectedItem).map(_.toString.trim).getOrElse(""), n
    )
    (region, model)
  }

  private def normalizeModelParams(f: UiFields, n: Normalizer): (String, String, String) = (
    n.normalizeInt(
      f.maxTokensField.getText, "Max Tokens",
      AssistantConstants.DEFAULT_MAX_TOKENS, AssistantConstants.MIN_MAX_TOKENS, Int.MaxValue
    ),
    n.normalizeInt(
      f.maxContextTokensField.getText, "Max Context Tokens",
      AssistantConstants.DEFAULT_MAX_CONTEXT_TOKENS, AssistantConstants.MIN_MAX_CONTEXT_TOKENS, Int.MaxValue
    ),
    n.normalizeOptionalInt(
      f.maxToolIterationsField.getText, "Max Tool Iterations",
      AssistantConstants.DEFAULT_MAX_TOOL_ITERATIONS, 1, 50
    )
  )

  private def normalizeVerification(f: UiFields, n: Normalizer): (String, String) = (
    n.normalizeInt(
      f.maxRetriesField.getText, "Max Retries",
      AssistantConstants.DEFAULT_MAX_VERIFICATION_RETRIES, 1, 10
    ),
    n.normalizeLong(
      f.verifyTimeoutField.getText, "Verification Timeout",
      AssistantConstants.DEFAULT_VERIFICATION_TIMEOUT, 5000L, 300000L
    )
  )

  private def normalizeSuggestions(f: UiFields, n: Normalizer): (String, String, String, String) = (
    n.normalizeLong(
      f.sledgehammerTimeoutField.getText, "Sledgehammer Timeout",
      AssistantConstants.DEFAULT_SLEDGEHAMMER_TIMEOUT, 1000L, 300000L
    ),
    n.normalizeInt(
      f.maxVerifyCandidatesField.getText, "Max Verify Candidates",
      AssistantConstants.DEFAULT_MAX_VERIFY_CANDIDATES, 1, 20
    ),
    n.normalizeInt(
      f.findTheoremsLimitField.getText, "Find Theorems Limit",
      AssistantConstants.DEFAULT_FIND_THEOREMS_LIMIT, 1, 100
    ),
    n.normalizeLong(
      f.findTheoremsTimeoutField.getText, "Find Theorems Timeout",
      AssistantConstants.DEFAULT_FIND_THEOREMS_TIMEOUT, 1000L, 300000L
    )
  )

  private def normalizeCounterexample(f: UiFields, n: Normalizer): (String, String) = (
    n.normalizeLong(
      f.quickcheckTimeoutField.getText, "Quickcheck Timeout",
      AssistantConstants.DEFAULT_QUICKCHECK_TIMEOUT, 1000L, 300000L
    ),
    n.normalizeLong(
      f.nitpickTimeoutField.getText, "Nitpick Timeout",
      AssistantConstants.DEFAULT_NITPICK_TIMEOUT, 1000L, 300000L
    )
  )

  private def normalizeTracing(f: UiFields, n: Normalizer): (String, String) = (
    n.normalizeInt(
      f.traceTimeoutField.getText, "Trace Timeout",
      AssistantConstants.DEFAULT_TRACE_TIMEOUT, 1, 300
    ),
    n.normalizeInt(
      f.traceDepthField.getText, "Trace Depth",
      AssistantConstants.DEFAULT_TRACE_DEPTH, 1, 50
    )
  )

  private def normalizeSummarization(f: UiFields, n: Normalizer): (String, String, String) = {
    val planningModel = validateOptionalModel(
      Option(f.planningModelCombo.getSelectedItem).map(_.toString.trim).getOrElse(""),
      "Planning", n
    )
    val threshold = n.normalizeDouble(
      f.summarizationThresholdField.getText, "Summarization Threshold",
      AssistantConstants.DEFAULT_SUMMARIZATION_THRESHOLD,
      AssistantConstants.MIN_SUMMARIZATION_THRESHOLD,
      AssistantConstants.MAX_SUMMARIZATION_THRESHOLD
    )
    val summarizationModel = validateOptionalModel(
      Option(f.summarizationModelCombo.getSelectedItem).map(_.toString.trim).getOrElse(""),
      "Summarization", n
    )
    (planningModel, threshold, summarizationModel)
  }

  private def normalizeAll(f: UiFields, n: Normalizer): NormalizedSettings = {
    val (region, model) = normalizeAwsSection(f, n)
    val (maxTokens, maxContextTokens, maxToolIterations) = normalizeModelParams(f, n)
    val (maxRetries, verifyTimeout) = normalizeVerification(f, n)
    val (sledgehammerTimeout, maxVerifyCandidates, findTheoremsLimit, findTheoremsTimeout) =
      normalizeSuggestions(f, n)
    val (quickcheckTimeout, nitpickTimeout) = normalizeCounterexample(f, n)
    val (traceTimeout, traceDepth) = normalizeTracing(f, n)
    val (planningModel, summarizationThreshold, summarizationModel) =
      normalizeSummarization(f, n)
    NormalizedSettings(
      region = region,
      model = model,
      useCris = f.crisCheckbox.isSelected,
      maxTokens = maxTokens,
      maxContextTokens = maxContextTokens,
      maxToolIterations = maxToolIterations,
      maxRetries = maxRetries,
      verifyTimeout = verifyTimeout,
      verifySuggestions = f.verifySuggestionsCheckbox.isSelected,
      useSledgehammer = f.useSledgehammerCheckbox.isSelected,
      sledgehammerTimeout = sledgehammerTimeout,
      quickcheckTimeout = quickcheckTimeout,
      nitpickTimeout = nitpickTimeout,
      maxVerifyCandidates = maxVerifyCandidates,
      findTheoremsLimit = findTheoremsLimit,
      findTheoremsTimeout = findTheoremsTimeout,
      traceTimeout = traceTimeout,
      traceDepth = traceDepth,
      planningModel = planningModel,
      summarizationModel = summarizationModel,
      autoSummarize = f.autoSummarizeCheckbox.isSelected,
      summarizationThreshold = summarizationThreshold
    )
  }

  private def writeJEditProperties(n: NormalizedSettings): Unit = {
    jEdit.setProperty("assistant.aws.region", n.region)
    jEdit.setProperty("assistant.model.id", n.model)
    jEdit.setBooleanProperty("assistant.use.cris", n.useCris)
    jEdit.setProperty("assistant.max.tokens", n.maxTokens)
    jEdit.setProperty("assistant.max.context.tokens", n.maxContextTokens)
    jEdit.setProperty("assistant.max.tool.iterations", n.maxToolIterations)
    jEdit.setProperty("assistant.verify.max.retries", n.maxRetries)
    jEdit.setProperty("assistant.verify.timeout", n.verifyTimeout)
    jEdit.setBooleanProperty("assistant.verify.suggestions", n.verifySuggestions)
    jEdit.setBooleanProperty("assistant.use.sledgehammer", n.useSledgehammer)
    jEdit.setProperty("assistant.sledgehammer.timeout", n.sledgehammerTimeout)
    jEdit.setProperty("assistant.quickcheck.timeout", n.quickcheckTimeout)
    jEdit.setProperty("assistant.nitpick.timeout", n.nitpickTimeout)
    jEdit.setProperty("assistant.max.verify.candidates", n.maxVerifyCandidates)
    jEdit.setProperty("assistant.find.theorems.limit", n.findTheoremsLimit)
    jEdit.setProperty("assistant.find.theorems.timeout", n.findTheoremsTimeout)
    jEdit.setProperty("assistant.trace.timeout", n.traceTimeout)
    jEdit.setProperty("assistant.trace.depth", n.traceDepth)
    jEdit.setProperty("assistant.planning.model.id", n.planningModel)
    jEdit.setBooleanProperty("assistant.auto.summarize", n.autoSummarize)
    jEdit.setProperty("assistant.summarization.threshold", n.summarizationThreshold)
    jEdit.setProperty("assistant.summarization.model.id", n.summarizationModel)
  }

  private def isValidBaseModelId(modelId: String): Boolean =
    AssistantOptionsSchema.isValidBaseModelId(modelId)

  @volatile private var _cache: Option[SettingsSnapshot] = None

  private def snapshot: SettingsSnapshot = _cache match {
    case Some(s) => s
    case None    =>
      synchronized {
        _cache match {
          case Some(s) => s
          case None    =>
            val s = loadSnapshot()
            _cache = Some(s)
            s
        }
      }
  }

  private def loadSnapshot(): SettingsSnapshot = {
    parseSnapshot(
      (key, default) => jEdit.getProperty(key, default),
      (key, default) => jEdit.getBooleanProperty(key, default)
    )
  }

  /** Delegates to AssistantOptionsSchema — exposed here at the old location
    * so existing call sites (and tests) keep working.
    */
  private[assistant] def parseSnapshot(
      prop: (String, String) => String,
      boolProp: (String, Boolean) => Boolean
  ): SettingsSnapshot =
    AssistantOptionsSchema.parseSnapshot(prop, boolProp)

  def invalidateCache(): Unit = synchronized { _cache = None }

  // --- Accessors (all go through the atomic snapshot) ---

  def getRegion: String = snapshot.region
  def getBaseModelId: String = snapshot.baseModelId
  def getMaxTokens: Int = snapshot.maxTokens
  def getMaxContextTokens: Int = snapshot.maxContextTokens
  def getMaxToolIterations: Option[Int] = snapshot.maxToolIterations
  def getMaxVerificationRetries: Int = snapshot.maxRetries
  def getVerificationTimeout: Long = snapshot.verifyTimeout
  def getSledgehammerTimeout: Long = snapshot.sledgehammerTimeout
  def getQuickcheckTimeout: Long = snapshot.quickcheckTimeout
  def getNitpickTimeout: Long = snapshot.nitpickTimeout
  def getMaxVerifyCandidates: Int = snapshot.maxVerifyCandidates
  def getFindTheoremsLimit: Int = snapshot.findTheoremsLimit
  def getFindTheoremsTimeout: Long = snapshot.findTheoremsTimeout
  def getTraceTimeout: Int = snapshot.traceTimeout
  def getTraceDepth: Int = snapshot.traceDepth
  def getUseCris: Boolean = snapshot.useCris
  def getVerifySuggestions: Boolean = snapshot.verifySuggestions
  def getUseSledgehammer: Boolean = snapshot.useSledgehammer
  def getPlanningBaseModelId: String = snapshot.planningBaseModelId

  def getModelId: String = {
    val base = getBaseModelId
    if (base.isEmpty) ""
    else if (getUseCris) BedrockModels.applyCrisPrefix(base, getRegion)
    else base
  }

  def getPlanningModelId: String = {
    val base = getPlanningBaseModelId
    if (base.isEmpty) getModelId // Fallback to main model if planning model not set
    else if (getUseCris) BedrockModels.applyCrisPrefix(base, getRegion)
    else base
  }

  def getSummarizationBaseModelId: String = snapshot.summarizationBaseModelId
  def getAutoSummarize: Boolean = snapshot.autoSummarize
  def getSummarizationThreshold: Double = snapshot.summarizationThreshold

  def getSummarizationModelId: String = {
    val base = getSummarizationBaseModelId
    if (base.isEmpty) getModelId // Fallback to main model if summarization model not set
    else if (getUseCris) BedrockModels.applyCrisPrefix(base, getRegion)
    else base
  }

  // --- Data-driven setting definitions ---

  /** Descriptor for a single configuration setting, enabling DRY get/set/list.
    */
  private sealed trait SettingDef {
    def key: String
    def get(s: SettingsSnapshot): String
    def set(value: String): Option[String]
  }

  private case class StringSetting(
      key: String,
      prop: String,
      validate: String => Boolean,
      errorMsg: String,
      getter: SettingsSnapshot => String
  ) extends SettingDef {
    def get(s: SettingsSnapshot): String = getter(s)
    def set(value: String): Option[String] =
      if (validate(value)) {
        jEdit.setProperty(prop, value); Some(s"$key = $value")
      } else Some(errorMsg)
  }

  private case class BoolSetting(
      key: String,
      prop: String,
      getter: SettingsSnapshot => Boolean
  ) extends SettingDef {
    def get(s: SettingsSnapshot): String = getter(s).toString
    def set(value: String): Option[String] =
      try {
        val b = value.toBoolean; jEdit.setBooleanProperty(prop, b);
        Some(s"$key = $b")
      } catch {
        case _: IllegalArgumentException => Some(s"$key must be true or false")
      }
  }

  private case class IntSetting(
      key: String,
      prop: String,
      min: Int,
      max: Int,
      getter: SettingsSnapshot => Int
  ) extends SettingDef {
    def get(s: SettingsSnapshot): String = getter(s).toString
    def set(value: String): Option[String] =
      try {
        val v = value.toInt
        if (v >= min && v <= max) {
          jEdit.setProperty(prop, value); Some(s"$key = $value")
        } else Some(s"$key must be between $min and $max")
      } catch {
        case _: NumberFormatException => Some(s"$key must be a number")
      }
  }

  private case class LongSetting(
      key: String,
      prop: String,
      min: Long,
      max: Long,
      getter: SettingsSnapshot => Long
  ) extends SettingDef {
    def get(s: SettingsSnapshot): String = getter(s).toString
    def set(value: String): Option[String] =
      try {
        val v = value.toLong
        if (v >= min && v <= max) {
          jEdit.setProperty(prop, value); Some(s"$key = $value")
        } else Some(s"$key must be between $min and $max")
      } catch {
        case _: NumberFormatException => Some(s"$key must be a number")
      }
  }

  private case class DoubleSetting(
      key: String,
      prop: String,
      min: Double,
      max: Double,
      getter: SettingsSnapshot => Double
  ) extends SettingDef {
    def get(s: SettingsSnapshot): String = getter(s).toString
    def set(value: String): Option[String] =
      try {
        val v = value.toDouble
        if (v >= min && v <= max) {
          jEdit.setProperty(prop, value); Some(s"$key = $value")
        } else Some(s"$key must be between $min and $max")
      } catch {
        case _: NumberFormatException => Some(s"$key must be a number")
      }
  }

  private case class OptionalIntSetting(
      key: String,
      prop: String,
      min: Int,
      max: Int,
      getter: SettingsSnapshot => Option[Int]
  ) extends SettingDef {
    def get(s: SettingsSnapshot): String = getter(s) match {
      case Some(n) => n.toString
      case None    => "unlimited"
    }
    def set(value: String): Option[String] = {
      val normalized = value.trim.toLowerCase
      if (
        normalized.isEmpty || normalized == "0" || normalized == "none" || normalized == "unlimited"
      ) {
        jEdit.setProperty(prop, "")
        Some(s"$key = unlimited")
      } else
        try {
          val v = value.toInt
          if (v >= min && v <= max) {
            jEdit.setProperty(prop, value); Some(s"$key = $value")
          } else
            Some(
              s"$key must be between $min and $max, or 0/none/unlimited for no limit"
            )
        } catch {
          case _: NumberFormatException =>
            Some(s"$key must be a number or 0/none/unlimited")
        }
    }
  }

  /** Registry of all settings — single source of truth for get/set/list. */
  private val settingDefs: List[SettingDef] = List(
    StringSetting(
      "region",
      "assistant.aws.region",
      _.matches("^[a-z]{2}(?:-[a-z]+)+-\\d+$"),
      "Invalid region format. Expected format: us-east-1, eu-west-2, me-south-1, etc.",
      _.region
    ),
    StringSetting(
      "model",
      "assistant.model.id",
      isValidBaseModelId,
      "Invalid model ID. Only Anthropic model IDs are supported (for example: anthropic.claude-3-7-sonnet-20250219-v1:0).",
      _.baseModelId
    ),
    BoolSetting("cris", "assistant.use.cris", _.useCris),
    IntSetting(
      "max_tokens",
      "assistant.max.tokens",
      AssistantConstants.MIN_MAX_TOKENS,
      Int.MaxValue,
      _.maxTokens
    ),
    IntSetting(
      "max_context_tokens",
      "assistant.max.context.tokens",
      AssistantConstants.MIN_MAX_CONTEXT_TOKENS,
      Int.MaxValue,
      _.maxContextTokens
    ),
    OptionalIntSetting(
      "max_tool_iterations",
      "assistant.max.tool.iterations",
      1,
      50,
      _.maxToolIterations
    ),
    IntSetting(
      "max_retries",
      "assistant.verify.max.retries",
      1,
      10,
      _.maxRetries
    ),
    LongSetting(
      "verify_timeout",
      "assistant.verify.timeout",
      5000L,
      300000L,
      _.verifyTimeout
    ),
    BoolSetting(
      "verify_suggestions",
      "assistant.verify.suggestions",
      _.verifySuggestions
    ),
    BoolSetting(
      "use_sledgehammer",
      "assistant.use.sledgehammer",
      _.useSledgehammer
    ),
    LongSetting(
      "sledgehammer_timeout",
      "assistant.sledgehammer.timeout",
      1000L,
      300000L,
      _.sledgehammerTimeout
    ),
    LongSetting(
      "quickcheck_timeout",
      "assistant.quickcheck.timeout",
      1000L,
      300000L,
      _.quickcheckTimeout
    ),
    LongSetting(
      "nitpick_timeout",
      "assistant.nitpick.timeout",
      1000L,
      300000L,
      _.nitpickTimeout
    ),
    IntSetting(
      "max_verify_candidates",
      "assistant.max.verify.candidates",
      1,
      20,
      _.maxVerifyCandidates
    ),
    IntSetting(
      "find_theorems_limit",
      "assistant.find.theorems.limit",
      1,
      100,
      _.findTheoremsLimit
    ),
    LongSetting(
      "find_theorems_timeout",
      "assistant.find.theorems.timeout",
      1000L,
      300000L,
      _.findTheoremsTimeout
    ),
    IntSetting(
      "trace_timeout",
      "assistant.trace.timeout",
      1,
      300,
      _.traceTimeout
    ),
    IntSetting("trace_depth", "assistant.trace.depth", 1, 50, _.traceDepth),
    StringSetting(
      "planning_model",
      "assistant.planning.model.id",
      isValidBaseModelId,
      "Invalid planning model ID. Only Anthropic model IDs are supported (or empty to use main model).",
      s => if (s.planningBaseModelId.isEmpty) "(use main)" else s.planningBaseModelId
    ),
    BoolSetting("auto_summarize", "assistant.auto.summarize", _.autoSummarize),
    DoubleSetting(
      "summarization_threshold",
      "assistant.summarization.threshold",
      AssistantConstants.MIN_SUMMARIZATION_THRESHOLD,
      AssistantConstants.MAX_SUMMARIZATION_THRESHOLD,
      _.summarizationThreshold
    ),
    StringSetting(
      "summarization_model",
      "assistant.summarization.model.id",
      isValidBaseModelId,
      "Invalid summarization model ID. Only Anthropic model IDs are supported (or empty to use main model).",
      s => if (s.summarizationBaseModelId.isEmpty) "(use main)" else s.summarizationBaseModelId
    )
  )

  /** Map from normalized key to definition, supporting aliases. */
  private lazy val settingsByKey: Map[String, SettingDef] = {
    val base = settingDefs.map(d => d.key -> d).toMap
    // Aliases
    base ++ Map(
      "use_cris" -> base("cris"),
      "sledgehammer" -> base("use_sledgehammer")
    )
  }

  private def normalizeKey(key: String): String =
    key.toLowerCase.replace('-', '_')

  private[assistant] def normalizeKeyForTest(key: String): String =
    normalizeKey(key)
  private[assistant] def hasSettingKey(key: String): Boolean =
    settingsByKey.contains(normalizeKey(key))
  private[assistant] def publicSettingKeys: List[String] =
    settingDefs.map(_.key)

  def setSetting(key: String, value: String): Option[String] = {
    val result = settingsByKey.get(normalizeKey(key)).flatMap(_.set(value))
    invalidateCache()
    result
  }

  def getSetting(key: String): Option[String] =
    settingsByKey.get(normalizeKey(key)).map(_.get(snapshot))

  def listSettings: String = {
    val snap = snapshot
    settingDefs.map { d =>
      val current = d.get(snap)
      val default = defaultFor(d.key)
      default match {
        case Some(dv) if dv != current => s"${d.key} = $current (default: $dv)"
        case _                         => s"${d.key} = $current"
      }
    }.mkString("\n")
  }

  /** Static default per setting key. Mirrors AssistantOptionsSchema's defaults
    * so that `:set` can show `(default: X)` next to any non-default value.
    * Keys without a meaningful constant default (region, model ids — env-
    * dependent) return None and render as plain `key = value`. */
  private def defaultFor(key: String): Option[String] = key match {
    case "max_tokens"              => Some(AssistantConstants.DEFAULT_MAX_TOKENS.toString)
    case "max_context_tokens"      => Some(AssistantConstants.DEFAULT_MAX_CONTEXT_TOKENS.toString)
    case "max_tool_iterations"     => Some(AssistantConstants.DEFAULT_MAX_TOOL_ITERATIONS.toString)
    case "max_retries"             => Some(AssistantConstants.DEFAULT_MAX_VERIFICATION_RETRIES.toString)
    case "verify_timeout"          => Some(AssistantConstants.DEFAULT_VERIFICATION_TIMEOUT.toString)
    case "sledgehammer_timeout"    => Some(AssistantConstants.DEFAULT_SLEDGEHAMMER_TIMEOUT.toString)
    case "quickcheck_timeout"      => Some(AssistantConstants.DEFAULT_QUICKCHECK_TIMEOUT.toString)
    case "nitpick_timeout"         => Some(AssistantConstants.DEFAULT_NITPICK_TIMEOUT.toString)
    case "max_verify_candidates"   => Some(AssistantConstants.DEFAULT_MAX_VERIFY_CANDIDATES.toString)
    case "find_theorems_limit"     => Some(AssistantConstants.DEFAULT_FIND_THEOREMS_LIMIT.toString)
    case "find_theorems_timeout"   => Some(AssistantConstants.DEFAULT_FIND_THEOREMS_TIMEOUT.toString)
    case "trace_timeout"           => Some(AssistantConstants.DEFAULT_TRACE_TIMEOUT.toString)
    case "trace_depth"             => Some(AssistantConstants.DEFAULT_TRACE_DEPTH.toString)
    case "cris"                    => Some("true")
    case "verify_suggestions"      => Some("true")
    case "use_sledgehammer"        => Some("false")
    case "auto_summarize"          => Some("true")
    case "summarization_threshold" => Some(AssistantConstants.DEFAULT_SUMMARIZATION_THRESHOLD.toString)
    case "region"                  => Some("us-east-1")
    case _                         => None
  }
}
