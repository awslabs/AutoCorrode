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
  * region, model selection, temperature, verification settings, and tracing
  * parameters.
  */
class AssistantOptions extends AbstractOptionPane("assistant-general-options") {
  private var regionCombo: Option[JComboBox[String]] = None
  private var modelCombo: Option[JComboBox[String]] = None
  private var crisCheckbox: Option[JCheckBox] = None
  private var refreshButton: Option[JButton] = None
  private var temperatureField: Option[JTextField] = None
  private var maxTokensField: Option[JTextField] = None
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

    val temperature = new JTextField(AssistantOptions.getTemperature.toString, 10)
    temperatureField = Some(temperature)
    addComponent("Temperature (0.0-1.0):", temperature)

    val maxTokens = new JTextField(AssistantOptions.getMaxTokens.toString, 10)
    maxTokensField = Some(maxTokens)
    addComponent("Max Tokens:", maxTokens)

    val toolIterText = AssistantOptions.getMaxToolIterations match {
      case Some(n) => n.toString
      case None    => ""
    }
    val maxToolIterations = new JTextField(toolIterText, 10)
    maxToolIterations.setToolTipText(
      "Maximum tool-use iterations per LLM call. Leave empty or set to 0 for unlimited."
    )
    maxToolIterationsField = Some(maxToolIterations)
    addComponent("Max Tool Iterations:", maxToolIterations)

    addSeparator("Verification (I/Q Integration)")

    val maxRetries =
      new JTextField(AssistantOptions.getMaxVerificationRetries.toString, 10)
    maxRetries.setToolTipText(
      "Maximum LLM retry attempts when proof verification fails"
    )
    maxRetriesField = Some(maxRetries)
    addComponent("Max Retries:", maxRetries)

    val verifyTimeout =
      new JTextField(AssistantOptions.getVerificationTimeout.toString, 10)
    verifyTimeout.setToolTipText(
      "Timeout for proof verification in milliseconds"
    )
    verifyTimeoutField = Some(verifyTimeout)
    addComponent("Timeout (ms):", verifyTimeout)

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
      "Timeout for sledgehammer in milliseconds"
    )
    sledgehammerTimeoutField = Some(sledgehammerTimeout)
    addComponent("Sledgehammer Timeout (ms):", sledgehammerTimeout)

    val maxVerifyCandidates =
      new JTextField(AssistantOptions.getMaxVerifyCandidates.toString, 10)
    maxVerifyCandidates.setToolTipText(
      "Maximum number of suggestions to verify"
    )
    maxVerifyCandidatesField = Some(maxVerifyCandidates)
    addComponent("Max Verify Candidates:", maxVerifyCandidates)

    val findTheoremsLimit =
      new JTextField(AssistantOptions.getFindTheoremsLimit.toString, 10)
    findTheoremsLimit.setToolTipText(
      "Maximum theorems to find for LLM context"
    )
    findTheoremsLimitField = Some(findTheoremsLimit)
    addComponent("Find Theorems Limit:", findTheoremsLimit)

    val findTheoremsTimeout =
      new JTextField(AssistantOptions.getFindTheoremsTimeout.toString, 10)
    findTheoremsTimeout.setToolTipText(
      "Timeout for find_theorems in milliseconds"
    )
    findTheoremsTimeoutField = Some(findTheoremsTimeout)
    addComponent("Find Theorems Timeout (ms):", findTheoremsTimeout)

    addSeparator("Counterexample Search")

    val quickcheckTimeout =
      new JTextField(AssistantOptions.getQuickcheckTimeout.toString, 10)
    quickcheckTimeout.setToolTipText(
      "Timeout for Quickcheck in milliseconds"
    )
    quickcheckTimeoutField = Some(quickcheckTimeout)
    addComponent("Quickcheck Timeout (ms):", quickcheckTimeout)

    val nitpickTimeout =
      new JTextField(AssistantOptions.getNitpickTimeout.toString, 10)
    nitpickTimeout.setToolTipText(
      "Timeout for Nitpick in milliseconds"
    )
    nitpickTimeoutField = Some(nitpickTimeout)
    addComponent("Nitpick Timeout (ms):", nitpickTimeout)

    addSeparator("Simplifier Tracing")

    val traceTimeout = new JTextField(AssistantOptions.getTraceTimeout.toString, 10)
    traceTimeout.setToolTipText("Timeout for simp/auto tracing in seconds")
    traceTimeoutField = Some(traceTimeout)
    addComponent("Trace Timeout (s):", traceTimeout)

    val traceDepth = new JTextField(AssistantOptions.getTraceDepth.toString, 10)
    traceDepth.setToolTipText("Maximum depth for simplifier trace")
    traceDepthField = Some(traceDepth)
    addComponent("Trace Depth:", traceDepth)

  }

  private def populateModelCombo(models: Array[String], current: String): Unit = {
    val combo = requireUi(modelCombo, "modelCombo")
    combo.removeAllItems()
    models.foreach(combo.addItem)
    if (current.nonEmpty && !models.contains(current)) combo.addItem(current)
    if (current.nonEmpty) combo.setSelectedItem(current)
    else if (models.nonEmpty) combo.setSelectedIndex(0)
  }

  private def loadModelsFromCache(): Unit = {
    val current = AssistantOptions.getBaseModelId
    val models = BedrockModels.getModels
    populateModelCombo(models, current)
  }

  private def refreshModelsAsync(): Unit = {
    val regionCombo = requireUi(this.regionCombo, "regionCombo")
    val modelCombo = requireUi(this.modelCombo, "modelCombo")
    val refresh = requireUi(refreshButton, "refreshButton")
    val region =
      Option(regionCombo.getSelectedItem).map(_.toString).getOrElse("us-east-1")
    val current =
      Option(modelCombo.getSelectedItem).map(_.toString).getOrElse("")
    refresh.setEnabled(false)
    refresh.setText("Refreshing...")

    new SwingWorker[Array[String], Void] {
      override def doInBackground(): Array[String] =
        BedrockModels.refreshModels(region)
      override def done(): Unit = {
        refresh.setEnabled(true)
        refresh.setText("Refresh Models")
        try {
          val models = get()
          populateModelCombo(models, current)
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
    val (
      regionCombo,
      modelCombo,
      crisCheckbox,
      temperatureField,
      maxTokensField,
      maxToolIterationsField,
      maxRetriesField,
      verifyTimeoutField,
      verifySuggestionsCheckbox,
      useSledgehammerCheckbox,
      sledgehammerTimeoutField,
      quickcheckTimeoutField,
      nitpickTimeoutField,
      maxVerifyCandidatesField,
      findTheoremsLimitField,
      findTheoremsTimeoutField,
      traceTimeoutField,
      traceDepthField
    ) = (
      requireUi(this.regionCombo, "regionCombo"),
      requireUi(this.modelCombo, "modelCombo"),
      requireUi(this.crisCheckbox, "crisCheckbox"),
      requireUi(this.temperatureField, "temperatureField"),
      requireUi(this.maxTokensField, "maxTokensField"),
      requireUi(this.maxToolIterationsField, "maxToolIterationsField"),
      requireUi(this.maxRetriesField, "maxRetriesField"),
      requireUi(this.verifyTimeoutField, "verifyTimeoutField"),
      requireUi(this.verifySuggestionsCheckbox, "verifySuggestionsCheckbox"),
      requireUi(this.useSledgehammerCheckbox, "useSledgehammerCheckbox"),
      requireUi(this.sledgehammerTimeoutField, "sledgehammerTimeoutField"),
      requireUi(this.quickcheckTimeoutField, "quickcheckTimeoutField"),
      requireUi(this.nitpickTimeoutField, "nitpickTimeoutField"),
      requireUi(this.maxVerifyCandidatesField, "maxVerifyCandidatesField"),
      requireUi(this.findTheoremsLimitField, "findTheoremsLimitField"),
      requireUi(this.findTheoremsTimeoutField, "findTheoremsTimeoutField"),
      requireUi(this.traceTimeoutField, "traceTimeoutField"),
      requireUi(this.traceDepthField, "traceDepthField")
    )

    val warnings = ListBuffer.empty[String]
    def warn(msg: String): Unit = warnings += msg

    def normalizeInt(
        raw: String,
        settingLabel: String,
        default: Int,
        min: Int,
        max: Int
    ): String =
      try {
        val parsed = raw.trim.toInt
        val clamped = math.max(min, math.min(max, parsed))
        if (clamped != parsed)
          warn(s"$settingLabel was clamped to $clamped (valid range: $min-$max).")
        clamped.toString
      } catch {
        case _: NumberFormatException =>
          warn(s"$settingLabel was invalid and reset to $default.")
          default.toString
      }

    def normalizeLong(
        raw: String,
        settingLabel: String,
        default: Long,
        min: Long,
        max: Long
    ): String =
      try {
        val parsed = raw.trim.toLong
        val clamped = math.max(min, math.min(max, parsed))
        if (clamped != parsed)
          warn(
            s"$settingLabel was clamped to $clamped (valid range: $min-$max)."
          )
        clamped.toString
      } catch {
        case _: NumberFormatException =>
          warn(s"$settingLabel was invalid and reset to $default.")
          default.toString
      }

    def normalizeDouble(
        raw: String,
        settingLabel: String,
        default: Double,
        min: Double,
        max: Double
    ): String =
      try {
        val parsed = raw.trim.toDouble
        val clamped = math.max(min, math.min(max, parsed))
        if (clamped != parsed)
          warn(s"$settingLabel was clamped to $clamped (valid range: $min-$max).")
        clamped.toString
      } catch {
        case _: NumberFormatException =>
          warn(s"$settingLabel was invalid and reset to $default.")
          default.toString
      }

    def normalizeOptionalInt(
        raw: String,
        settingLabel: String,
        default: Int,
        min: Int,
        max: Int
    ): String = {
      val normalized = raw.trim.toLowerCase
      if (
        normalized.isEmpty || normalized == "0" || normalized == "none" || normalized == "unlimited"
      ) ""
      else
        try {
          val parsed = normalized.toInt
          if (parsed < min || parsed > max) {
            warn(
              s"$settingLabel was invalid and reset to $default (or leave empty for unlimited)."
            )
            default.toString
          } else parsed.toString
        } catch {
          case _: NumberFormatException =>
            warn(
              s"$settingLabel was invalid and reset to $default (or leave empty for unlimited)."
            )
            default.toString
        }
    }

    val regionValue = {
      val value =
        Option(regionCombo.getSelectedItem).map(_.toString.trim).getOrElse("")
      if (value.matches("^[a-z]{2}(?:-[a-z]+)+-\\d+$")) value
      else {
        warn("AWS Region had an invalid format and was reset to us-east-1.")
        "us-east-1"
      }
    }

    val modelValue = {
      val value =
        Option(modelCombo.getSelectedItem).map(_.toString.trim).getOrElse("")
      if (value.isEmpty || BedrockModels.isAnthropicModelId(value)) value
      else {
        warn("Model ID was invalid and has been cleared. Only Anthropic model IDs are supported.")
        ""
      }
    }

    val temperatureValue = normalizeDouble(
      temperatureField.getText,
      "Temperature",
      AssistantConstants.DEFAULT_TEMPERATURE,
      AssistantConstants.MIN_TEMPERATURE,
      AssistantConstants.MAX_TEMPERATURE
    )
    val maxTokensValue = normalizeInt(
      maxTokensField.getText,
      "Max Tokens",
      AssistantConstants.DEFAULT_MAX_TOKENS,
      AssistantConstants.MIN_MAX_TOKENS,
      AssistantConstants.MAX_MAX_TOKENS
    )
    val maxToolIterationsValue = normalizeOptionalInt(
      maxToolIterationsField.getText,
      "Max Tool Iterations",
      AssistantConstants.DEFAULT_MAX_TOOL_ITERATIONS,
      1,
      50
    )
    val maxRetriesValue = normalizeInt(
      maxRetriesField.getText,
      "Max Retries",
      AssistantConstants.DEFAULT_MAX_VERIFICATION_RETRIES,
      1,
      10
    )
    val verifyTimeoutValue = normalizeLong(
      verifyTimeoutField.getText,
      "Verification Timeout",
      AssistantConstants.DEFAULT_VERIFICATION_TIMEOUT,
      5000L,
      300000L
    )
    val sledgehammerTimeoutValue = normalizeLong(
      sledgehammerTimeoutField.getText,
      "Sledgehammer Timeout",
      AssistantConstants.DEFAULT_SLEDGEHAMMER_TIMEOUT,
      1000L,
      300000L
    )
    val quickcheckTimeoutValue = normalizeLong(
      quickcheckTimeoutField.getText,
      "Quickcheck Timeout",
      AssistantConstants.DEFAULT_QUICKCHECK_TIMEOUT,
      1000L,
      300000L
    )
    val nitpickTimeoutValue = normalizeLong(
      nitpickTimeoutField.getText,
      "Nitpick Timeout",
      AssistantConstants.DEFAULT_NITPICK_TIMEOUT,
      1000L,
      300000L
    )
    val maxVerifyCandidatesValue = normalizeInt(
      maxVerifyCandidatesField.getText,
      "Max Verify Candidates",
      AssistantConstants.DEFAULT_MAX_VERIFY_CANDIDATES,
      1,
      20
    )
    val findTheoremsLimitValue = normalizeInt(
      findTheoremsLimitField.getText,
      "Find Theorems Limit",
      AssistantConstants.DEFAULT_FIND_THEOREMS_LIMIT,
      1,
      100
    )
    val findTheoremsTimeoutValue = normalizeLong(
      findTheoremsTimeoutField.getText,
      "Find Theorems Timeout",
      AssistantConstants.DEFAULT_FIND_THEOREMS_TIMEOUT,
      1000L,
      300000L
    )
    val traceTimeoutValue = normalizeInt(
      traceTimeoutField.getText,
      "Trace Timeout",
      AssistantConstants.DEFAULT_TRACE_TIMEOUT,
      1,
      300
    )
    val traceDepthValue = normalizeInt(
      traceDepthField.getText,
      "Trace Depth",
      AssistantConstants.DEFAULT_TRACE_DEPTH,
      1,
      50
    )

    jEdit.setProperty("assistant.aws.region", regionValue)
    jEdit.setProperty("assistant.model.id", modelValue)
    jEdit.setBooleanProperty("assistant.use.cris", crisCheckbox.isSelected)
    jEdit.setProperty("assistant.temperature", temperatureValue)
    jEdit.setProperty("assistant.max.tokens", maxTokensValue)
    jEdit.setProperty("assistant.max.tool.iterations", maxToolIterationsValue)
    jEdit.setProperty("assistant.verify.max.retries", maxRetriesValue)
    jEdit.setProperty("assistant.verify.timeout", verifyTimeoutValue)
    jEdit.setBooleanProperty(
      "assistant.verify.suggestions",
      verifySuggestionsCheckbox.isSelected
    )
    jEdit.setBooleanProperty(
      "assistant.use.sledgehammer",
      useSledgehammerCheckbox.isSelected
    )
    jEdit.setProperty("assistant.sledgehammer.timeout", sledgehammerTimeoutValue)
    jEdit.setProperty("assistant.quickcheck.timeout", quickcheckTimeoutValue)
    jEdit.setProperty("assistant.nitpick.timeout", nitpickTimeoutValue)
    jEdit.setProperty("assistant.max.verify.candidates", maxVerifyCandidatesValue)
    jEdit.setProperty("assistant.find.theorems.limit", findTheoremsLimitValue)
    jEdit.setProperty("assistant.find.theorems.timeout", findTheoremsTimeoutValue)
    jEdit.setProperty("assistant.trace.timeout", traceTimeoutValue)
    jEdit.setProperty("assistant.trace.depth", traceDepthValue)

    regionCombo.setSelectedItem(regionValue)
    modelCombo.setSelectedItem(modelValue)
    temperatureField.setText(temperatureValue)
    maxTokensField.setText(maxTokensValue)
    maxToolIterationsField.setText(maxToolIterationsValue)
    maxRetriesField.setText(maxRetriesValue)
    verifyTimeoutField.setText(verifyTimeoutValue)
    sledgehammerTimeoutField.setText(sledgehammerTimeoutValue)
    quickcheckTimeoutField.setText(quickcheckTimeoutValue)
    nitpickTimeoutField.setText(nitpickTimeoutValue)
    maxVerifyCandidatesField.setText(maxVerifyCandidatesValue)
    findTheoremsLimitField.setText(findTheoremsLimitValue)
    findTheoremsTimeoutField.setText(findTheoremsTimeoutValue)
    traceTimeoutField.setText(traceTimeoutValue)
    traceDepthField.setText(traceDepthValue)

    AssistantOptions.invalidateCache()
    AssistantDockable.refreshModelLabel()

    if (warnings.nonEmpty) {
      val msg = warnings.map(w => s"• $w").mkString("\n")
      JOptionPane.showMessageDialog(
        this,
        s"Some settings were adjusted while saving:\n\n$msg",
        "Isabelle Assistant",
        JOptionPane.WARNING_MESSAGE
      )
    }
  }
}

object AssistantOptions {
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
  private def isValidBaseModelId(modelId: String): Boolean =
    modelId.matches(modelIdPattern) &&
      (modelId.isEmpty || BedrockModels.isAnthropicModelId(modelId))

  /** All parsed settings in a single immutable snapshot, cached atomically.
    * Boolean settings are included here (not read from jEdit directly) to
    * ensure a consistent view across all settings.
    */
  private[assistant] case class SettingsSnapshot(
      region: String,
      baseModelId: String,
      temperature: Double,
      maxTokens: Int,
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
      useSledgehammer: Boolean
  )

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

  private[assistant] def parseSnapshot(
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

    SettingsSnapshot(
      region =
        if (region.matches("^[a-z]{2}(?:-[a-z]+)+-\\d+$")) region
        else "us-east-1",
      baseModelId = if (isValidBaseModelId(modelId)) modelId else "",
      temperature = doubleProp(
        "assistant.temperature",
        AssistantConstants.DEFAULT_TEMPERATURE,
        AssistantConstants.MIN_TEMPERATURE,
        AssistantConstants.MAX_TEMPERATURE
      ),
      maxTokens = intProp(
        "assistant.max.tokens",
        AssistantConstants.DEFAULT_MAX_TOKENS,
        AssistantConstants.MIN_MAX_TOKENS,
        AssistantConstants.MAX_MAX_TOKENS
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
      useSledgehammer = boolProp("assistant.use.sledgehammer", false)
    )
  }

  def invalidateCache(): Unit = synchronized { _cache = None }

  // --- Accessors (all go through the atomic snapshot) ---

  def getRegion: String = snapshot.region
  def getBaseModelId: String = snapshot.baseModelId
  def getTemperature: Double = snapshot.temperature
  def getMaxTokens: Int = snapshot.maxTokens
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

  def getModelId: String = {
    val base = getBaseModelId
    if (base.isEmpty) ""
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
    DoubleSetting(
      "temperature",
      "assistant.temperature",
      AssistantConstants.MIN_TEMPERATURE,
      AssistantConstants.MAX_TEMPERATURE,
      _.temperature
    ),
    IntSetting(
      "max_tokens",
      "assistant.max.tokens",
      AssistantConstants.MIN_MAX_TOKENS,
      AssistantConstants.MAX_MAX_TOKENS,
      _.maxTokens
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
    IntSetting("trace_depth", "assistant.trace.depth", 1, 50, _.traceDepth)
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

  def listSettings: String =
    settingDefs.map(d => s"${d.key} = ${d.get(snapshot)}").mkString("\n")
}
