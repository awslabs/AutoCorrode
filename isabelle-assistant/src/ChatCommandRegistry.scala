/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Canonical list of colon-prefixed chat commands.
  *
  * The enum is the single source of truth for every command name that the
  * Assistant recognises. `ChatAction.dispatch` pairs each id with its handler
  * and documentation; the `require(...)` assertion there guards against drift.
  *
  * Extracted from ChatAction so the registry can grow (additional metadata,
  * help-text helpers) without enlarging the dispatcher file.
  */
enum CommandId(val wireName: String) {
  case Analyze extends CommandId("analyze")
  case Deps extends CommandId("deps")
  case Explain extends CommandId("explain")
  case ExplainCounterexample extends CommandId("explain-counterexample")
  case ExplainError extends CommandId("explain-error")
  case Extract extends CommandId("extract")
  case Find extends CommandId("find")
  case GenerateDoc extends CommandId("generate-doc")
  case GenerateElim extends CommandId("generate-elim")
  case GenerateIntro extends CommandId("generate-intro")
  case GenerateTests extends CommandId("generate-tests")
  case Help extends CommandId("help")
  case Models extends CommandId("models")
  case Nitpick extends CommandId("nitpick")
  case PrintContext extends CommandId("print-context")
  case Quickcheck extends CommandId("quickcheck")
  case Read extends CommandId("read")
  case Refactor extends CommandId("refactor")
  case Search extends CommandId("search")
  case Set extends CommandId("set")
  case ShowType extends CommandId("show-type")
  case Sledgehammer extends CommandId("sledgehammer")
  case Suggest extends CommandId("suggest")
  case SuggestName extends CommandId("suggest-name")
  case SuggestStrategy extends CommandId("suggest-strategy")
  case SuggestTactic extends CommandId("suggest-tactic")
  case Summarize extends CommandId("summarize")
  case Theories extends CommandId("theories")
  case Tidy extends CommandId("tidy")
  case Trace extends CommandId("trace")
  case TryMethods extends CommandId("try-methods")
  case Verify extends CommandId("verify")
  case Version extends CommandId("version")
}

object CommandId {
  private val byWire: Map[String, CommandId] =
    values.iterator.map(id => id.wireName -> id).toMap

  def fromWire(wireName: String): Option[CommandId] =
    byWire.get(wireName.trim.toLowerCase)
}
