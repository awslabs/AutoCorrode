# Contributing to Isabelle Assistant

## Architecture Overview

Isabelle Assistant is a jEdit plugin written in Scala 3 that integrates AWS Bedrock LLMs with the Isabelle proof assistant. See the [Architecture section in README.md](README.md#architecture) for the high-level component map.

### Layering Rules (Mandatory)

Isabelle Assistant owns UI and model orchestration. Isabelle-proof execution semantics must be owned by I/Q capabilities.

- In `AssistantTools`, the migrated proof tools (`find_theorems`, `verify_proof`, `run_sledgehammer`, `find_counterexample`, `execute_step`, `trace_simplifier`) must remain MCP-only and route through `IQMcpClient`.
- In `IQIntegration`, migrated proof-query APIs (`verifyProofAsync`, `runSledgehammerAsync`, `runFindTheoremsAsync`, `runQueryAsync`, `executeStepAsync`) must remain MCP-only and route through `IQMcpClient`.
- Do not add local fallback logic for those tools via `IQIntegration` or `Extended_Query_Operation`.
- If a capability is missing in I/Q, add it to I/Q rather than re-implementing runtime semantics in Assistant.
- Read-only UI/context introspection is allowed in designated UI modules for interaction latency.
- `make check-layering` is a hard failing gate. Any forbidden low-level Isabelle runtime touchpoint in Assistant fails CI.

### Key Components

| Component | Purpose |
|-----------|---------|
| `AssistantPlugin` | jEdit plugin lifecycle (start/stop) |
| `AssistantDockable` | Chat UI panel (Swing, singleton) |
| `ChatAction` | Command dispatch + chat history |
| `BedrockClient` | AWS Bedrock API with retry, caching, tool-use loop |
| `IQIntegration` | Async adapter/facade over I/Q MCP with GUI-thread callback delivery |
| `SuggestAction` | Proof suggestion pipeline (LLM + sledgehammer) |
| `ContextFetcher` | Goal-aware definition/context lookup via typed I/Q capabilities |
| `GoalExtractor` | Goal/context extraction via typed I/Q MCP goal APIs |
| `PromptLoader` | Mustache template loading from `prompts/` |

### Threading Model

Three thread contexts are used:

- **GUI Thread (Swing EDT)**: All UI updates and jEdit API calls. Use `GUI_Thread.later { ... }`.
- **Isabelle_Thread**: Background work (LLM calls, latch waits). Use `Isabelle_Thread.fork(name = "...") { ... }`.
- **I/Q MCP Worker Threads**: IQ requests run off-EDT; `IQIntegration` dispatches callbacks back onto GUI thread before invoking callers.

**Critical rules:**
- `ContextFetcher.getContext` and `PrintContextAction.getContextString` must NOT be called from the GUI thread (deadlock).
- `IQIntegration.verifyProofAsync`, `runSledgehammerAsync`, `runFindTheoremsAsync`, `runQueryAsync`, and `executeStepAsync` are safe to call from any thread; callbacks are delivered on GUI thread.
- All `AssistantDockable` UI updates go through `GUI_Thread.later`.

## Adding a New Chat Command

1. Create a new action file in `src/` (e.g., `MyFeatureAction.scala`).
2. Add the command to the `dispatch` map in `ChatAction.scala`:
   ```scala
   "my-feature" -> CommandEntry("Description of my feature", (v, a) => MyFeatureAction.run(v, a))
   ```
3. If your command needs I/Q, set `needsIQ = true` in the `CommandEntry`.
4. The command is automatically available as `:my-feature` in chat and appears in `:help`.

## Adding a New Prompt Template

1. Create a Mustache template in `prompts/` (e.g., `my_feature.md`).
2. Document variables at the top: `<!-- Variables: var1 (required), var2 (optional) -->`
3. Use `{{var1}}` for required variables, `{{#var2}}...{{/var2}}` for optional sections.
4. Load with `PromptLoader.load("my_feature.md", Map("var1" -> value))`.

## Adding a New Tool (for Anthropic tool-use)

Tools are wired together in three places: the ID enum, the registry (name + schema), and the dispatch map (runtime behaviour). Follow the steps in order.

1. **Declare the tool ID.** Add a new case to `enum ToolId` in `ToolId.scala` with a unique wire name (the string Anthropic sees).

2. **Define the schema.** Add a `ToolDef` to the `tools` list in `AssistantTools.scala`. The `ToolDef` carries the name, description, and JSON-schema parameters.

3. **Implement the handler.** Put the handler body in whichever file is most appropriate:
   - **Theory-file and proof handlers** (read/write/search theories, verify, sledgehammer, nitpick, etc.) stay as `private def execMyNewTool(...)` methods on `AssistantTools`.
   - **Memory handlers** live in `MemoryToolHandler.scala` (`MemoryToolHandler.execMemoryAdd`, etc.).
   - **Task-list handlers** live in `TaskListToolHandler.scala` (`TaskListToolHandler.execTaskListAdd`, etc.).
   - **Interactive `ask_user`-style handlers** live in `AskUserToolHandler.scala`.
   - If your tool doesn't fit any of the above, prefer adding it to the most-related existing handler file rather than bloating `AssistantTools.scala`.

4. **Wire up dispatch.** Add a line to the `toolHandlers` map in `AssistantTools.scala` pointing your `ToolId` at the handler:
   ```scala
   // In-class (theory ops, etc.):
   ToolId.MyNewTool -> ((args, view) => execMyNewTool(args, view)),

   // Delegated to a dedicated handler file (memory/task/ask-user):
   ToolId.MyNewMemoryTool -> ((a, v) => MemoryToolHandler.execMyNewMemoryTool(a, v)),
   ```
   If the handler doesn't need `view`, use `((a, _) => ...)` — the layering check rejects unused `@unused view: View` parameters.

5. **Permissions.** Add the tool to `defaultPermissions` and `toolDescriptionsById` in `ToolPermissions.scala`. Classify it as `Always`, `AskAtFirstUse`, or `Never` based on side-effect blast radius.

6. **Input sanitation.** Parse arguments through the `ToolArgs` helpers:
   - `ToolArgs.safeStringArg(args, key)` / `ToolArgs.safeStringArgEither(args, key)` for strings
   - `ToolArgs.safeTheoryArg(args)` for a validated theory name
   - `ToolArgs.optionalIntArg(args, key)` / `ToolArgs.intArg(args, key, default)` for integers
   - `ToolArgs.boolArg(args, key, default)` for booleans

7. **Tests.**
   - `ToolIdTest.scala` — verifies the wire name is present and unique.
   - `AssistantToolsTest.scala` — covers dispatch and happy/error paths.
   - `ToolPermissionsTest.scala` — pins the permission classification.
   - If you added a handler file, also extend its own test suite (e.g., `MemoryToolHandlerTest.scala`).

## Customizing the System Prompt

System prompts are loaded from `prompts/system/` in sorted filename order.
- `01_isabelle_style.md` — Core Isabelle expertise (always included)
- Additional files (e.g., `02_autocorrode.md`) are auto-discovered
- See `prompts/system/02_autocorrode.md.example` for framework-specific customization

## Building and Testing

```bash
./fetch-deps.sh          # Download AWS SDK + third-party JARs
make build               # Build the plugin JAR
make install             # Build and install (includes I/Q)
make clean               # Clean build artifacts
make check-layering      # Enforce hard failing Assistant/IQ architectural boundary
make report-layering     # Runtime boundary report (must stay at zero forbidden touchpoints)
```

For a machine-readable boundary snapshot (tsv), run:
`./scripts/check_layering.sh --mode report --inventory-out ../design-documents/10-assistant-runtime-boundary-inventory.tsv`

### Running Tests

Tests use ScalaTest. To run them, you need ScalaTest JARs in `lib/test/`:

```bash
# Download ScalaTest JARs (one-time)
mkdir -p lib/test
curl -sL "https://repo1.maven.org/maven2/org/scalatest/scalatest_3/3.2.17/scalatest_3-3.2.17.jar" -o lib/test/scalatest_3-3.2.17.jar
curl -sL "https://repo1.maven.org/maven2/org/scalatest/scalatest-core_3/3.2.17/scalatest-core_3-3.2.17.jar" -o lib/test/scalatest-core_3-3.2.17.jar
curl -sL "https://repo1.maven.org/maven2/org/scalatest/scalatest-funsuite_3/3.2.17/scalatest-funsuite_3-3.2.17.jar" -o lib/test/scalatest-funsuite_3-3.2.17.jar
curl -sL "https://repo1.maven.org/maven2/org/scalatest/scalatest-matchers-core_3/3.2.17/scalatest-matchers-core_3-3.2.17.jar" -o lib/test/scalatest-matchers-core_3-3.2.17.jar
curl -sL "https://repo1.maven.org/maven2/org/scalatest/scalatest-shouldmatchers_3/3.2.17/scalatest-shouldmatchers_3-3.2.17.jar" -o lib/test/scalatest-shouldmatchers_3-3.2.17.jar
curl -sL "https://repo1.maven.org/maven2/org/scalactic/scalactic_3/3.2.17/scalactic_3-3.2.17.jar" -o lib/test/scalactic_3-3.2.17.jar
curl -sL "https://repo1.maven.org/maven2/org/scalatest/scalatest-compatible/3.2.17/scalatest-compatible-3.2.17.jar" -o lib/test/scalatest-compatible-3.2.17.jar

# Run tests (includes layering guard checks)
make test
```

Note: Some tests require jEdit/Isabelle to be running (integration tests). Unit tests for parsing, rendering, and error handling can run standalone.

## Code Style

- Copyright header on every file: `/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. SPDX-License-Identifier: MIT */`
- Package: `isabelle.assistant`
- Use `@volatile` for shared mutable state across threads
- Use `CountDownLatch` for cross-thread synchronization
- Use `ErrorHandler.withErrorHandling` for standardized error handling
- Log operations with `Output.writeln(s"[Assistant] ...")`
