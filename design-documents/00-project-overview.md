# Project Overview for I/Q and Isabelle Assistant

Status: Active steering document  
Applies to: `iq`, `isabelle-assistant`  
Last reviewed: 2026-02-21

## Purpose

This document defines the high-level purpose, scope, and operating model of the `iq` and `isabelle-assistant` subsystems in AutoCorrode. It is a steering document for contributors and agent-generated changes.

## System Purpose

AutoCorrode includes two interactive assistant subsystems:

- `iq`: Isabelle/Q plugin exposing Isabelle operations as an MCP server for machine clients.
- `isabelle-assistant`: jEdit-based chat and action UI that orchestrates LLM interactions over AWS Bedrock and optional tool use.

Together they support interactive theorem proving workflows in Isabelle/jEdit.

## Product Scope

### In Scope

- Interactive exploration and editing of Isabelle theory files.
- Goal-state inspection and proof context introspection.
- Proof search and proof step validation through Isabelle tooling.
- LLM-assisted explanation, refactoring, and proof suggestion.
- Permission-gated tool execution for model-initiated operations.

### Out of Scope

- Headless replacement for Isabelle itself.
- Unconstrained autonomous editing without user control.
- Hidden or unverifiable proof synthesis.

## Current Capability Baseline

Current capabilities are implemented across both subsystems:

- `iq` provides MCP tools for read/edit/query/explore/save operations and normalized typed responses for assistant integration.
- `isabelle-assistant` provides chat UI, prompt loading, Bedrock orchestration, right-click actions, verification workflows, and user-facing tool permissions.
- Core assistant actions now route command/goal/context/diagnostic/definition/entity lookups through `IQMcpClient`-backed paths.
- Assistant runtime touchpoint inventory is tracked in:
  `design-documents/10-assistant-runtime-boundary-inventory.tsv`
  and is expected to remain empty under the hard layering gate in `isabelle-assistant/scripts/check_layering.sh`.

## Target Capability Split

The target architecture is:

- `isabelle-assistant`: user interaction, prompt orchestration, model invocation, and presentation.
- `iq`: Isabelle interaction backplane, tool execution against Isabelle state, and enforcement of operation-level safety constraints.

This target split is normative for future refactoring and new feature work.

## Enforcement Status

- `make -C isabelle-assistant check-layering` is a failing architectural gate.
- Any direct assistant-side Isabelle runtime touchpoint is rejected (zero-exception policy).

## Stakeholders

- End users (proof engineers) interacting through jEdit.
- Plugin developers extending actions, tools, and workflows.
- Agent-generated contributors whose code must satisfy these steering constraints.

## Quality Priorities

Priority order:

1. Correctness and soundness of proof-related behavior.
2. Safety and permission clarity for tool execution.
3. Reliability and deterministic recovery under tool/API failures.
4. Maintainability through clear layering and typed interfaces.
5. Performance and responsiveness for interactive use.

## Source of Truth

This overview is complemented by:

- `design-documents/01-architecture-current-vs-target.md`
- `design-documents/02-layering-rules-and-boundaries.md`
- `design-documents/03-tooling-and-permissions-model.md`
- `design-documents/06-prompt-system-contract.md`

## Acceptance Checks

A change is consistent with this document only if:

1. It preserves the explicit distinction between assistant orchestration and Isabelle execution responsibilities.
2. It does not weaken permission gating or verification transparency.
3. It does not introduce hidden proof-state assumptions or fabricated tool outputs.
