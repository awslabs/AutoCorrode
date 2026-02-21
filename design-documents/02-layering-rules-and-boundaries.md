# Layering Rules and Module Boundaries

Status: Draft steering document  
Applies to: `iq`, `isabelle-assistant`  
Last reviewed: 2026-02-21

## Purpose

This document defines mandatory dependency and ownership boundaries to keep the architecture understandable and evolvable.

## Layers

### Layer 1: UI and Interaction (`isabelle-assistant`)

Responsibilities:

- Dockables, context menus, command routing, and renderers.
- User-facing state and settings presentation.
- Human approval prompts for tool permissions.

Must not own:

- Core Isabelle operation semantics.
- Proof execution engines.
- Hidden side effects to theory files outside explicit tools.

### Layer 2: Orchestration (`isabelle-assistant`)

Responsibilities:

- Prompt assembly and model invocation.
- Tool-call loop control.
- Mapping tool results to user-readable output.

Must not own:

- direct mutation/query logic that bypasses capability boundaries.

### Layer 3: Capability Backplane (`iq`)

Responsibilities:

- Isabelle query and explore operations.
- File and proof operation primitives.
- Operation normalization and error canonicalization.
- Server-side security controls.

### Layer 4: Isabelle Runtime

Responsibilities:

- PIDE document model and command processing.
- theorem prover and tool execution.

## Dependency Rules

1. `isabelle-assistant` may depend on `iq` capabilities, not on `iq` internals.
2. Any module in `isabelle-assistant` that directly performs proof-state execution should be considered migration debt unless explicitly justified.
3. `iq` must not depend on assistant UI classes.
4. Shared data contracts should be explicit and typed.

## Forbidden Patterns

- Stringly typed protocol glue without typed decoding boundaries.
- Assistant-side shadow implementations of Isabelle operations that already exist in `iq`.
- Permission bypasses where tool execution can occur without policy checks.

## Required Patterns

- Single source of truth for capability ownership.
- Typed ADTs for operation outcomes and normalized errors.
- Deterministic fallbacks on timeout, unavailable backend, or denied permissions.

## Review Checklist

For each new feature, reviewers must answer:

1. Which layer owns this behavior?
2. Is ownership already captured in this document?
3. If not, was the boundary intentionally revised and documented?

## Acceptance Checks

A pull request passes layering checks only when:

1. New dependencies follow allowed layer direction.
2. No forbidden patterns are introduced.
3. Ownership of new behavior is explicit and test-backed.
