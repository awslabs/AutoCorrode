# Layering Rules and Module Boundaries

Status: Active steering document  
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

Permitted local behavior:

- read-only UI/context introspection for responsiveness (menu enablement, cursor/selection state, lightweight local affordance checks).
- this permission does not include proof execution, file mutation semantics, or assistant tool semantics.

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
2. Any module in `isabelle-assistant` that directly performs proof-state execution is forbidden.
3. `iq` must not depend on assistant UI classes.
4. Shared data contracts should be explicit and typed.
5. Read-only UI/context introspection may remain assistant-local for interaction latency; semantic operations must still route through `iq`.

## Forbidden Patterns

- Stringly typed protocol glue without typed decoding boundaries.
- Assistant-side shadow implementations of Isabelle operations that already exist in `iq`.
- Permission bypasses where tool execution can occur without policy checks.

## Required Patterns

- Single source of truth for capability ownership.
- Typed ADTs for operation outcomes and normalized errors.
- Deterministic fallbacks on timeout, unavailable backend, or denied permissions.
- Canonical `iq` capability usage from assistant call sites (no reintroduction of deprecated aliases where a canonical tool exists).

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

Current enforcement:

- `make -C isabelle-assistant check-layering` is a failing gate:
  1. migrated proof and theory tools in `AssistantTools`, theory browsing in `TheoryBrowserAction`, and migrated proof-query APIs in `IQIntegration` must remain MCP-only (no local `IQIntegration`/`Extended_Query_Operation` execution paths),
  2. forbidden low-level assistant runtime touchpoints fail,
  3. designated read-only UI/context modules are exempt from the low-level touchpoint scan for responsiveness.
