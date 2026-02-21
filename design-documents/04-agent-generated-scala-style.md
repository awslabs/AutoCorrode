# Agent-Generated Scala Style Guide

Status: Draft steering document  
Applies to: `iq`, `isabelle-assistant`  
Last reviewed: 2026-02-21

## Purpose

This guide defines expected Scala quality for agent-generated and human-authored code.

## Design Principles

1. Make invalid states unrepresentable where practical.
2. Prefer explicit typed outcomes over implicit failure channels.
3. Keep concurrency contracts visible in code.
4. Optimize for maintainable behavior under strict compile flags.

## Type System Expectations

Required patterns:

- Use sealed traits/enums for closed state sets.
- Use case classes for structured payloads and results.
- Use constructor constraints or smart constructors where invariants matter.
- Avoid stringly typed identifiers when a closed type exists.

Discouraged patterns:

- ad hoc string constants for operation identity.
- broad `Any` payloads without typed decoding.
- nullable semantics hidden in raw strings.

## Error Handling

Required patterns:

- Represent expected failure via `Either`, typed ADTs, or domain errors.
- Reserve exceptions for truly exceptional faults.
- Propagate actionable error context, not opaque messages.

## Concurrency and State

Required patterns:

- Keep mutable shared state small and explicit.
- Use synchronization or volatile fields only where justified and documented.
- Separate UI-thread and worker-thread responsibilities.

## API Boundaries

- Encode external payloads at the boundary, decode to domain types immediately.
- Keep adapter code thin and deterministic.
- Normalize external errors before they enter business logic.

## Style and Readability

- Use descriptive names that capture domain intent.
- Keep methods small and single-purpose where feasible.
- Prefer expression-oriented code over imperative sprawl.
- Add concise comments for non-obvious invariants and thread constraints.

## Compile Flag Policy

Current build policy includes strict compile flags (`-Werror`, `-Wunused`, `-Xlint`, and value-discard protections in production). Agent-generated code must compile cleanly under project defaults.

Tests may use slightly different strictness where justified for test frameworks, but must not hide real warnings in production code.

## Testing Expectations for Scala Changes

Each non-trivial change should include tests that cover:

1. Success path behavior.
2. Error behavior.
3. Concurrency or timeout edge behavior where applicable.
4. Permission/security behavior for tool-related code.

## Acceptance Checks

A Scala change passes this guide only when:

1. Domain states are represented with typed structures.
2. Error channels are explicit and testable.
3. Compile flags remain clean.
4. Thread and boundary assumptions are documented and validated.
