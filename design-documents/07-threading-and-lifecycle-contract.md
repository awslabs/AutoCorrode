# Threading and Lifecycle Contract

Status: Active steering document  
Applies to: `iq`, `isabelle-assistant` async and UI interactions  
Last reviewed: 2026-02-21

## Purpose

This document defines thread-safety and lifecycle rules for responsive, deadlock-resistant operation.

## Thread Classes

### UI Thread (Swing EDT)

Used for:

- jEdit UI updates.
- UI component mutations.
- operations requiring GUI-thread activation.

### Worker Threads

Used for:

- LLM calls and network waits.
- bounded blocking and timeout management.
- heavy processing that must not block UI.

### Callback Threads

Callbacks may arrive on different thread contexts and must synchronize shared state explicitly.

## Non-Negotiable Rules

1. Do not block the UI thread on network or long-running operations.
2. Do not call thread-sensitive APIs from the wrong thread context.
3. Guard shared completion state with explicit synchronization.
4. Ensure every async operation has a timeout and deactivation path.

## Lifecycle Management

Each async operation should define:

- creation/activation semantics.
- completion semantics (success/failure/timeout/cancel).
- cleanup/deactivation on every terminal path.

Plugin lifecycle hooks must clear volatile session state (for example permission session caches) and release resources on stop.

## Error and Timeout Semantics

Timeout is a first-class result, not an implicit failure.

Required:

- explicit timeout result variants.
- single terminal completion callback per operation.
- logging sufficient for diagnosis without noisy duplication.

## Test Expectations

Threading/lifecycle tests should verify:

1. no duplicate completion callback.
2. timeout path triggers cleanup.
3. UI updates are marshaled onto UI thread.
4. cancelled or failed operations do not leak active resources.

## Acceptance Checks

A concurrency-sensitive change is accepted only when:

1. thread ownership of changed code paths is explicit.
2. timeout/cancel/deactivate behavior is preserved.
3. test coverage includes the changed async lifecycle path.
