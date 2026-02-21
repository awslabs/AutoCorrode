# Tooling and Permissions Model

Status: Active steering document  
Applies to: `isabelle-assistant` tools and `iq` operation surfaces  
Last reviewed: 2026-02-21

## Purpose

This document defines tool taxonomy, permission semantics, security expectations, and user interaction rules for model tool use.

## Tool Taxonomy

Current assistant tool inventory includes 35 tools (`isabelle-assistant/src/ToolId.scala`).

Categories:

- Read and inspect: theory reads, diagnostics, entities, context.
- Prove and verify: verify, execute steps, try methods, theorem search, ATP/model-finders.
- Edit and navigation: edit/create/open theory, cursor moves.
- External and meta: web search, ask_user, task list operations.

## Permission Levels

Canonical permission levels (`ToolPermissions`):

- `Allow`
- `AskAtFirstUse`
- `AskAlways`
- `Deny`

Normative behavior:

- `Deny` tools are not offered to the model and are rejected if requested.
- `AskAlways` requires an explicit approval every invocation.
- `AskAtFirstUse` prompts once per session and stores a scoped decision.
- `Allow` executes without prompt.

## Default Risk Posture

Defaults should remain conservative:

- Read-only inspection: usually `Allow`.
- Proof compute tools: usually `AskAtFirstUse`.
- Side-effecting or external tools: usually `AskAlways`.

Any default relaxation requires rationale and threat analysis.

## Prompting and Explainability Requirements

Permission prompts must include:

1. Tool display name.
2. Resource target where relevant (theory/file/query).
3. Sanitized summary of arguments.

Sensitive argument keys (token, secret, password, auth, credential, api_key) must be redacted in prompt previews and logs.

## Server-Side Security Contract (`iq`)

`iq` enforces baseline controls through environment configuration:

- Loopback binding by default.
- optional auth token requirement.
- mutation root constraints.
- read root constraints.
- bounded client thread count.

These controls are mandatory defense-in-depth even when assistant permissions are enabled.

## Canonical Capability Surface (`iq`)

The `iq` MCP surface is canonicalized; overlapping aliases are not retained.

- File creation is expressed via `open_file` with `create_if_missing=true` (optionally with `content` and `overwrite_if_exists`).
- Goal-state reads are obtained from `get_context_info.goal` (no separate `get_goal_state` capability at `iq` layer).
- Proof-block introspection is handled by `get_proof_blocks` with explicit `scope`:
  - `scope="selection"` for focused block extraction,
  - `scope="file"` for multi-block file extraction.

Assistant-level tool naming may remain user-oriented, but must map to these canonical `iq` operations rather than reintroducing assistant-side semantic duplicates.

## Failure and Degradation Rules

On permission denial or unavailable backend:

1. Surface a clear and concise reason.
2. Continue with lower-capability strategy when feasible.
3. Do not loop on repeated identical failing calls.

## Observability

Tool failures and permission outcomes should be observable in logs without leaking sensitive content.

## Acceptance Checks

A change passes tooling/permission checks only when:

1. Each new tool has an explicit `ToolId`, permission default, description, and tests.
2. Permission prompts remain resource-aware and sanitized.
3. Deny-level hiding behavior is preserved.
4. `iq` security constraints are not bypassed.
