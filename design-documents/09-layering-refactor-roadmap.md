# Layering Refactor Roadmap

Status: Active (Phase 4 enforcement in place)  
Applies to: architecture convergence for `iq` and `isabelle-assistant`  
Last reviewed: 2026-02-21

## Purpose

This roadmap defines a phased migration from mixed-responsibility implementation toward clean layering where Isabelle interactions are capability-owned by `iq`.

## Desired End State

- assistant owns UX, model orchestration, and permission UX.
- iq owns Isabelle interaction capabilities and operation-level safety constraints.
- assistant consumes typed capability results rather than re-implementing runtime behavior.

## Phase 1: Inventory and Contract Freeze

Deliverables:

- explicit inventory of assistant-side direct Isabelle interactions.
- capability contract list for features that should move into `iq`.
- typed response schema proposals for moved capabilities.

Acceptance criteria:

1. All direct coupling points are documented.
2. No new direct coupling is introduced during this phase.

## Phase 2: Capability Extraction

Deliverables:

- implement missing `iq` capabilities for high-value proof operations currently assistant-local.
- add adapter layer in assistant for new `iq` responses.

Acceptance criteria:

1. extracted operations are exercised through `iq` end-to-end.
2. behavior parity tests exist for extracted flows.

## Phase 3: Assistant Simplification

Deliverables:

- remove or minimize assistant-side duplicated logic.
- keep orchestration and rendering only.

Acceptance criteria:

1. assistant modules no longer contain migrated runtime semantics.
2. permission and UX behavior remains unchanged or improved.

## Phase 4: Hardening and Governance

Deliverables:

- stricter architectural tests/checks preventing forbidden dependencies.
- contributor guidance updated to enforce target layering.

Acceptance criteria:

1. CI checks detect forbidden boundary violations.
2. architecture docs and contributor docs align.

Current implementation status:

- `isabelle-assistant/scripts/check_layering.sh` enforces MCP-only execution for migrated proof tools in `AssistantTools` and migrated proof-query APIs in `IQIntegration`.
- strict mode also enforces a failing runtime-touchpoint allowlist: new direct assistant runtime couplings fail `check-layering`.
- `make -C isabelle-assistant test` now runs `check-layering` before tests.
- contributor and architecture docs include the layering gate and ownership rule.

Current debt inventory snapshot:

- machine-readable runtime touchpoint inventory:
  `design-documents/10-assistant-runtime-boundary-inventory.tsv`
- generated via:
  `make -C isabelle-assistant report-layering` or
  `isabelle-assistant/scripts/check_layering.sh --mode report --inventory-out design-documents/10-assistant-runtime-boundary-inventory.tsv`

Debt buckets mapped to target `iq` capabilities:

1. `iq.explore_query`
   - direct assistant use of `Extended_Query_Operation` / `PIDE.editor` for ad-hoc queries.
   - target: canonical `explore`/query capabilities in `iq` for context/definition extraction.
2. `iq.goal_and_query`
   - assistant-local goal extraction from `PIDE.editor.output`.
   - target: `iq` goal-state and structured goal-analysis capability.
3. `iq.document_model_lookup` + `iq.document_snapshot`
   - assistant-local use of `Document_Model.get_model` + snapshot plumbing.
   - target: `iq` document lookup/session-state capability returning typed structures.
4. `iq.command_lookup`
   - assistant-local `snapshot.get_node` / `command_iterator` command resolution and traversal.
   - target: `iq` command-at-target / command-range / proof-block lookup capabilities.

## Risk Register

- Functional regressions during behavior relocation.
- Performance overhead from additional indirection.
- Protocol drift if typed contracts are not stabilized early.

Mitigations:

- staged rollouts by feature slice.
- parity tests against pre-refactor behavior.
- strict schema versioning for capability responses.

## Tracking

Every migration PR should include:

1. phase label.
2. capabilities added/removed.
3. changed ownership statement.
4. updated tests and docs.

## Completion Criteria

Roadmap is complete when:

1. direct assistant-side Isabelle execution logic is reduced to UI-only necessities.
2. feature parity is retained or improved.
3. layering rules in `design-documents/02-layering-rules-and-boundaries.md` are enforceable by checks.
