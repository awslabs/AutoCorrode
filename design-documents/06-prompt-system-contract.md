# Prompt System Contract

Status: Draft steering document  
Applies to: `isabelle-assistant` prompt loading and delivery  
Last reviewed: 2026-02-21

## Purpose

This document defines reliability and governance requirements for system prompts used by Isabelle Assistant.

## Prompt Stack

System prompts are composed from ordered files in:

- `isabelle-assistant/prompts/system/_index.txt`
- `isabelle-assistant/prompts/system/*.md`

Current ordered baseline:

1. `00_core_operating_rules.md`
2. `01_isabelle_style.md`
3. `02_tools.md`
4. `03_task_planning.md`

## Loading and Fallback Contract

Prompt loading (`PromptLoader`) must provide reliable fallback behavior:

1. load from `ISABELLE_ASSISTANT_HOME` when available.
2. fall back to classpath prompt resources.
3. fall back to built-in minimal baseline if no prompt files are found.

Failure to find external prompts must not silently remove core operating rules.

## Normative Prompt Content

System prompt stack must always communicate:

- non-fabrication and verification-first behavior.
- Isabelle proof style and formatting conventions.
- tool execution runbook and failure handling.
- planning discipline for multi-step tasks.
- chat rendering capabilities (Markdown, LaTeX, Mermaid).

## Change Management Rules

Any prompt change must include:

1. rationale for behavioral impact.
2. explicit note of added/removed constraints.
3. tests or checks validating prompt composition order and non-empty delivery.

## Regression Risks to Guard Against

- Losing style constraints during prompt rewrites.
- Losing tool-use safety instructions.
- Losing rendering guidance that affects user comprehension.
- Empty or partial prompt delivery when environment variables differ.

## Testing Expectations

Tests should cover:

- index parsing and ordering behavior.
- fallback resolution paths.
- invariant that the final system prompt is non-empty.
- inclusion of required sections under normal deployment.

## Acceptance Checks

A prompt-related change is accepted only when:

1. system prompt transport remains reliable across installation modes.
2. required guidance categories remain present.
3. prompt ordering remains deterministic.
