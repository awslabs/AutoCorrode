# Feature Matrix and Capability Map

Status: Active steering document  
Applies to: `iq`, `isabelle-assistant`  
Last reviewed: 2026-02-21

## Purpose

This document maps user-facing features to system capabilities and dependencies.

## Capability Providers

- `isabelle-assistant`: UI actions, chat commands, rendering, orchestration.
- `iq`: Isabelle-side tools and MCP interfaces.
- Isabelle runtime: proof checking and document processing.
- AWS Bedrock: model inference and tool-calling behavior.

## Feature Map

| Feature group | User surface | Primary owner | Depends on I/Q | Depends on Bedrock |
| --- | --- | --- | --- | --- |
| Freeform chat | Dockable chat panel | isabelle-assistant | No (optional for richer grounding) | Yes |
| Explain and summarize actions | Context menu and chat commands | isabelle-assistant | Optional | Yes |
| Proof suggestions | Context menu and `:suggest` | isabelle-assistant orchestration | Optional for verification | Yes |
| Proof verification | Verification badges and retries | iq capability + assistant presentation | Yes | Optional |
| Find theorems and proof exploration | Tools/actions | iq capability + assistant orchestration | Yes | Optional |
| Theory read/search navigation | Tools/actions | assistant buffer APIs + iq-backed reads where available | Optional | Optional |
| Theory edits/creation via model tools | tool use | assistant permission gate + jEdit buffer/file operations (migration debt) | No | Yes |
| Permission gating | settings + runtime prompts | isabelle-assistant | No | No |

## User-Facing Preconditions

- Bedrock-backed model and credentials are required for LLM generation.
- Full verification/proof search capabilities require I/Q availability.
- Prompt resources must be available through installation or classpath fallback.

## Degraded Modes

Expected degraded operation:

- If I/Q unavailable: chat and non-I/Q actions still function, verification is marked unavailable.
- If model unavailable: deterministic non-LLM tooling can still run where supported.
- If specific tools denied: assistant continues with available tools and reports limitations.

## Discoverability Requirements

- Every right-click action should have a corresponding documented chat command where practical.
- Settings UI must clearly show effectful options, especially model and tool permission controls.
- Verification state must be visible and unambiguous to the user.

## Acceptance Checks

A new feature is accepted only when:

1. ownership and dependencies are documented in this matrix.
2. degraded behavior is explicitly defined.
3. user-visible entry point and status reporting are clear.
