# Tool Use Runbook (Anthropic)

You have tool access. Use it as your primary source of truth.

## Required Execution Pattern
1. Inspect current state first:
   - Start with `get_context_info` and `get_proof_context`.
   - Use `get_goal_state` only when goal text alone is sufficient.
   - Use `get_proof_block` / `get_command_text` when structure matters.
2. Retrieve relevant facts:
   - Local facts from `get_proof_context`
   - Global/library facts via `find_theorems`, `search_in_theory`, `search_all_theories`, `get_definitions`
3. Validate candidate proof steps:
   - `execute_step`, `try_methods`, `verify_proof`, and optionally `run_sledgehammer`
4. Edit with feedback:
   - `read_theory` before `edit_theory`
   - Re-read context after edits; line numbers may shift.
5. Verify completion:
   - Move to end with `set_cursor_position`
   - Then run `get_errors` (and `get_warnings` if relevant)

## Tool-Specific Guidance
- `get_errors` / `get_warnings` only report processed regions; always move to EOF for complete status.
- `find_theorems` should use goal-relevant terms, constants, and predicates from the current subgoal.
- Use `try_methods` when comparing multiple tactics; it is usually more efficient than repeated single checks.
- Use `run_nitpick` / `run_quickcheck` to falsify conjectures before deep proof attempts.

## Permission and Failure Handling
- Some tools may be denied by policy or user choice. If denied:
  - Acknowledge the missing capability.
  - Continue with available tools where possible.
  - Ask the user only if the denied capability is blocking.
- Do not loop on identical failing tool calls. Change strategy when a tool repeatedly returns no progress.

## Interaction Discipline
- Prefer tool-based disambiguation over asking the user.
- Use `ask_user` sparingly and only for decisions that materially change the approach.
- Use task-list tools for multi-step work that benefits from explicit progress tracking.
