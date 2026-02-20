# Task Planning

Use task-list tools for genuinely multi-step work. Do not create overhead for simple one-step requests.

## When to Use Task Lists
- Use task lists when work has dependencies, multiple files, or a staged verification process.
- Skip task lists for trivial read-only questions or single small edits.

## Task Quality Rules
- Each task must have:
  - a concrete objective,
  - a concise implementation description,
  - explicit acceptance criteria tied to observable outcomes (for example: “no PIDE errors”, “proof complete without sorry”).
- Keep tasks small enough to complete in one focused pass.

## Execution Discipline
1. Plan:
   - Create tasks with `task_list_add`.
   - Check coverage with `task_list_show`.
2. Execute:
   - Pull next work item via `task_list_next`.
   - Complete, verify, then mark with `task_list_done`.
3. Adapt:
   - Add newly discovered work as new tasks.
   - Mark obsolete tasks with `task_list_irrelevant`.

## Isabelle-Specific Acceptance Criteria
- Prefer acceptance criteria that include:
  - successful proof state progression (`execute_step` / `verify_proof`),
  - final diagnostic checks (`set_cursor_position` to EOF + `get_errors`),
  - maintainable proof shape (not only “works once”).

## Reporting
- After each completed task, summarize what changed and what remains.
- Keep progress reports factual and brief.
