# Isabelle Proof Style and Quality

Produce proofs that are robust under maintenance, easy to read, and consistent with idiomatic Isar.

## Structural Preferences
- Prefer Isar-structured proofs (`proof - ... qed`) over long `apply` chains.
- Prefer hypothetical reasoning blocks `{ ... }` over deeply nested inner `proof` blocks when both are clear.
- Preserve and follow existing style in the file being edited.
- Use meaningful intermediate facts with `have`, `then`, `from`, `moreover`, and `ultimately`.
- Keep proofs local and compositional: prove small facts, then combine them.
- Use explicit introduction/elimination style (`rule`, `erule`, `cases`, `induct`) when it improves clarity.

## Statement and Context Discipline
- Use `assumes` / `fixes` / `shows` where appropriate for readable theorem statements.
- For multiple assumptions or fixed variables in one statement, prefer `and`-chaining over repeating `assumes`/`fixes`.
- Reuse assumptions by name instead of relying on fragile positional reasoning.
- Prefer context-aware structuring (`context ... begin`, local lemmas, named theorem collections) when the surrounding theory uses it.
- Follow local naming patterns for rule families (for example `...I`, `...E`, `...iff`, `..._wrap`) when introducing companion lemmas.
- Use cartouches (`‹...›`) for Isabelle text syntax.

## Automation Discipline
- Use automation (`simp`, `auto`, `blast`, `metis`) intentionally, not as a blind fallback.
- Treat `auto` / `simp_all` as terminal clean-up steps, not the default first move.
- Avoid brittle one-line `metis`/`smt` proofs when a short structured derivation is clearer.
- If simplification behavior matters, control simpsets explicitly (for example with local `simp del` / `simp add`).
- Keep attributes (`[simp]`, `[intro]`, `[elim]`, named theorem sets) intentional and consistent with nearby theory style.

## Editing and Formatting
- Keep edits minimal and scoped to the user’s request.
- Keep theory text and comments informative; use `text‹...›` / `\<comment>‹...›` instead of ML comments for narrative.
- Maintain clean spacing and readable block layout.
- Use two-space indentation consistently for proof/script layout.
- Keep the proof for a claim on the next line (indented) after the claim line.
- Keep exactly one blank line between top-level declarations (definitions, lemmas, theorems, sectioning commands).

## Response Format
- When suggesting code the user might insert, wrap it in ```isabelle fences.
- If giving alternatives, present the primary recommendation first and explain tradeoffs briefly.

## Chat Rendering Conventions
- The chat UI supports Markdown; use standard headings, lists, emphasis, and tables where useful.
- The chat UI renders LaTeX math with `$...$` (inline) and `$$...$$` (display).
- Prefer ```isabelle code fences for snippets intended for insertion.
