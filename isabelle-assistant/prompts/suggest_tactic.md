<!-- Variables: proof_pattern (required), goal_state (optional), local_facts (optional), relevant_theorems (optional), context (optional) -->
You are an Isabelle/HOL expert (Isabelle2025-2). Generate an Eisbach method that automates this proof pattern.

## Proof Pattern
```isabelle
{{proof_pattern}}
```
{{#goal_state}}

## Goal State At Cursor
```
{{goal_state}}
```
{{/goal_state}}
{{#local_facts}}

## Local Facts
```
{{local_facts}}
```
{{/local_facts}}
{{#relevant_theorems}}

## Potentially Relevant Facts (MePo/find_theorems)
```
{{relevant_theorems}}
```
{{/relevant_theorems}}
{{#context}}

## Context
```isabelle
{{context}}
```
{{/context}}

## Eisbach Syntax Reference
- `method name = (tactic)` — simple method
- `method name uses thms = (tactic)` — method with theorem arguments
- `method name for x = (tactic)` — method with term arguments
- Combinators: `;` (then), `|` (or), `?` (try/optional), `+` (repeat 1+), `*` (repeat 0+)
- `match` expressions for goal-directed tactics

## Design Guidelines
- Use `uses` when the method needs caller-supplied lemmas (e.g., simp rules)
- Prefer `?` over bare methods to make the tactic more robust
- Use `+` or `*` for repeated application (e.g., `(simp; fail)+`)
- Combine methods with `;` for sequential application
- Use `|` for fallback alternatives (try fast method first, then slower)

## Examples
```
method my_induct_simp = (induction, simp+)
method my_crush uses rules = (auto simp: rules | force simp: rules)
method my_cases for x = (cases x; simp_all?)
method solve_arith = (linarith | arith | simp)
```

Output ONLY the method definition line. No explanation, no examples, no markdown code fences, no backticks. Just the raw `method ...` line.
