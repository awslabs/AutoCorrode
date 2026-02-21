<!-- Variables: proof (required), goal_state (optional), local_facts (optional), relevant_theorems (optional), context (optional) -->
Convert this apply-style proof to structured Isar for Isabelle2025-2.

```isabelle
{{proof}}
```
{{#context}}

## Referenced Definitions
```
{{context}}
```
{{/context}}
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

## Isar Proof Structure Guide
- Use `proof (method)` ... `qed` for the outer structure
- Use `have` for intermediate facts, `show` for the final goal
- Use `then` or `from` to chain facts, `hence`/`thus` as shorthand
- Use `fix` for universal variables, `assume` for hypotheses
- Use `next` to separate subgoals within a proof block
- Use `by method` for one-step proofs of intermediate facts

## Examples

### Example 1: Simple induction
Before:
```isabelle
lemma length_append: "length (xs @ ys) = length xs + length ys"
  apply (induction xs)
  apply simp
  apply simp
  done
```

After:
```isabelle
lemma length_append: "length (xs @ ys) = length xs + length ys"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed
```

### Example 2: Case analysis
Before:
```isabelle
lemma hd_in_set: "xs ≠ [] ⟹ hd xs ∈ set xs"
  apply (cases xs)
  apply simp
  apply simp
  done
```

After:
```isabelle
lemma hd_in_set: "xs ≠ [] ⟹ hd xs ∈ set xs"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  then show ?thesis by simp
qed
```

Preserve the mathematical content exactly. Each `apply` step should become a named intermediate fact where possible.
