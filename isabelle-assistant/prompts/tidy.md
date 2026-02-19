<!-- Variables: code (required) -->
Tidy up this Isabelle code without changing its meaning.

```isabelle
{{code}}
```

Apply these transformations:
- Replace "..." quotes with ‹...› cartouches
- Replace (* ... *) comments with text ‹...› (block) or ― ‹...› (marginal one-liner)
- Rewrite lemma/theorem statements to use `assumes`, `fixes`, `shows` instead of bare implications
  e.g. `lemma foo: ‹P ⟹ Q›` becomes `lemma foo: assumes ‹P› shows ‹Q›`
- Use flat indentation (proof body indented once, not by depth)
- Trim trailing whitespace

## Examples

### Example 1: Quotes to cartouches
Before: `lemma "x + 0 = x"`
After: `lemma ‹x + 0 = x›`

### Example 2: Comments
Before: `(* This is a comment *)`
After: `text ‹This is a comment›`

Before: `lemma foo: "P" (* inline comment *)`
After: `lemma foo: ‹P› ― ‹inline comment›`

### Example 3: Assumes/shows
Before:
```isabelle
lemma append_assoc: "xs ≠ [] ⟹ length (xs @ ys) = length xs + length ys"
```

After:
```isabelle
lemma append_assoc:
  assumes ‹xs ≠ []›
  shows ‹length (xs @ ys) = length xs + length ys›
```

### Example 4: Multiple premises
Before:
```isabelle
lemma "P ⟹ Q ⟹ R"
```

After:
```isabelle
lemma
  assumes ‹P› ‹Q›
  shows ‹R›
```

Do NOT change proof structure, methods, or convert apply-style to Isar.

You MUST respond with exactly a single JSON object containing the tidied code, ensuring newlines and quotes are properly escaped:

```json
{
  "code": "lemma foo: ‹P ⟹ Q›\n..."
}
```

CRITICAL: The output MUST be strictly valid JSON. Do NOT add any conversational text before or after the JSON block.
