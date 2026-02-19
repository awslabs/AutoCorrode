<!-- Variables: code (required), failed_attempt (required), error (required) -->
Your tidied code failed verification:
```
{{error}}
```

Original:
```isabelle
{{code}}
```

Your attempt:
```isabelle
{{failed_attempt}}
```

Common issues to check:
- Cartouche conversion changed string delimiters inside proof methods
- Comment conversion altered whitespace that affects parsing
- `assumes`/`shows` rewrite changed the logical structure
- Indentation changes broke Isabelle's layout-sensitive parsing

Fix the code. You MUST respond with exactly a single JSON object containing the tidied code, ensuring newlines and quotes are properly escaped:

```json
{
  "code": "lemma foo: ‹P ⟹ Q›\n..."
}
```

CRITICAL: The output MUST be strictly valid JSON. Do NOT add any conversational text before or after the JSON block.
