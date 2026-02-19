<!-- Variables: lemma_statement (required), full_proof (required), selected_text (required), goal_state (optional) -->
Extract the selected proof steps into a separate lemma.

## Original Lemma
```isabelle
{{lemma_statement}}
```

## Full Proof
```isabelle
{{full_proof}}
```

## Selected Steps
```isabelle
{{selected_text}}
```
{{#goal_state}}

## Goal State at Selection
```
{{goal_state}}
```
{{/goal_state}}

You MUST respond with exactly a single JSON object containing two fields, ensuring newlines and quotes are properly escaped:

```json
{
  "extracted_lemma": "lemma name: \"statement\"\n  <proof>",
  "updated_proof": "<original lemma updated to use extracted lemma>"
}
```

CRITICAL: The output MUST be strictly valid JSON. Do NOT add any conversational text before or after the JSON block.
