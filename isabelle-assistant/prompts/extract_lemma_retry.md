<!-- Variables: selected_text (required), full_proof (required), lemma_statement (required), goal_state (optional), failed_lemma (required), failed_proof (required), error (required), local_facts (optional), relevant_theorems (optional), context (optional) -->
Lemma extraction failed verification:
```
{{error}}
```

Selected steps to extract:
```isabelle
{{selected_text}}
```
{{#goal_state}}

Goal state at selection:
```
{{goal_state}}
```
{{/goal_state}}
{{#local_facts}}

Local facts:
```
{{local_facts}}
```
{{/local_facts}}
{{#relevant_theorems}}

Potentially relevant facts (MePo/find_theorems):
```
{{relevant_theorems}}
```
{{/relevant_theorems}}
{{#context}}

Referenced definitions:
```isabelle
{{context}}
```
{{/context}}

Original enclosing lemma statement:
```isabelle
{{lemma_statement}}
```

Full original proof block:
```isabelle
{{full_proof}}
```

Failed extraction:
### EXTRACTED_LEMMA
```isabelle
{{failed_lemma}}
```

### UPDATED_PROOF
```isabelle
{{failed_proof}}
```

Common issues to check:
- Extracted lemma statement doesn't match what the selected steps actually prove
- Updated proof references the extracted lemma with wrong name or wrong arguments
- Free variables in the extracted lemma need to be universally quantified
- The extracted lemma needs additional assumptions from the enclosing context

Fix the extraction. You MUST respond with exactly a single JSON object containing the corrected fields, ensuring newlines and quotes are properly escaped:

```json
{
  "extracted_lemma": "<corrected lemma code>",
  "updated_proof": "<corrected proof code>"
}
```

CRITICAL: The output MUST be strictly valid JSON. Do NOT add any conversational text before or after the JSON block.
