<!-- Variables: selected_text (required), failed_lemma (required), failed_proof (required), error (required) -->
Lemma extraction failed verification:
```
{{error}}
```

Selected steps to extract:
```isabelle
{{selected_text}}
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
