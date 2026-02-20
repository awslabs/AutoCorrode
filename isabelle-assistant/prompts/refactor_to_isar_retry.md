<!-- Variables: proof (required), failed_attempt (required), error (required), goal_state (optional), local_facts (optional), relevant_theorems (optional), context (optional) -->
Your previous Isar proof failed verification:
```
{{error}}
```

Original apply-style proof:
```isabelle
{{proof}}
```

Failed attempt:
```isabelle
{{failed_attempt}}
```
{{#goal_state}}

Current goal state:
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

Common issues to check:
- Missing `then`/`from` chains between intermediate facts
- Incorrect `show` statement not matching the actual subgoal
- Missing `next` between subgoals in a structured proof
- Using `have` where `show` is needed (or vice versa)
- Proof methods that work in apply-style but need adjustment in Isar

Fix the proof. You MUST respond with exactly a single JSON object containing the refactored code, ensuring newlines and quotes are properly escaped:

```json
{
  "code": "lemma foo:\nproof\n  ...\nqed"
}
```

CRITICAL: The output MUST be strictly valid JSON. Do NOT add any conversational text before or after the JSON block.
