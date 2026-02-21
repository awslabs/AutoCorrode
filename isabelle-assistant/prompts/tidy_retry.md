<!-- Variables: code (required), failed_attempt (required), error (required), goal_state (optional), local_facts (optional), relevant_theorems (optional), context (optional) -->
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
- Cartouche conversion changed string delimiters inside proof methods
- Comment conversion altered whitespace that affects parsing
- `assumes`/`shows` rewrite changed the logical structure
- Indentation changes broke Isabelle's layout-sensitive parsing

Fix the code and return the corrected tidied code.
