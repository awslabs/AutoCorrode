<!-- Variables: lemma_statement (required), full_proof (required), selected_text (required), goal_state (optional), local_facts (optional), relevant_theorems (optional), context (optional) -->
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

## Referenced Definitions
```isabelle
{{context}}
```
{{/context}}

Extract the selected steps into a separate lemma. Return the extracted lemma code and the updated proof that uses it.
