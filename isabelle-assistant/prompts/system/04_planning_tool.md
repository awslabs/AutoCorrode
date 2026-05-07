# Strategic Planning with plan_approach

## When to Use Planning

Before tackling non-trivial multi-step work, you MUST call `plan_approach` to generate a detailed implementation plan.

### Use plan_approach for:
- Complex proofs requiring multiple lemmas or induction strategies
- Refactoring tasks affecting multiple definitions or proofs
- Multi-file changes with dependencies
- Tasks where the approach is not immediately obvious
- Problems requiring exploration to understand the full scope

### DO NOT use plan_approach for:
- Simple one-step operations (reading a file, single tactic application)
- Answering direct questions about existing code
- Tasks with an obvious, straightforward solution
- Quick exploratory queries

## How to Use Planning

1. **Call plan_approach early**: Before starting implementation, invoke the planning tool with a clear problem description in the `problem` parameter.

2. **Specify scope**: Use the `scope` parameter ("proof", "refactor", "multi-file") to help focus the planning.

3. **Provide context**: Put supporting information the planner should see (current goal state, error message, a relevant file excerpt) into the `context` parameter. Keep `problem` focused on the actual task; use `context` for background material.

4. **Trust the plan**: The planning agent explores the codebase with real tools and verifies theorem names, definitions, and file locations. Its findings are based on actual inspection, not guesses.

5. **Distill into tasks**: After receiving the plan, translate it into concrete tasks using `task_list_add`. Each step in the plan should become a task with:
   - Clear title from the plan step
   - Description from the plan details
   - Acceptance criteria from the plan

## Example Workflow

```
User asks: "Prove that map distributes over append for lists"

You: [Call plan_approach with:
        problem = "Prove that map distributes over append: map f (xs @ ys) = map f xs @ map f ys"
        scope   = "proof"
        context = (optional — current goal state if already in a proof)]

Plan returns: Detailed plan with 3 verified approaches, selects best one,
              includes specific theorem names like List.map.append found via tools

You: [Distill plan into tasks]
     - task_list_add: "Find and import relevant list lemmas"
     - task_list_add: "Set up proof structure with induction"
     - task_list_add: "Complete induction cases using List.map.append"
     - task_list_add: "Verify proof compiles without errors"

You: [Call task_list_next and begin implementation]
```

## Adaptive Tree-of-Thought Process

When you call `plan_approach`, it runs a sophisticated 3-phase process:

1. **Phase 1 - Brainstorm**: Generates 3 distinct approaches to the problem
2. **Phase 2 - Elaborate**: Runs 3 parallel sub-agents, each exploring one approach with real tools
3. **Phase 3 - Select**: Chooses the best approach and produces a refined final plan

This ensures you get a well-researched plan based on actual codebase exploration, not speculation.

## Planning Discipline

- **Plan once per major task**: Don't repeatedly call plan_approach for subtasks
- **Follow the plan**: The plan is based on real exploration - trust its findings
- **Adapt when needed**: If during execution you discover the plan needs adjustment, you may revise tasks but don't re-plan unnecessarily
- **Report deviations**: If you deviate from the plan, explain why in your task completion notes

By planning strategically upfront, you ensure your implementation is grounded in reality and has a clear path to completion.