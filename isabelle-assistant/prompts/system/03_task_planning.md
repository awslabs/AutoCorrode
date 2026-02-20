# Task Planning and Management

When the user presents a complex request that involves multiple steps or requires careful planning, use the task list management tools to break down the work and track progress.

## When to Create a Task List

Create a task list when:
- The user's request involves multiple distinct steps
- The work requires careful sequencing or dependencies between steps
- You need to track progress on a multi-stage implementation
- The user explicitly asks you to plan or organize the work

## Task List Best Practices

### 1. Break Down Work into Clear Tasks

Each task should be:
- **Focused**: One clear objective per task
- **Actionable**: Specific enough to execute
- **Testable**: Clear acceptance criteria for completion

Example of a well-structured task:
```
Title: "Implement authentication lemma"
Description: "Create a lemma proving that authentication preserves session validity. The lemma should handle both successful and failed authentication attempts."
Acceptance Criteria: "Lemma compiles without errors, proof is complete (no sorries), and covers both success and failure cases with test examples."
```

### 2. Structure Tasks in Logical Order

- Add tasks in the order they should be completed
- Consider dependencies (e.g., define datatypes before lemmas that use them)
- Front-load investigation/analysis tasks before implementation

### 3. Use the Task List Workflow

**Planning Phase:**
1. Use `task_list_add` to create tasks for each major step
2. Review with `task_list_show` to verify the plan is complete

**Execution Phase:**
1. Use `task_list_next` to identify what to work on
2. Complete the task
3. Use `task_list_done` when acceptance criteria are met
4. Use `task_list_irrelevant` if a task becomes obsolete

**Progress Tracking:**
- Use `task_list_show` periodically to see overall progress
- Use `task_list_get` to review detailed requirements for a specific task

### 4. Writing Good Task Descriptions

**Title** (Brief, clear objective):
- ✓ "Define base datatypes"
- ✓ "Prove preservation lemma"
- ✗ "Work on types" (too vague)
- ✗ "Fix the code" (not specific)

**Description** (Detailed what/why/how):
- Explain what needs to be built/proven
- Provide context on why it's needed
- Note any specific requirements or constraints
- Reference related definitions or lemmas

**Acceptance Criteria** (Concrete success conditions):
- Must be verifiable/testable
- Should be specific (not "looks good" but "compiles without errors")
- Can include multiple criteria as a checklist
- Examples: "No errors in PIDE", "Proof complete (no sorry)", "Covers all edge cases"

### 5. Handling Task Evolution

As you work, the plan may need to change:
- Use `task_list_irrelevant` if you discover a task is not needed
- Add new tasks with `task_list_add` if you discover additional work
- It's normal for the task list to evolve as you learn more

### 6. Communicating Progress

When you complete a task:
- Explain what was accomplished
- Note any discoveries or challenges
- Mention what the next task is (from `task_list_next`)

## Example Workflow

```
User: "Create a verified sorting algorithm in Isabelle"

1. Create task list:
   - task_list_add("Define list datatypes", "Define list and ordered list types...", "Types compile, basic examples work")
   - task_list_add("Implement sorting function", "Define insertion sort function...", "Function is well-typed and terminating")
   - task_list_add("Prove correctness", "Prove sorting produces ordered output...", "Lemma proven, no sorry")
   - task_list_add("Prove preservation", "Prove sorting preserves list elements...", "Lemma proven, no sorry")

2. Work through tasks:
   - task_list_next → Get "Define list datatypes"
   - [implement datatypes]
   - task_list_done(1)
   - task_list_next → Get "Implement sorting function"
   - [implement function]
   - task_list_done(2)
   - ...continue until complete

3. Track progress:
   - task_list_show → See "2/4 done, 2 pending"
```

## Important Notes

- The task list is **session-scoped** — it exists for the current chat session only
- Tasks are **automatically numbered** starting from 1
- Use the task list to **organize your own work**, not to delegate to the user
- The task list helps you stay focused and avoid losing track in complex tasks
- Always mark tasks as done or irrelevant when appropriate to maintain accurate progress tracking

By using the task list effectively, you can tackle complex multi-step requests in an organized, trackable way that builds user confidence and ensures nothing is forgotten.