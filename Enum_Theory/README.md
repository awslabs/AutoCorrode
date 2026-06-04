# Enum_Theory: Enumeration Type Support for AutoCorrode

## Overview

The `Enums` theory provides infrastructure for defining enumeration types in Isabelle/HOL with automatic theorem generation. It supports both simple enumerations (nullary constructors only) and complex enumerations (constructors with arguments).

## Functionality

### The `enum` Command

**Syntax:**
```isabelle
enum <type_name> = 
  <constructor1> [<type1> ... <typeN>]
| <constructor2> [<type1> ... <typeM>]
| ...
```

### Automatically Generated Theorems

For each enum type, the following theorems are automatically generated:

1. **Induction Principle** (`typ.induct`)
   - Structural induction over the enum type
   - Format: `⟦ P C1; P C2; ... ⟧ ⟹ P x`
   - Automatically registered for use with `case_tac` and `cases` tactics

2. **Case Combinator** (`typ.case`)
   - Pattern matching eliminator
   - Type: `'a → ... → 'a → typ → 'a` (simple enum)
   - Type: `(t1 → ... → tn → 'a) → ... → typ → 'a` (complex enum)

3. **Case Equality Theorems** (`typ.cases`)
   - Simplification rules for case expressions
   - Automatically added to the simplifier with `[simp]` attribute
   - Format: `case f1 ... fn (Ci x1 ... xk) = fi x1 ... xk`

4. **Type Classification** (`typ.is_enum`)
   - `typ.is_enum`: Theorem proving `True` for all enum types
   - Used for programmatic type introspection in ML
   - Enables the `enum_neq_simproc` to automatically prove constructor inequalities

### Simple Enums

Simple enums have only nullary constructors and are represented as finite subsets of natural numbers.

**Example:**
```isabelle
enum color = Red | Green | Blue
```

**Generated:**
- Constructors: `color.Red`, `color.Green`, `color.Blue`
- Type: `color` (typedef over `{0, 1, 2}`)
- Theorems: `color.induct`, `color.case_def`, `color.cases`, `color.is_enum`

### Complex Enums

Complex enums have constructors with arguments and are represented as sum-of-products types.

**Example:**
```isabelle
enum result = Success nat | Failure string | Pending
```

**Generated:**
- Constructors: `result.Success`, `result.Failure`, `result.Pending`
- Type: `result` (typedef over `nat + string + unit`)
- Theorems: `result.induct`, `result.case_def`, `result.cases`, `result.is_enum`

### Pattern Matching Integration

The case combinators are automatically registered with Isabelle's pattern matching translation, enabling idiomatic case expressions:

```isabelle
lemma "case x of Red ⇒ 1 | Green ⇒ 2 | Blue ⇒ 3 = 
       color.case 1 2 3 x"
  by (simp add: color.case_def)
```

### Tactic Integration

The induction principle is automatically registered with Isabelle's case analysis system, enabling the use of standard tactics:

```isabelle
(* Using cases tactic in Isar *)
lemma "c = Red ∨ c = Green ∨ c = Blue"
  apply (cases c)
  by auto

(* Using case_tac tactic in apply-style proofs *)
lemma "c = Red ∨ c = Green ∨ c = Blue"
  apply (case_tac c)
  by auto

(* Using structured Isar proof *)
lemma "⟦ P Red; P Green; P Blue ⟧ ⟹ P c"
proof (cases c)
  case Red
  then show ?thesis by assumption
next
  case Green
  then show ?thesis by assumption
next
  case Blue
  then show ?thesis by assumption
qed
```

## Implementation Details

### Architecture

The implementation consists of two ML functions:

1. **`enum_cmd_simpl`**: Handles simple enums (nullary constructors only)
   - Uses typedef over `{..<n}` (lessThan) where `n` is the number of constructors
   - Each constructor is defined as `Abs i` for index `i`
   - Efficient representation with direct natural number mapping
   - Induction proof uses arithmetic reasoning with `less_SucE` for scalability

2. **`enum_cmd_complex`**: Handles complex enums (with constructor arguments)
   - Uses typedef over sum-of-products type
   - Each constructor is defined as `Abs (Inl/Inr (x1, ..., xn))`
   - Supports arbitrary argument types for constructors
   - Special handling for singleton enums (no sum type needed)

### Key ML Modules

- **`enum_cmd.ML`**: Main implementation
  - `Enum_Cmd` structure with signature `ENUM_CMD`
  - Functions: `enum_cmd_simpl`, `enum_cmd_complex`, `enum_cmd`
  - Helper functions: `get_type_thm_local`, `has_is_enum_thm`, `get_ctor_def`
  - Simproc: `enum_neq_simproc` for automatic inequality proofs
  - Command parser registration via `Outer_Syntax.local_theory`
  - Built-in timing instrumentation for performance monitoring

### Type Representation

**Simple enum** (`n` constructors):
```
typedef typ = "{..<n}"  (* i.e., {x. x < n} *)
C_i = Abs i
```

Example for n=3:
```isabelle
typedef color = "{..<3}"  (* equivalent to {0, 1, 2} *)
Red = color.Abs 0
Green = color.Abs 1
Blue = color.Abs 2
```

**Complex enum** (constructors with argument types `T1, T2, ..., Tn`):
```
typedef typ = "UNIV :: (T1 + (T2 + ... + Tn))"
C_i x1 ... xk = Abs (Inl^i (x1, ..., xk))
```

Special case for singleton (n=1):
```
typedef typ = "UNIV :: T1"
C x1 ... xk = Abs (x1, ..., xk)
```

### Proof Strategy

**Simple enum induction:**
1. Apply `Abs_induct` from typedef
2. Unfold all constructor definitions
3. Clarify and simplify to expose constraint `x < n`
4. Repeatedly apply `less_SucE` to eliminate successor cases
5. Solve each case by assumption or simplification
   - This scales efficiently to large enums (O(n) rather than O(2^n) for disjunction elimination)

**Complex enum induction:**
1. Apply `Abs_induct` from typedef
2. Unfold all constructor definitions
3. For n=1: Just clarify and simplify (no sum type)
4. For n>1: Repeatedly apply `sum.exhaust` to split on sum type constructors
5. Clarify and simplify each case

**Case equality theorems:**
- Proven by unfolding case definition and constructor definitions
- Use `Abs_inverse` theorem from typedef
- Simplification handles tuple destructuring

### Simproc for Inequality

The `enum_neq_simproc` automatically proves inequalities between different enum constructors:
- Matches on terms of form `x ≠ y`
- Checks if the type has `is_enum` marker theorem
- Retrieves `Abs_inject` and constructor definitions
- Simplifies to prove inequality (different natural numbers or sum injections)

### Integration Points

1. **Case_Translation**: Registers case combinators for pattern matching syntax
2. **Simplifier**: Adds case equality theorems with `[simp]` attribute
3. **Induct.cases_type**: Registers induction theorem as cases rule for `case_tac` and `cases` tactics
4. **Naming conventions**: All generated constants/theorems use qualified names (`typ.X`)

## Files

- **`Enum_Theory.thy`**: Main theory file, imports `enum_cmd.ML` and provides the enum command
- **`enum_cmd.ML`**: Implementation of the enum command
- **`Enum_Tests.thy`**: Comprehensive test suite (not included in ROOT)
- **`ROOT`**: Session definition for the Enums session

## Usage

Import the theory in your Isabelle development:

```isabelle
theory MyTheory
imports "Enum_Theory.Enum_Theory"
begin

enum status = Running | Stopped | Error string

(* Use the generated theorems *)
lemma "⟦ P Running; P Stopped; ⋀s. P (Error s) ⟧ ⟹ P x"
  by (rule status.induct)

end
```

If you need to use the fully qualified path (e.g., from another session):
```isabelle
imports "AutoCorrode.Enum_Theory.Enum_Theory"
```

## Limitations

- Enums are **monomorphic** (no type parameters)
- Enums are **non-recursive** (cannot refer to the type being defined)
- Constructor argument types must be existing types
- No automatic generation of distinctness or injectivity theorems (future work)

## Future Enhancements

- Injectivity theorems for constructors with arguments
- Exhaustiveness lemmas
- Derive type class instances (e.g., `enum`, `finite`)
