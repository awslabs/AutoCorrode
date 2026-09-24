# AutoLocality

--- TODO: This should be a machine-checked theory file, not Markdown. ---

AutoLocality is AutoCorrode's automation for reasoning about functions on
records. Its purpose is simple: The user states once which record fields a function can
observe or change, then let Isabelle remove state updates that cannot affect
the current observation.

For example, if `set_counter` touches only `counter` and `in_mode` reads only
`mode`, then AutoLocality lets the ordinary simplifier prove:

```isabelle
lemma ‹in_mode (set_counter n R) = in_mode R›
  by simp
```

A simple approach to achieve this is to pre-generate such a "cancellation lemmas"
for every pair of functions with disjoint footprint. This, however, is inefficient
from a complexity and memory usage perspective since the number of such cancellation
lemmas is quadratic in the number of operations.

The present implementation does not populate the theory with every possible pairwise
commutativity and cancellation theorem. Instead, it stores a linear set of checked
"certificates for each registered function and constructs the cancellation and/or
commutativity lemmas at simplification time using a simproc. For a fixed record width, this
keeps declaration cost and theory data proportional to the number of
registered functions rather than the number of pairs of functions.

The executable implementation and its design notes are in
[AutoLocality.thy](AutoLocality.thy); the regression theories live under
`AutoLocality_Tests/`.

## The problem AutoLocality solves

Large state models commonly contain:

- **operations**, which return an updated record;
- **attributes**, which observe a record and return another type; and
- long pipelines of operations under an attribute.

Each operation and attribute has a **footprint**. For an attribute, the
footprint contains every field it reads. For an operation, it contains every
field it reads or writes. The combined read-and-write interpretation matters:
two disjoint operation footprints are sufficient to show that the operations
commute, while an operation disjoint from an attribute cannot change the
attribute's result.

Suppose:

```isabelle
attr (outer (irrelevant R))
```

`irrelevant` can be removed when:

1. its footprint is disjoint from the footprint of `attr`; and
2. it can cross every operation between itself and `attr`.

AutoLocality discovers that cancellation at simplification time. It can keep
operations that matter, commute an irrelevant operation past compatible
blockers, and then cancel it at the attribute. A failed or inapplicable
attempt simply leaves the term unchanged.

The user remains responsible for declaring the footprint. AutoLocality proves
certificates for that declaration before registering it, so an incorrect
under-approximation normally fails at the `locality_lemma` proof. A safe
over-approximation is allowed, but may prevent valid cancellations.

## Quick start

Import `AutoLocality`, define the state functions, and register their
footprints:

```isabelle
theory Example
  imports AutoLocality
begin

datatype_record machine_state =
  mode :: nat
  counter :: nat

definition set_counter ::
    ‹nat ⇒ machine_state ⇒ machine_state› where
  ‹set_counter n ≡ update_counter (λ_. n)›

definition set_mode ::
    ‹nat ⇒ machine_state ⇒ machine_state› where
  ‹set_mode n ≡ update_mode (λ_. n)›

definition in_mode :: ‹machine_state ⇒ bool› where
  ‹in_mode R ≡ mode R > 0›

locality_lemma for machine_state:
  ‹set_counter› footprint [counter] .

locality_lemma for machine_state:
  ‹set_mode› footprint [mode] .

locality_lemma for machine_state:
  ‹in_mode› footprint [mode] .

lemma ‹in_mode (set_counter n R) = in_mode R›
  by simp

end
```

The first `locality_lemma` initializes the record automatically. Explicit
`locality_init` is useful when the locality registrations for generated field
selectors and updaters must exist before any user-defined function is
registered.

Plain `simp` includes AutoLocality cancellation by default. `simp only`
deliberately starts without the ambient simprocs, so add
`[[locality_cancel]]` when cancellation is wanted:

```isabelle
lemma ‹in_mode (set_counter n R) = in_mode R›
  by (simp only: [[locality_cancel]])
```

## Concepts and terminology

### Operations

An operation has exactly one argument matching the record type and returns
that record type, possibly with additional non-record arguments:

```isabelle
set_counter :: nat ⇒ machine_state ⇒ machine_state
```

Its footprint includes all fields that its result may depend on or modify.

### Attributes

An attribute observes one or more arguments matching the record type. In
ordinary use it returns a non-record result:

```isabelle
in_mode  :: machine_state ⇒ bool
between  :: nat ⇒ machine_state ⇒ nat ⇒ bool
related  :: machine_state ⇒ machine_state ⇒ bool
```

Each record argument is registered separately when an attribute observes more
than one record.

The operation classifier requires exactly one record-typed argument and a
record result. A function that returns the record but has multiple
record-typed arguments therefore falls through to the attribute path. This is
a known modelling boundary, not support for multi-record state updates.

### Generated field operations

`locality_init` registers each generated record selector as an attribute and
each generated record updater as an operation. Users therefore do not need
`locality_lemma` declarations for ordinary field selectors and updaters.

## Commands and attributes

### `locality_init`

Syntax:

```isabelle
locality_init for record_type
```

This command:

- registers the record's generated selectors and updaters;
- creates the record's `<record>_locality_facts` named-theorem bundle; and
- declares the required named cancellation dispatchers in the active local
  theory.

Initialization is idempotent. It is also performed implicitly by the first
`locality_lemma` for a record.

### `locality_lemma`

General syntax:

```isabelle
locality_lemma for record_type
  [(no_proof)]
  [fact_attributes]:
  term [record_match_index]
  footprint [field_1, ..., field_n]
  proof
```

The common forms are:

```isabelle
locality_lemma for machine_state:
  ‹set_counter› footprint [counter] .

locality_lemma for machine_state:
  ‹in_mode› footprint [mode] .
```

AutoLocality classifies the term from its type, generates the linear
certificates needed for later proof construction, and first attempts to prove
them automatically. A trailing `.` is enough when that attempt succeeds. If
goals remain, continue with an ordinary Isar proof.

Use `(no_proof)` to suppress the initial automatic attempt:

```isabelle
locality_lemma for machine_state (no_proof):
  ‹manual_operation› footprint [counter]
  by (auto simp add: manual_operation_def)
```

`record_match_index` selects among the term's record-typed arguments, not
among all arguments. It defaults to `0`. Thus an attribute whose sole record
argument is its second ordinary argument still uses `[0]`, while an attribute
with two record arguments uses `[0]` and `[1]` in separate declarations:

```isabelle
definition related ::
    ‹machine_state ⇒ machine_state ⇒ bool› where
  ‹related L R ≡ mode L < counter R›

locality_lemma for machine_state:
  ‹related› [0] footprint [mode] .

locality_lemma for machine_state:
  ‹related› [1] footprint [counter] .
```

The registered term may be a typed or partial application. Distinct rigid
prefixes can have distinct footprints:

```isabelle
locality_lemma for machine_state:
  ‹policy_attribute mode_policy› footprint [mode]
  by (auto simp add: policy_attribute_def mode_policy_def)
```

Inside a locale, register locale-defined constants from a `context` re-entry
after their definitions are complete, and use their short names. The
registration is morphism-aware and follows locale interpretations. The
dispatcher declaration stays with that owning local theory; it is not
installed by leaving the locale, modifying the background theory, and
re-entering the locale.

When `[fact_attributes]` is omitted, generated public certificates are added
to the record's `<record>_locality_facts` bundle. Supplying attributes directs
the generated facts to those attributes instead; the explicit attributes
replace, rather than supplement, the default bundle annotation.

### Automatic cancellation with `simp`

Cancellation is enabled in the ambient simpset:

```isabelle
lemma ‹in_mode (set_counter n R) = in_mode R›
  by simp
```

The same applies to nested operation pipelines. AutoLocality removes only
operations that are irrelevant to the observation and can be moved across
the intervening operations.

This automation is for an **attribute over operations**. It does not
arbitrarily reorder a bare term such as `op_a (op_b R)`.

### `[[locality_cancel]]`

This fact attribute enables cancellation and restores any registered local
dispatchers missing from the current simpset. The restoration matters for
`simp only:`, which clears the ambient simpset before processing its explicit
arguments.

Typical uses:

```isabelle
by (simp only: [[locality_cancel]])
```

or:

```isabelle
context
  notes [[locality_cancel]]
begin

...

end
```

It is usually unnecessary with plain `simp`, because cancellation is enabled
by default. Repeated activation is idempotent: it does not duplicate raw
simprocs.

### `[[locality_no_cancel]]`

This fact attribute disables AutoLocality cancellation in its scope:

```isabelle
lemma ‹in_mode (set_counter n R) = in_mode R›
  supply [[locality_no_cancel]]
  by (simp add: in_mode_def set_counter_def)
```

This is useful for controls, diagnostics, and proofs whose own rewrite set
must determine the normal form. It changes a context configuration flag; it
does not remove inherited simproc declarations. Disabled callbacks return
immediately.

### `[[locality_autocancellation ...]]`

Syntax:

```isabelle
[[locality_autocancellation
    operation attribute relative_record_index]]
```

The record type is inferred from the operation and indexed-attribute
registrations. If the same polymorphic constants are registered for more than
one record, disambiguate explicitly:

```isabelle
[[locality_autocancellation
    (record_type) operation attribute relative_record_index]]
```

This derives and returns one generalized operation/attribute cancellation
theorem without registering or caching it:

```isabelle
lemma ‹in_mode (set_counter n R) = in_mode R›
  by (rule [[locality_autocancellation
    set_counter in_mode 0]])
```

It is most useful in `simp only` proofs that need one explicit cancellation:

```isabelle
by (simp only:
  [[locality_autocancellation
      set_counter in_mode 0]])
```

Here the index is the attribute's record argument position relative to the
arguments remaining after any prefix supplied by the context. Locale
parameters already supplied by the context do not count. This differs from
`locality_lemma`'s `record_match_index`, which selects among record-typed
arguments.

The operation and attribute positions accept named constants, not arbitrary
terms. An explicit fact therefore cannot directly name a rigid partial
application such as `policy_attribute mode_policy`; use ambient `simp` or
introduce a named wrapper constant for that case.

Ordinary proofs should prefer plain `simp`; needing this attribute routinely
is a sign that cancellation is being requested in a restricted simpset or
that automatic dispatcher coverage should be investigated.

### `[[locality_autocommutativity ...]]`

Syntax:

```isabelle
[[locality_autocommutativity
    operation_a operation_b]]
```

The record type is inferred from the records carrying matching registrations
for both operations. If that intersection contains more than one record,
disambiguate explicitly:

```isabelle
[[locality_autocommutativity
    (record_type) operation_a operation_b]]
```

This derives and returns one generalized theorem saying that two registered
operations commute:

```isabelle
lemma
  ‹set_mode m (set_counter n R) =
   set_counter n (set_mode m R)›
  by (rule [[locality_autocommutativity
    set_mode set_counter]])
```

It can also be named or supplied to the simplifier:

```isabelle
lemmas mode_counter_commute =
  [[locality_autocommutativity
      set_mode set_counter]]

lemma ...
  by (simp add:
    [[locality_autocommutativity
        set_mode set_counter]])
```

The attribute fails if the registrations are missing or the requested
commutativity cannot be proved. It does not alter the ambient simpset.

Both operation positions accept named constants. To request commutativity for
a rigid partial application, introduce a named wrapper constant.

### `locality_check`

Syntax:

```isabelle
locality_check
locality_check for record_type
```

This diagnostic scans visible operations and attributes involving the
selected record, prints whether each has footprint information, and warns
about unregistered user constants. With no record argument, it checks every
record already known to AutoLocality.

It does not create registrations.

### `print_locality_data`

Syntax:

```isabelle
print_locality_data
print_locality_data for record_type
```

This prints registered terms, selected record arguments, and footprints. Use
it to inspect typed or partial registrations and to confirm which record slot
was selected.

## Diagnostic configuration

Tracing is disabled by default. Positive values increase verbosity:

```isabelle
declare [[locality_trace_level = 1]]
```

Declaration-time proof timing is also off by default:

```isabelle
declare [[locality_timing = true]]
```

`locality_timing` reports the phases used to establish registration
certificates. It is a diagnostic setting, not a benchmarking interface.

## What to expect from the simplifier

AutoLocality should:

- cancel disjoint operations under registered attributes with plain `simp`;
- preserve operations whose footprints overlap the attribute;
- cross an intervening operation only when the required commutativity is
  proved;
- preserve extra arguments, including arguments after function-valued record
  selectors;
- respect typed partial applications and locale interpretations; and
- decline safely when no justified rewrite exists.

AutoLocality does not:

- infer footprints from definitions;
- automatically normalize every operation/operation ordering;
- make overlapping footprints commute;
- add on-demand pairwise theorems permanently to the context; or
- use a process-global theorem cache.

## Further examples

The most direct executable examples are:

- [AutoLocality_Test_Cancel.thy](AutoLocality_Tests/AutoLocality_Test_Cancel.thy)
  for plain-`simp` cancellation;
- [AutoLocality_B0_Base.thy](AutoLocality_Tests/AutoLocality_B0_Base.thy)
  for explicit cancellation and commutativity facts;
- [AutoLocality_Test_Shapes.thy](AutoLocality_Tests/AutoLocality_Test_Shapes.thy)
  for argument positions, polymorphism, and function-valued selectors;
- [AutoLocality_Test_Locale.thy](AutoLocality_Tests/AutoLocality_Test_Locale.thy)
  for locale declarations and interpretations;
- [AutoLocality_Test_Perf.thy](AutoLocality_Tests/AutoLocality_Test_Perf.thy)
  for deep-telescope structural performance guards; and
- [AutoLocality_Test_Wide.thy](AutoLocality_Tests/AutoLocality_Test_Wide.thy)
  for wide records and the counted buried-hoist regression.
