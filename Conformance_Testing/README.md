# Micro Rust Conformance Testing

This directory contains the conformance framework that checks Micro Rust (μRust) semantics against real Rust execution.

## Purpose

The conformance suite is designed to:

- evaluate expected behaviour from Micro Rust definitions in Isabelle/HOL
- execute equivalent Rust expressions/tests in `cargo test`
- fail when HOL and Rust behaviour diverge
- produce auditable coverage summaries
- block CI when conformance or coverage gates fail

## Core Strategy

Expected results are computed from HOL evaluation of Micro Rust functions, not from reimplemented expected-value logic in SML.

At a high level:

1. test inputs are generated (edge cases + deterministic random data)
2. HOL terms are evaluated to compute expected outcomes
3. Rust tests are generated with embedded expected values/assertions
4. Rust tests are executed with `cargo test`
5. coverage summaries are emitted (`json` + `markdown`) and checked for required categories

## Current Test Categories

Unified generation is defined in:

- `Conformance_Testing/Tests/Generate_All.thy`

Required categories currently enforced:

- `arithmetic`
- `bitwise`
- `comparison`
- `conversion`
- `panic`
- `stdlibarith`
- `option`
- `result`
- `range`
- `ordering`
- `tuple`

Category generators currently included:

- `Conformance_Testing/Tests/Arithmetic_Conformance.thy`
- `Conformance_Testing/Tests/Bitwise_Conformance.thy`
- `Conformance_Testing/Tests/Comparison_Conformance.thy`
- `Conformance_Testing/Tests/Conversion_Conformance.thy`
- `Conformance_Testing/Tests/Panic_Conformance.thy`
- `Conformance_Testing/Tests/StdLib_Arithmetic_Conformance.thy`
- `Conformance_Testing/Tests/Option_Conformance.thy`
- `Conformance_Testing/Tests/Result_Conformance.thy`
- `Conformance_Testing/Tests/Range_Conformance.thy`
- `Conformance_Testing/Tests/Ordering_Conformance.thy`
- `Conformance_Testing/Tests/Tuple_Conformance.thy`

## API Coverage Status (Current)

### Option

Covered:

- `option_expect`
- `option_unwrap`
- `urust_func_option_is_none`
- `urust_func_option_is_some`
- `ok_or`

Not yet covered by conformance tests:

- `option_as_mut`
- `take_mut_ref_option`

### Result

Covered:

- `result_expect`
- `result_unwrap`
- `urust_func_result_is_err`
- `urust_func_result_is_ok`
- `result_or`
- `map_err`
- `ok`
- `result_unwrap_or`

Not yet covered by conformance tests:

- `result_as_mut`

### Range

All public definitions in:

- `Shallow_Micro_Rust/Range_Type.thy`

are covered, including:

- `range_into_list`
- `make_iterator_from_range`
- `range_into_iter`
- indexing and range-slicing operations with value and abort paths

### Tuple

Covered:

- `list_zip` from `Micro_Rust_Std_Lib/StdLib_Tuple.thy`

## Running

From repository root:

```bash
make conformance-gen
make conformance-test
```

Or run end-to-end:

```bash
make conformance
```

## CI Gate

CI runs conformance as a blocking gate via:

- `.github/workflows/ci.yml`

step:

- `make conformance ISABELLE_HOME=$ISABELLE_HOME`

If generation, coverage checks, or Rust conformance tests fail, CI fails.

## Artifacts

Generated outputs:

- `Conformance_Testing/rust_harness/src/lib.rs`
- `Conformance_Testing/rust_harness/coverage_summary.json`
- `Conformance_Testing/rust_harness/coverage_summary.md`

These are generated artifacts and not source-of-truth.

## Coverage Summary

Coverage summaries are produced by:

- `Conformance_Testing/coverage.ML`

They include:

- total module/test counts
- category module/test counts
- tracked type counts (`u8`, `u16`, `u32`, `u64`)
- per-module breakdown
- panic expectation counts for panic modules

## Extending the Suite

To add new conformance material:

1. add a generator theory in `Conformance_Testing/Tests/`
2. expose `generate_all_tests ctxt num_random`
3. import the theory in `Generate_All.thy`
4. wire it into `Conformance_Gen.generate_all_tests`
5. add its category to `required_categories` if it represents a new required dimension
6. include the theory in `Conformance_Testing/ROOT`
