# Micro C Examples

This directory contains end-to-end examples of translating C11 into AutoCorrode Core and verifying the generated definitions with weakest-precondition proofs.

Start with [`Simple_C_Functions.thy`](Simple_C_Functions.thy), then use the other files as focused case studies:

- [`C_Struct_Examples.thy`](C_Struct_Examples.thy): struct layout and pointer-to-struct field updates.
- [`C_Array_Examples.thy`](C_Array_Examples.thy): array indexing, loop invariants, and memory-style fill/copy routines.
- [`C_Bitwise_Examples.thy`](C_Bitwise_Examples.thy): bitwise arithmetic and shift-side conditions.
- [`C_While_Examples.thy`](C_While_Examples.thy): while-loop reasoning with explicit fuel discharge and break/continue behavior.
- [`C_ABI_Examples.thy`](C_ABI_Examples.thy): ABI-sensitive translation examples for wire data (portable big-endian parsing vs native cast loads), with specs/lemmas for parser correctness and host-endian conversion, plus ABI-driven byte-prism selection.

The examples reuse the locale setup from `Simple_C_Functions.thy` (reference allocation, dereference, and update operations), so each theory can focus on proof structure rather than locale boilerplate.
