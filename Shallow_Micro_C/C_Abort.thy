(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Abort
  imports
    "Shallow_Micro_Rust.Core_Expression"
begin

section \<open>C-Specific Abort Types\<close>

text \<open>
  C programs can exhibit undefined behavior that we model as explicit aborts.
  The \<open>c_abort\<close> datatype below captures the specific kinds of undefined behavior
  that our C semantics detects, and is used to instantiate the core monad's
  @{typ "'abort"} parameter via @{const CustomAbort}.
\<close>

datatype c_abort =
    NullPointerDereference
  | BufferOverflow
  | SignedOverflow
  | DivisionByZero
  | UseAfterFree
  | ShiftOutOfRange

text \<open>
  Convenience abbreviations for aborting with specific C undefined behaviors.
  These produce expressions of type @{typ "('s, 'v, 'r, c_abort, 'i, 'o) expression"}.
\<close>

definition c_abort :: \<open>c_abort \<Rightarrow> ('s, 'v, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_abort reason \<equiv> abort (CustomAbort reason)\<close>

definition c_null_pointer_dereference :: \<open>('s, 'v, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_null_pointer_dereference \<equiv> c_abort NullPointerDereference\<close>

definition c_buffer_overflow :: \<open>('s, 'v, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_buffer_overflow \<equiv> c_abort BufferOverflow\<close>

definition c_signed_overflow :: \<open>('s, 'v, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_signed_overflow \<equiv> c_abort SignedOverflow\<close>

definition c_division_by_zero :: \<open>('s, 'v, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_division_by_zero \<equiv> c_abort DivisionByZero\<close>

definition c_use_after_free :: \<open>('s, 'v, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_use_after_free \<equiv> c_abort UseAfterFree\<close>

definition c_shift_out_of_range :: \<open>('s, 'v, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>c_shift_out_of_range \<equiv> c_abort ShiftOutOfRange\<close>

end
