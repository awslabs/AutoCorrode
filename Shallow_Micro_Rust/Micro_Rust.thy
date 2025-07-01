(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Micro_Rust
  imports
    Bool_Type Bool_Type_Lemmas Core_Expression Core_Expression_Lemmas Core_Syntax Result_Type 
    Option_Type Range_Type Rust_Iterator Rust_Iterator_Lemmas Numeric_Types
    Numeric_Types_Lemmas Global_Store SSA Micro_Rust_Shallow_Embedding
begin
(*>*)

section\<open>Entry point for Micro Rust\<close>

text\<open>This theory's main purpose is to import all of the material related to Core Micro Rust.  It
also serves as a point where common material (for example, automation routines) can be placed.\<close>

(*<*)
end
(*>*)
