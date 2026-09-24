(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_C1_Locale_Retention
  imports Autogen.AutoLocality
begin
(*>*)

section\<open>Collector-free locale interpretation retention\<close>

datatype_record retention_state =
  retention_left :: nat
  retention_right :: nat

locality_init for retention_state

definition retention_set_right ::
    \<open>nat \<Rightarrow> retention_state \<Rightarrow> retention_state\<close> where
  \<open>retention_set_right n \<equiv>
    update_retention_right (\<lambda>_. n)\<close>

locality_lemma for retention_state:
  \<open>retention_set_right\<close> footprint [retention_right] .

locale retention_family =
  fixes delta :: nat
begin

definition retention_op ::
    \<open>retention_state \<Rightarrow> retention_state\<close> where
  \<open>retention_op R \<equiv>
    update_retention_left (\<lambda>n. n + delta) R\<close>

definition retention_attr :: \<open>retention_state \<Rightarrow> bool\<close> where
  \<open>retention_attr R \<equiv> delta < retention_left R\<close>

end

context retention_family begin

locality_lemma for retention_state:
  \<open>retention_op\<close> footprint [retention_left] .

locality_lemma for retention_state:
  \<open>retention_attr\<close> footprint [retention_left] .

end

ML\<open>
structure AutoLocality_C1_Locale_Retention =
struct

open AutoLocality_Instrumentation

val retention_dispatch_head =
  "AutoLocality_C1_Locale_Retention.retention_family.retention_attr"

val retention_operation_head =
  "AutoLocality_C1_Locale_Retention.retention_family.retention_op"

val retention_record_name =
  "AutoLocality_C1_Locale_Retention.retention_state"

fun assert_interpretation_state interpretations ctxt =
  let
    val inventory_entries =
      LocalityDispatcherInventory.get (Context.Proof ctxt)
      |> LocalityDispatchKeyTable.dest
      |> filter (fn (key, _) =>
           #head_name key = retention_dispatch_head)
    val raw_dispatchers =
      Raw_Simplifier.simpset_of ctxt
      |> Raw_Simplifier.dest_ss
      |> #simprocs
    val semantic_entries =
      get_record_locality_entries retention_record_name ctxt
    fun semantic_count kind head_name =
      semantic_entries
      |> filter (fn entry =>
           locality_entry_kind entry = kind
           andalso #const_name entry = head_name)
      |> length
    val _ =
      (case (interpretations, inventory_entries) of
         (0, []) => ()
       | (_, [(_, entry)]) =>
           let
             val alias = #alias entry
             val checked_alias =
               #1 (Simplifier.check_simproc
                 ctxt (alias, Position.none))
             val matching_raw =
               raw_dispatchers
               |> filter (fn (name, _) =>
                    name = #source_name entry)
           in
             if checked_alias = alias
                andalso length matching_raw = 1
             then ()
             else
               error ("Retention dispatcher identity changed after "
                 ^ Int.toString interpretations
                 ^ " interpretations")
           end
       | _ =>
           error "Unexpected retention dispatcher inventory shape")
    val _ =
      if semantic_count Locality_Operation retention_operation_head =
           interpretations
         andalso semantic_count Locality_Attribute retention_dispatch_head =
           interpretations
      then ()
      else
        error "Retention semantic entry count changed unexpectedly"
  in
    ()
  end

fun statistic properties name =
  (case AList.lookup (op =) properties name of
    NONE => error ("Missing ML statistic " ^ quote name)
  | SOME text =>
      (case IntInf.fromString text of
        NONE =>
          error ("Malformed ML statistic " ^ quote name ^ ": " ^ quote text)
      | SOME value =>
          if value < 0 then
            error ("Negative ML statistic " ^ quote name ^ ": " ^ quote text)
          else (text, value)))

fun sample interpretations thy ctxt =
  let
    val run_id = current_run_id ctxt
    val _ =
      if run_id = disabled_run_id andalso run_id = 0 then ()
      else error "AutoLocality retention sampling requires disabled instrumentation"
    val _ = assert_interpretation_state interpretations ctxt
    val _ = Thm.consolidate_theory thy
    val _ = ML_Heap.full_gc ()
    val properties = ML_Statistics.get ()
    val ((size_heap_raw, size_heap),
         (size_heap_free_last_full_gc_raw, size_heap_free_last_full_gc)) =
      (statistic properties "size_heap",
       statistic properties "size_heap_free_last_full_GC")
    val live_bytes = size_heap - size_heap_free_last_full_gc
    val _ =
      if live_bytes >= 0 then ()
      else
        error ("Inconsistent ML heap statistics: size_heap=" ^
          size_heap_raw ^ " size_heap_free_last_full_GC=" ^
          size_heap_free_last_full_gc_raw)
  in
    writeln ("[AUTOLOCALITY_RETENTION] interpretations=" ^
      Int.toString interpretations ^ " live_bytes=" ^
      IntInf.toString live_bytes)
  end

end
\<close>

ML\<open>
  AutoLocality_C1_Locale_Retention.sample 0 \<^theory> \<^context>
\<close>

subsection\<open>Interpretations 1--16\<close>

global_interpretation retention_01: retention_family 1 .
global_interpretation retention_02: retention_family 2 .
global_interpretation retention_03: retention_family 3 .
global_interpretation retention_04: retention_family 4 .
global_interpretation retention_05: retention_family 5 .
global_interpretation retention_06: retention_family 6 .
global_interpretation retention_07: retention_family 7 .
global_interpretation retention_08: retention_family 8 .
global_interpretation retention_09: retention_family 9 .
global_interpretation retention_10: retention_family 10 .
global_interpretation retention_11: retention_family 11 .
global_interpretation retention_12: retention_family 12 .
global_interpretation retention_13: retention_family 13 .
global_interpretation retention_14: retention_family 14 .
global_interpretation retention_15: retention_family 15 .
global_interpretation retention_16: retention_family 16 .

lemma retention_16_cancellation:
  shows \<open>retention_16.retention_attr
      (retention_set_right n (retention_16.retention_op R)) =
    retention_16.retention_attr (retention_16.retention_op R)\<close>
  by simp

ML\<open>
  AutoLocality_C1_Locale_Retention.sample 16 \<^theory> \<^context>
\<close>

subsection\<open>Interpretations 17--32\<close>

global_interpretation retention_17: retention_family 17 .
global_interpretation retention_18: retention_family 18 .
global_interpretation retention_19: retention_family 19 .
global_interpretation retention_20: retention_family 20 .
global_interpretation retention_21: retention_family 21 .
global_interpretation retention_22: retention_family 22 .
global_interpretation retention_23: retention_family 23 .
global_interpretation retention_24: retention_family 24 .
global_interpretation retention_25: retention_family 25 .
global_interpretation retention_26: retention_family 26 .
global_interpretation retention_27: retention_family 27 .
global_interpretation retention_28: retention_family 28 .
global_interpretation retention_29: retention_family 29 .
global_interpretation retention_30: retention_family 30 .
global_interpretation retention_31: retention_family 31 .
global_interpretation retention_32: retention_family 32 .

lemma retention_32_cancellation:
  shows \<open>retention_32.retention_attr
      (retention_set_right n (retention_32.retention_op R)) =
    retention_32.retention_attr (retention_32.retention_op R)\<close>
  by simp

ML\<open>
  AutoLocality_C1_Locale_Retention.sample 32 \<^theory> \<^context>
\<close>

subsection\<open>Interpretations 33--48\<close>

global_interpretation retention_33: retention_family 33 .
global_interpretation retention_34: retention_family 34 .
global_interpretation retention_35: retention_family 35 .
global_interpretation retention_36: retention_family 36 .
global_interpretation retention_37: retention_family 37 .
global_interpretation retention_38: retention_family 38 .
global_interpretation retention_39: retention_family 39 .
global_interpretation retention_40: retention_family 40 .
global_interpretation retention_41: retention_family 41 .
global_interpretation retention_42: retention_family 42 .
global_interpretation retention_43: retention_family 43 .
global_interpretation retention_44: retention_family 44 .
global_interpretation retention_45: retention_family 45 .
global_interpretation retention_46: retention_family 46 .
global_interpretation retention_47: retention_family 47 .
global_interpretation retention_48: retention_family 48 .

lemma retention_48_cancellation:
  shows \<open>retention_48.retention_attr
      (retention_set_right n (retention_48.retention_op R)) =
    retention_48.retention_attr (retention_48.retention_op R)\<close>
  by simp

ML\<open>
  AutoLocality_C1_Locale_Retention.sample 48 \<^theory> \<^context>
\<close>

subsection\<open>Interpretations 49--64\<close>

global_interpretation retention_49: retention_family 49 .
global_interpretation retention_50: retention_family 50 .
global_interpretation retention_51: retention_family 51 .
global_interpretation retention_52: retention_family 52 .
global_interpretation retention_53: retention_family 53 .
global_interpretation retention_54: retention_family 54 .
global_interpretation retention_55: retention_family 55 .
global_interpretation retention_56: retention_family 56 .
global_interpretation retention_57: retention_family 57 .
global_interpretation retention_58: retention_family 58 .
global_interpretation retention_59: retention_family 59 .
global_interpretation retention_60: retention_family 60 .
global_interpretation retention_61: retention_family 61 .
global_interpretation retention_62: retention_family 62 .
global_interpretation retention_63: retention_family 63 .
global_interpretation retention_64: retention_family 64 .

lemma retention_64_cancellation:
  shows \<open>retention_64.retention_attr
      (retention_set_right n (retention_64.retention_op R)) =
    retention_64.retention_attr (retention_64.retention_op R)\<close>
  by simp

ML\<open>
  AutoLocality_C1_Locale_Retention.sample 64 \<^theory> \<^context>
\<close>

(*<*)
end
(*>*)
