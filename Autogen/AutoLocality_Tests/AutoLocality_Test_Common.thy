(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLocality_Test_Common
  imports Autogen.AutoLocality
begin
(*>*)

section\<open>Shared assertion harness for the AutoLocality regression suite\<close>

text\<open>The themed @{verbatim \<open>AutoLocality_Test_*\<close>} theories share one ML assertion vocabulary,
collected in the structure @{verbatim \<open>AutoLocality_Assert\<close>}. Every assertion is a thunk
@{verbatim \<open>unit -> unit\<close>} that succeeds silently or raises @{verbatim \<open>ASSERT msg\<close>}; a whole themed
section is run via @{verbatim \<open>run_suite\<close>}, which aggregates the failures of all its tests into a
single @{verbatim \<open>error\<close>} (so one broken case does not mask the rest). The harness only ever calls
into the public AutoLocality ML (the ambient simpset, the named generated facts, and the
cancellation simproc), so the tests exercise exactly what downstream proofs see.\<close>

ML\<open>
structure AutoLocality_Assert = struct

  \<comment>\<open>True iff the (parsed) goal closes by the ambient simpset, which includes the default-on
     locality cancellation simprocs. This is the workhorse: it is precisely what a downstream
     @{verbatim \<open>by simp\<close>} would do.\<close>
  fun cancels ctxt (goal_str : string) : bool =
    let val goal = Syntax.read_prop ctxt goal_str in
      (Goal.prove ctxt [] [] goal (fn {context, ...} => asm_full_simp_tac context 1); true)
      handle ERROR _ => false | THM _ => false
    end

  \<comment>\<open>As @{verbatim \<open>cancels\<close>}, but bounded by @{verbatim \<open>ms\<close>} milliseconds; a timeout counts as
     failure. Used by the performance suite to guard against cancellation blowing up.\<close>
  fun cancels_within ctxt (ms : int) (goal_str : string) : bool =
    Timeout.apply (Time.fromMilliseconds (IntInf.fromInt ms)) (fn () => cancels ctxt goal_str) ()
      handle Timeout.TIMEOUT _ => false

  \<comment>\<open>Number of theorems behind a named fact, or @{verbatim \<open>~1\<close>} if the name does not resolve.\<close>
  fun fact_card ctxt (n : string) : int =
    (length (Proof_Context.get_thms ctxt n)) handle ERROR _ => ~1
  fun fact_exists ctxt n = fact_card ctxt n >= 0

  \<comment>\<open>Invoke the cancellation simproc directly on a (parsed) term, bypassing the simpset. Used to
     test the fixpoint / decline behaviour in isolation.\<close>
  fun simproc_on ctxt rec_name attr_name (term_str : string) : thm option =
    locality_cancellation_simproc rec_name attr_name 0 ctxt
      (Thm.cterm_of ctxt (Syntax.read_term ctxt term_str))

  \<comment>\<open>Assertion core. @{verbatim \<open>check\<close>} raises @{verbatim \<open>ASSERT\<close>} on failure; @{verbatim \<open>run_guarded\<close>}
     captures a thunk's outcome as an optional error message, re-raising interrupts so the harness
     never swallows a cancel. @{verbatim \<open>run_suite\<close>} runs a labelled batch and reports pass/fail
     counts, collecting every failure into one error.\<close>
  exception ASSERT of string
  fun check (label : string) (ok : bool) : unit =
    if ok then writeln ("  [OK] " ^ label) else raise ASSERT label

  fun run_guarded (f : unit -> unit) : string option =
    (case Exn.capture f () of
       Exn.Res _ => NONE
     | Exn.Exn e => if Exn.is_interrupt e then Exn.reraise e
                    else SOME (case e of ASSERT m => m | _ => Runtime.exn_message e))

  fun run_suite (suite_name : string) (tests : (string * (unit -> unit)) list) : unit =
    let
      fun run (name, body) = Option.map (fn m => name ^ ": " ^ m) (run_guarded body)
      val failures = List.mapPartial run tests
      val total = length tests
    in
      if null failures then
        writeln ("[PASS] " ^ suite_name ^ ": " ^ Int.toString total ^ "/" ^ Int.toString total)
      else
        error ("[FAIL] " ^ suite_name ^ ": " ^ Int.toString (total - length failures) ^ "/"
               ^ Int.toString total ^ "; failures:\n" ^ cat_lines (map (fn m => "    - " ^ m) failures))
    end

  \<comment>\<open>High-level assertions used by the themed suites.\<close>
  fun assert_cancels ctxt g = check ("cancels: " ^ g) (cancels ctxt g)
  fun assert_does_not_cancel ctxt g = check ("does NOT cancel: " ^ g) (not (cancels ctxt g))
  fun assert_fact ctxt n = check ("fact present: " ^ n) (fact_exists ctxt n)
  fun assert_no_fact ctxt n = check ("fact absent: " ^ n) (not (fact_exists ctxt n))
  fun assert_fact_card ctxt n k =
    check ("fact " ^ n ^ " has " ^ Int.toString k ^ " thm(s)") (fact_card ctxt n = k)

  \<comment>\<open>The three linear lemmas generated for an operation, by record identifier and operation id.\<close>
  fun assert_op_lemmas ctxt rec_id op_id =
    (assert_fact ctxt (rec_id ^ "_local_op_" ^ op_id ^ "_local");
     assert_fact ctxt (rec_id ^ "_local_op_" ^ op_id ^ "_core");
     assert_fact ctxt (rec_id ^ "_local_op_" ^ op_id ^ "_disjoint"))

  \<comment>\<open>The cancellation 'core' lemma generated for an attribute, by record id, attr id, match index.\<close>
  fun assert_attr_lemmas ctxt rec_id attr_id idx =
    assert_fact ctxt (rec_id ^ "_local_attr_" ^ attr_id ^ "_" ^ Int.toString idx ^ "_core")

  \<comment>\<open>The OLD quadratic pre-generation produced a @{verbatim \<open>*_commutativity_facts\<close>} bundle. It must
     no longer exist.\<close>
  fun assert_no_quadratic ctxt rec_id =
    assert_no_fact ctxt (rec_id ^ "_commutativity_facts")

  \<comment>\<open>Fixpoint safety: the simproc declines a normal-form term (returns @{verbatim \<open>NONE\<close>}), so it
     cannot rewrite-and-refire forever.\<close>
  fun assert_simproc_declines ctxt rn an term_str =
    check ("simproc declines: " ^ term_str)
      (case simproc_on ctxt rn an term_str of NONE => true | SOME _ => false)

  \<comment>\<open>The simproc fires and the right-hand side of the resulting meta-equation is alpha-equivalent
     to the parsed @{verbatim \<open>expected_rhs\<close>}. We compare terms with @{verbatim \<open>aconv\<close>}, not printed
     strings: @{verbatim \<open>Syntax.string_of_term\<close>} embeds YXML markup, so a string comparison against a
     plain literal would spuriously fail.\<close>
  fun assert_simproc_cancels_to ctxt rn an term_str expected_rhs =
    check ("simproc cancels " ^ term_str ^ " to " ^ expected_rhs)
      (case simproc_on ctxt rn an term_str of
         NONE => false
       | SOME thm =>
           (case Thm.prop_of thm of
              Const ("Pure.eq", _) $ _ $ rhs => Term.aconv (rhs, Syntax.read_term ctxt expected_rhs)
            | _ => false))

  \<comment>\<open>A thunk is expected to raise (non-interrupt) - e.g. an illegal footprint. Interrupts are
     re-raised so a user cancel is never mistaken for a passing test.\<close>
  fun assert_raises label (thunk : unit -> 'a) =
    check ("raises: " ^ label)
      (case Exn.capture thunk () of
         Exn.Res _ => false
       | Exn.Exn e => if Exn.is_interrupt e then Exn.reraise e else true)

end
\<close>

section\<open>Generative cancellation testing with an independent oracle\<close>

text\<open>The hand-written suites cover specific shapes; this engine covers \<^emph>\<open>breadth\<close>. Given a set of
registered attributes and operations (each described by its name, footprint, and a sample argument),
it enumerates every telescope \<^verbatim>\<open>attr (op1 (op2 ... R))\<close> up to a chosen depth and checks the
cancellation simproc against an \<^emph>\<open>independent\<close> footprint oracle.

The oracle is the key to these being real regression tests rather than tautologies: it recomputes,
purely from footprints, exactly which operations should cancel - an operation cancels iff its
footprint is disjoint from the attribute and from every operation that remains between it and the
attribute. It never consults the simproc. A discrepancy (under-cancellation, over-cancellation, a
wrong residual, a decline-where-cancellation-expected, or vice versa) is a genuine failure of one
side or the other. The same generator is instantiated in different contexts (top level, locale,
interpretation, polymorphic) by the matrix theories, turning a handful of operations and attributes
into hundreds of cases per context.\<close>

ML\<open>
structure AutoLocality_Gen = struct

  \<comment>\<open>An operation or attribute for generation: its (short or qualified) name, its field footprint,
     and a sample argument string for the non-record argument (@{verbatim \<open>""\<close>} if it has none). For
     a locale constant the name carries the applied parameter, e.g. @{verbatim \<open>"bigval bump"\<close>}.\<close>
  type item = { name: string, fp: string list, arg: string }

  \<comment>\<open>Apply an item to a body term-string: @{verbatim \<open>name arg (body)\<close>} or @{verbatim \<open>name (body)\<close>}.\<close>
  fun apply_str ({name, arg, ...}: item) body =
    if arg = "" then name ^ " (" ^ body ^ ")" else name ^ " " ^ arg ^ " (" ^ body ^ ")"

  fun disjoint xs ys = null (inter (op =) xs ys)

  \<comment>\<open>ORACLE. Fold the operation telescope outermost-first, maintaining the union of footprints that
     are 'blocked' (the attribute's, plus every operation kept so far). An operation cancels iff it
     is disjoint from the blocked set; otherwise it stays and extends the blocked set. Returns the
     operations that REMAIN, in order. Independent of the simproc.\<close>
  fun oracle_keep attr_fp (ops : item list) =
    let
      fun go _ [] = []
        | go blocked (item :: rest) =
            if disjoint (#fp item) blocked then go blocked rest
            else item :: go (union (op =) (#fp item) blocked) rest
    in go attr_fp ops end

  \<comment>\<open>LHS term-string: @{verbatim \<open>attr (op\<^sub>1 (\<dots> (op\<^sub>n base)))\<close>}, operations outermost-first.\<close>
  fun build_term (attr : item) (ops : item list) (base : string) =
    apply_str attr (fold_rev apply_str ops base)

  \<comment>\<open>Expected outcome: @{verbatim \<open>NONE\<close>} if the oracle keeps every operation (nothing cancels),
     otherwise @{verbatim \<open>SOME rhs\<close>} with the residual term-string.\<close>
  fun expected (attr : item) (ops : item list) (base : string) =
    let val keep = oracle_keep (#fp attr) ops
    in if length keep = length ops then NONE else SOME (build_term attr keep base) end

  \<comment>\<open>Run one generated case against the simproc; @{verbatim \<open>NONE\<close>} on agreement, @{verbatim \<open>SOME msg\<close>}
     on any disagreement with the oracle. @{verbatim \<open>attr_key\<close>} is the registered attribute name the
     simproc is keyed under (its base name; for a locale attribute this is the bare short name).\<close>
  fun check_case ctxt rec_name attr_key (attr : item) (ops : item list) (base : string)
        : string option =
    let
      val lhs_str = build_term attr ops base
      val got =
        AutoLocality_Assert.simproc_on ctxt rec_name attr_key lhs_str
      val exp = expected attr ops base
    in
      case (exp, got) of
        (NONE, NONE) => NONE
      | (NONE, SOME thm) =>
          SOME (lhs_str ^ ": oracle expects NO cancellation, simproc rewrote to "
                ^ Syntax.string_of_term ctxt (Thm.prop_of thm))
      | (SOME _, NONE) => SOME (lhs_str ^ ": oracle expects cancellation, simproc declined")
      | (SOME rhs_str, SOME thm) =>
          (case Thm.prop_of thm of
             Const ("Pure.eq", _) $ _ $ rhs =>
               if Term.aconv (rhs, Syntax.read_term ctxt rhs_str) then NONE
               else SOME (lhs_str ^ ": simproc RHS disagrees with oracle (oracle = " ^ rhs_str ^ ")")
           | _ => SOME (lhs_str ^ ": simproc result is not a meta-equation"))
    end

  \<comment>\<open>All operation telescopes over @{verbatim \<open>ops\<close>} of length 1 .. max_depth (with repetition and
     order, since order matters to both simproc and oracle).\<close>
  fun telescopes (ops : item list) (max_depth : int) : item list list =
    let
      fun lists 0 = [[]]
        | lists n = maps (fn o1 => map (fn tl => o1 :: tl) (lists (n - 1))) ops
    in maps lists (1 upto max_depth) end

  \<comment>\<open>Generate the full (attribute x telescope) matrix and check every case against the oracle.
     @{verbatim \<open>attr_key_of\<close>} maps an attribute item to the name the simproc is registered under.
     Reports pass/fail via @{ML AutoLocality_Assert.run_suite}, so a single failing case names the
     exact offending term. Returns the number of cases generated.\<close>
  fun run_matrix suite_name ctxt rec_name attr_key_of (attrs : item list) (ops : item list)
        (max_depth : int) (base : string) : int =
    let
      val tels = telescopes ops max_depth
      val cases = maps (fn a => map (fn t => (a, t)) tels) attrs
      val tests =
        map (fn (a, t) =>
          (build_term a t base,
           fn () =>
             case check_case ctxt rec_name (attr_key_of a) a t base of
               NONE => () | SOME m => raise AutoLocality_Assert.ASSERT m))
          cases
      val _ = AutoLocality_Assert.run_suite
                (suite_name ^ " (" ^ Int.toString (length cases) ^ " cases)") tests
    in length cases end

end
\<close>

(*<*)
end
(*>*)
