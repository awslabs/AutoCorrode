(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory AutoLens
  imports AutoCommon "Lenses_And_Other_Optics.Lenses_And_Other_Optics" "HOL-Library.Datatype_Records"
begin
(*>*)

section\<open>Auto-generation of record field lenses and foci\<close>

text\<open>Every field of a datatype has associated with it a lens and a focus encapsulating
the record field projection and update functions.

This section develops various ML functions supporting the autogeneration of those lenses/foci
and the automatic derivation of their basic properties.\<close>

subsection\<open>Miscellaneous helpers\<close>

ML\<open>
   \<comment>\<open>Lookup theorem (list) by name.

   TODO: This probably already exists in the standard library?\<close>
   exception LOOKUP of string
   fun lookup_thms ctxt thm_name =
    let val thm_opt = Facts.lookup (Context.Proof ctxt)
                                   (Proof_Context.facts_of ctxt)
                                   thm_name in
          case thm_opt of
            SOME thm => thm |> #thms
          | NONE => raise LOOKUP thm_name
        end
   fun lookup_thm ctxt thm_name = lookup_thms ctxt thm_name |> List.hd

   \<comment>\<open>Find the definitional theorem for a constant\<close>
   fun lookup_def ctxt = Thm.def_name #> lookup_thm ctxt

   \<comment>\<open>Find the definitional theorem for a constant, or return NONE if it doesn't exist.\<close>
   fun lookup_def_opt ctxt c =
      (SOME (lookup_def ctxt c) handle LOOKUP _ => NONE)
  
   \<comment>\<open>Find destination type of term\<close>
   fun tm_body_type (ctxt : Proof.context) =
     Thm.cterm_of ctxt #> Thm.typ_of_cterm #> Term.body_type
   
   \<comment>\<open>Check if a type can unify with another without being a type schematic\<close>
   fun could_unify_not_generic (rec_ty : typ) (tst_ty : typ) : bool =
     Type.could_unify (rec_ty, tst_ty) andalso (not (Term.is_TVar tst_ty))

   \<comment>\<open>Checks which binder/argument types inf \<^verbatim>\<open>ty_src\<close> are unifiable with the
   target type \<^verbatim>\<open>ty_tgt\<close>. Returns the list of indices of these arguments, alongside
   the total number of type arguments in \<^verbatim>\<open>ty_src\<close>.\<close>
   fun find_matching_args (ty_tgt : typ) (ty_src : typ) =
     let
       val args = ty_src |> Term.binder_types
       val num_args = length args
     in
       (num_args,
          args
        |> Library.map_index (could_unify_not_generic ty_tgt |> apsnd)
        |> List.filter snd
        |> List.map fst)
     end

   \<comment>\<open>Checks if \<^verbatim>\<open>ty_src\<close> is the type of an 'attribute' on the (record) type \<^verbatim>\<open>ty_tgt\<close>,
   in the sense that exactly one type argument in \<^verbatim>\<open>ty_src\<close> unifies with \<^verbatim>\<open>ty_tgt\<close>,
   and the target type does not.\<close>
   fun is_attr_ty_on (ty_tgt : typ) (ty_src : typ) : bool =
     let
       val body_match = could_unify_not_generic ty_tgt (Term.body_type ty_src)
     in
       (not body_match) andalso (List.length (find_matching_args ty_tgt ty_src |> snd) = 1)
     end

   \<comment>\<open>Checks if \<^verbatim>\<open>ty_src\<close> is the type of an 'operation' on the (record) type \<^verbatim>\<open>ty_tgt\<close>,
   in the sense that exactly one type argument in \<^verbatim>\<open>ty_src\<close> unifies with \<^verbatim>\<open>ty_tgt\<close>,
   and the target type matches, too.\<close>
   fun is_fun_ty_on (ty_tgt : typ) (ty_src : typ) =
     let
       val ty_h = Term.body_type ty_src
       val body_match = could_unify_not_generic ty_tgt ty_h
     in
       body_match andalso List.length (find_matching_args ty_tgt ty_src |> snd) = 1
     end

   \<comment>\<open>Given a term \<^verbatim>\<open>t\<close> and target type \<^verbatim>\<open>ty\<close>, return the head of the term, the number of arguments,
      and the list of argument indices which match \<^verbatim>\<open>ty\<close>. If there is no such argument, return \<^verbatim>\<open>NONE\<close>.\<close>
   fun dest_attr_term (ctxt : Proof.context) (ty : typ) (t : term) : (string * int * int list) option =
      let
        val t_ty = t |> Thm.cterm_of ctxt |> Thm.typ_of_cterm
        val head = t |> Term.head_of |> Term.term_name
        val (num_args, matching_args) = find_matching_args ty t_ty
      in
        case matching_args of
           [] => NONE
         | e => SOME (head, num_args, e)
      end

  val _ = dest_attr_term @{context} @{typ nat} @{term \<open>x y :: 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'c\<close>}
  \<comment>\<open>\<^verbatim>\<open>SOME ("x", 4, [1, 2]): (string * int * int list) option\<close>\<close>

   \<comment>\<open>Given a term \<^verbatim>\<open>t\<close> and target type \<^verbatim>\<open>ty\<close>, if the target type of \<^verbatim>\<open>t\<close> matches \<^verbatim>\<open>ty\<close> and
      exactly one argument type of \<^verbatim>\<open>t\<close> also matches \<^verbatim>\<open>ty\<close>, return the triple of head term,
      total number of arguments, and matching argument index. Otherwise, return NONE.\<close>
   fun dest_fun_term (ctxt : Proof.context) (ty : typ) (t : term) : (string * int * int) option =
      let val tgt = tm_body_type ctxt t
          val t = dest_attr_term ctxt ty t
          val head_match = could_unify_not_generic tgt ty
      in
        case (head_match, t) of
           (true, SOME (head, num_args, [i])) => SOME (head, num_args, i)
         | _ => NONE
      end

   val _ = dest_fun_term @{context} @{typ nat} @{term \<open>x y :: 'a \<Rightarrow> nat  \<Rightarrow> 'b \<Rightarrow> nat\<close>}
   \<comment>\<open>\<^verbatim>\<open>SOME ("x", 3, 1): (string * int * int) option\<close>\<close>
   val _ = dest_fun_term @{context} @{typ nat} @{term \<open>x y :: 'a \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> nat\<close>}
   \<comment>\<open>\<^verbatim>\<open>NONE: (string * int * int) option\<close>\<close>
   val _ = dest_fun_term @{context} @{typ nat} @{term \<open>x y :: 'a \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> bool\<close>}
   \<comment>\<open>\<^verbatim>\<open>NONE: (string * int * int) option\<close>\<close>

   \<comment>\<open>Checks whether the string \<^verbatim>\<open>t\<close> denotes a constant with a definition.\<close>
   fun is_const_with_def (ctxt : Proof.context) (t : string) : bool =
     Syntax.read_term ctxt t
     |> Term.dest_Const
     |> fst
     |> lookup_def_opt ctxt
     |> Option.isSome
     handle TERM _ => false

   fun make_arglist_with_prefix prefix (num_args : int) =
     let
       fun make_arglist_core acc _ 0 = acc
         | make_arglist_core acc base n =
             make_arglist_core (acc @ [prefix ^ Int.toString base]) (base + 1) (n - 1)
     in
       make_arglist_core [] 0 num_args
     end

   val make_arglist = make_arglist_with_prefix "arg"

   \<comment>\<open>Update the ith entry of a list\<close>
   fun list_set_nth (i : int) (x : 'a) = nth_map i (K x)

   \<comment>\<open>Looks up a datatype record in the given context, and returns the list of fields\<close>
   fun get_fields rec_name thy = let
     val ctxt = Local_Theory.target_of thy
     val (ty, _) = Term.dest_Type (Proof_Context.read_type_name {proper = true, strict = false} ctxt rec_name)
     val sels = hd (#selss (the (Ctr_Sugar.ctr_sugar_of ctxt ty))) in
          map (fst o Term.dest_Const) sels
       |> map Long_Name.base_name
     end

   \<comment>\<open>General helpers for interpreting strings as methods and applying them\<close>
   val apply_text = (Seq.the_result "initial method") oo ((fn t => (t, Position.no_range)) #> Proof.apply)
   val apply_method = K #> Method.Basic #> apply_text
   fun apply_txt ctxt = Input.string #> Method.read_closure_input ctxt #> fst #> apply_text

   fun context_tactic_to_context_tactic (t: Proof.context -> tactic) : context_tactic =
     fn (ctxt, thm) => (t ctxt thm |> Seq.make_results |> Seq.map_result (fn thm' => (ctxt, thm')))
     fun context_tactic_to_method (t : Proof.context -> tactic) : Method.method =
        t |> context_tactic_to_context_tactic |> K
   val apply_context_tactic = context_tactic_to_method #> apply_method

   \<comment> \<open>Extends the current context with an untyped definition \<^verbatim>\<open>definition \<open>name \<equiv> expr\<close>\<close>.\<close>
   fun typeless_def attribs name expr =
      ( #2 o Specification.definition_cmd (SOME((Binding.qualified_name name), NONE, Mixfix.NoSyn))
                                   [] [] ((Binding.empty, attribs), name ^ " \<equiv> " ^ expr) false)

   fun declare_attribs attribs thm =
     #2 o Specification.theorems_cmd "" [((Binding.empty, attribs), [(Facts.named thm, [])])] [] false
\<close>

subsection\<open>Automatic generation of lenses and lemmas\<close>

subsubsection\<open>Definitions\<close>

text\<open>This section implements the theory transformer \<^verbatim>\<open>lens_autogen_defs\<close> which, given a record name,
auto-generates lenses for each record field.\<close>

ML\<open>
   \<comment>\<open>The name of the lens associated with a record field\<close>
   fun lens_name rec_name field = rec_name ^ "_" ^ field ^ "_lens"

   \<comment>\<open>Theory transformation adding a single record field lens\<close>
   fun make_lens rec_name field ctxt = let
      val update_name = "update_" ^ field
      val lens_expr = "make_lens_via_view_modify " ^ field ^ " " ^ update_name in
        ctxt |> typeless_def [] (lens_name rec_name field) lens_expr
      end

   \<comment>\<open>Theory transformation adding lens definitions for a record\<close>
   fun lens_autogen_defs rec_name thy = fold (make_lens rec_name) (get_fields rec_name thy) thy
\<close>

locale AutoLensExample
begin

datatype_record foo =
  beef :: nat
  ham :: nat
  cheese :: nat
print_theorems

local_setup\<open>lens_autogen_defs "foo"\<close>
print_theorems
\<comment>\<open>\<^verbatim>\<open>theorems:
  foo_beef_lens_def: foo_beef_lens \<equiv> make_lens_via_view_modify beef update_beef
  foo_cheese_lens_def: foo_cheese_lens \<equiv> make_lens_via_view_modify cheese update_cheese
  foo_ham_lens_def: foo_ham_lens \<equiv> make_lens_via_view_modify ham update_ham\<close>\<close>

end

subsubsection\<open>Defining equations\<close>

ML\<open>
   fun prove_defining_eqns_for_lens attribs rec_name field ctxt = let
    val lens = lens_name rec_name field
    val lens_def = lens |> Thm.def_name
    val prop_view_str = "lens_view " ^ lens ^ " = " ^ field
    val prop_modify_str = "lens_modify " ^ lens ^ " = update_" ^ field
    val prop_update_str = "lens_update " ^ lens ^ " = (\<lambda>x. update_" ^ field ^ " (\<lambda>_. x))"
    val view_prop = prop_view_str |> Syntax.read_prop ctxt
    val modify_prop = prop_modify_str |> Syntax.read_prop ctxt
    val update_prop = prop_update_str |> Syntax.read_prop ctxt
    val prop_name = lens ^ "_view_update_modify"
    fun after_qed name thms ctxt = ctxt
       |> Local_Theory.note (name, flat thms) |> snd
       |> Local_Theory.note ((Binding.empty,attribs), thms |> flat) |> snd
    in
        ctxt
     |> Proof.theorem NONE
                      (after_qed ((Binding.name prop_name), []))
                      [[(view_prop, [])],[(modify_prop, [])], [(update_prop, [])]]
     |> apply_txt ctxt (
         "intro ext; clarsimp simp add: make_lens_via_view_modify_def " ^ lens_def
        )
     |> apply_txt ctxt (
         "intro ext; clarsimp simp add: make_lens_via_view_modify_def " ^ lens_def ^ 
                        " lens_modify_def " ^ rec_name ^ ".expand"
        )
     |> apply_txt ctxt (
         "intro ext; clarsimp simp add: make_lens_via_view_modify_def " ^ lens_def)
     |> Proof.global_done_proof
    end

   \<comment>\<open>Theory transformation adding defining equations for all fields of a record.\<close>
   fun lens_autogen_defining_equations attribs rec_name thy =
     let val fields = get_fields rec_name thy in
       fold (prove_defining_eqns_for_lens attribs rec_name) fields thy
     end
\<close>

context AutoLensExample
begin
local_setup\<open>lens_autogen_defining_equations [] "foo"\<close>
print_theorems
\<comment>\<open>\<^verbatim>\<open>theorems:
  foo_beef_lens_view_update_modify:
      lens_view foo_beef_lens = beef
      \<nabla>{foo_beef_lens} = update_beef
      lens_update foo_beef_lens = (\<lambda>x. update_beef (\<lambda>_. x))
  foo_cheese_lens_view_update_modify:
      lens_view foo_cheese_lens = cheese
      \<nabla>{foo_cheese_lens} = update_cheese
      lens_update foo_cheese_lens = (\<lambda>x. update_cheese (\<lambda>_. x))
  foo_ham_lens_view_update_modify:
      lens_view foo_ham_lens = ham
      \<nabla>{foo_ham_lens} = update_ham
      lens_update foo_ham_lens = (\<lambda>x. update_ham (\<lambda>_. x))\<close>\<close>
end

subsubsection\<open>Lens validity\<close>

text\<open>All auto-generated lenses are valid:\<close>

ML\<open>
  \<comment>\<open>States and proves the validity of the auto-generated lens corresponding to a record field.\<close>
  fun prove_lens_validity attribs rec_name field ctxt = let
    val lens = lens_name rec_name field
    val lens_def = lens |> Thm.def_name
    val prop_name = lens ^ "_valid"
    val prop_str = "is_valid_lens " ^ lens
    val validity_prop = prop_str |> Syntax.read_prop ctxt
    fun after_qed name thms ctxt = ctxt
       |> Local_Theory.note (name, flat thms) |> snd
       |> Local_Theory.note ((Binding.empty, attribs), thms |> flat) |> snd
    in
        ctxt
     |> Proof.theorem NONE
                      (after_qed ((Binding.name prop_name), []))
                      [[(validity_prop, [])]]
     |> apply_txt ctxt (String.concatWith ";"
          ["unfold " ^ lens_def,
           "intro is_valid_lens_via_modifyI'",
           "simp add: is_valid_lens_view_modify_def " ^ rec_name ^ ".expand"])
     |> Proof.global_done_proof
    end

   \<comment>\<open>Theory transformation adding lens validity lemmas\<close>
   fun lens_autogen_prove_lens_validity attribs rec_name thy =
      let val fields = get_fields rec_name thy in
        fold (prove_lens_validity attribs rec_name) fields thy
      end
\<close>

context AutoLensExample
begin
local_setup\<open>lens_autogen_prove_lens_validity [] "foo"\<close>
print_theorems
\<comment>\<open>\<^verbatim>\<open>foo_beef_lens_valid: is_valid_lens foo_beef_lens
    foo_cheese_lens_valid: is_valid_lens foo_cheese_lens
    foo_ham_lens_valid: is_valid_lens foo_ham_lens\<close>\<close>
end

subsubsection\<open>Field projection foci\<close>

text\<open>This section lifts the field-lenses auto-generated so far to the level of foci.\<close>

named_theorems lens_focus_conversions
ML\<open>
  fun get_field_type ctxt recname field = 
     Syntax.read_term ctxt (recname ^ "." ^ field) |> Term.type_of |> Term.body_type

  fun get_record_type ctxt recname field = 
     Syntax.read_term ctxt (recname ^ "." ^ field) |> Term.type_of |> Term.binder_types |> hd

  fun get_field_type_as_string ctxt recname field = 
      get_field_type ctxt recname field 
   |> Syntax.pretty_typ ctxt
   |> Pretty.symbolic_string_of
   |> Protocol_Message.clean_output

  fun get_record_type_as_string ctxt recname field =
      get_record_type ctxt recname field 
   |> Syntax.pretty_typ ctxt
   |> Pretty.symbolic_string_of
   |> Protocol_Message.clean_output

   \<comment>\<open>The name of the lens associated with a record field\<close>
   fun focus_name rec_name field = rec_name ^ "_" ^ field ^ "_focus"
   fun focus_type ctxt rec_name field = 
      "(" ^ get_record_type_as_string ctxt rec_name field ^ "," ^
            get_field_type_as_string ctxt rec_name field ^ ") focus"

  \<comment>\<open>Lifts the field projection lenses to foci via direct application of \<^verbatim>\<open>lift_definition\<close>:\<close>
  fun make_rec_field_focus_direct rec_name field ctxt = let
    val focus_name = focus_name rec_name field
    val lens_name = lens_name rec_name field
    val ty = focus_type ctxt rec_name field
    val lens_validity_lemma = lens_name ^ "_valid"
    in ctxt 
       |> (Lifting_Def_Code_Dt.lift_def_cmd (
          [], (Binding.name focus_name, SOME ty, Mixfix.NoSyn), "\<integral>\<^sub>l " ^ lens_name, []
       ))
       |> apply_txt ctxt ("simp add: lens_to_focus_raw_valid " ^ lens_validity_lemma)
       |> Proof.global_done_proof
    end

  \<comment>\<open>Prove component lemmas for record field foci, via lift definition\<close>
  fun prove_record_field_focus_components_direct attribs rec_name field ctxt = let
    val focus = focus_name rec_name field
    val lens = lens_name rec_name field
    val prop_view_str = "focus_view " ^ focus ^ " x = Some (" ^ field ^ " x)"
    val prop_modify_str = "focus_modify " ^ focus ^ " = update_" ^ field
    val prop_update_str = "focus_update " ^ focus ^ " = (\<lambda>x. update_" ^ field ^ " (\<lambda>_. x))"
    val view_prop = prop_view_str |> Syntax.read_prop ctxt
    val modify_prop = prop_modify_str |> Syntax.read_prop ctxt
    val update_prop = prop_update_str |> Syntax.read_prop ctxt
    val prop_name = focus ^ "_view_update_modify"
    fun after_qed name thms ctxt = ctxt
       |> Local_Theory.note (name, flat thms) |> snd
       |> Local_Theory.note ((Binding.empty,attribs), thms |> flat) |> snd
    in
        ctxt
     |> Proof.theorem NONE
                      (after_qed ((Binding.name prop_name), []))
                      [[(view_prop, [])],[(modify_prop, [])], [(update_prop, [])]]
     |> apply_txt ctxt "transfer"
     |> apply_txt ctxt (
         "clarsimp simp add: lens_to_focus_raw_components " ^ lens ^ "_view_update_modify" 
        )
     |> apply_txt ctxt "transfer"
     |> apply_txt ctxt (
         "intro ext; clarsimp simp add: lens_to_focus_raw_components " ^ lens ^ "_view_update_modify" 
        )
     |> apply_txt ctxt "transfer"
     |> apply_txt ctxt (
         "intro ext; clarsimp simp add: lens_to_focus_raw_components " ^ lens ^ "_view_update_modify" 
        )
     |> Proof.global_done_proof
    end

  \<comment>\<open>Lifts the field projection lenses to foci via generic \<^verbatim>\<open>lens_to_focus\<close>. The downside here
   is that all theorems about \<^verbatim>\<open>lens_to_focus\<close> are conditional on lens validity (which in the
   case of the construction via \<^verbatim>\<open>lift_definition\<close> is proved upfront, and need explicit instantiation.\<close>
   fun make_rec_field_focus_generic attribs rec_name field = let
      val lens = lens_name rec_name field
      val focus = focus_name rec_name field
      val focus_expr = "lens_to_focus " ^ lens in
        typeless_def attribs focus focus_expr
      end

  \<comment>\<open>Prove component lemmas for record field foci, via generic definition\<close>
  fun prove_record_field_focus_components_generic attribs rec_name field ctxt = let
    val focus = focus_name rec_name field
    val focus_def = focus |> Thm.def_name
    val lens = lens_name rec_name field
    val lens_valid = lens ^ "_valid"
    val lens_view_update_modify = lens ^ "_view_update_modify"
    val prop_view_str = "focus_view " ^ focus ^ " x = Some (" ^ field ^ " x)"
    val prop_modify_str = "focus_modify " ^ focus ^ " = update_" ^ field
    val prop_update_str = "focus_update " ^ focus ^ " = (\<lambda>x. update_" ^ field ^ " (\<lambda>_. x))"
    val view_prop = prop_view_str |> Syntax.read_prop ctxt
    val modify_prop = prop_modify_str |> Syntax.read_prop ctxt
    val update_prop = prop_update_str |> Syntax.read_prop ctxt
    val prop_name = focus ^ "_view_update_modify"
    fun after_qed name thms ctxt = ctxt
       |> Local_Theory.note (name, flat thms) |> snd
       |> Local_Theory.note ((Binding.empty,attribs), thms |> flat) |> snd
    in
        ctxt
     |> Proof.theorem NONE
                      (after_qed ((Binding.name prop_name), []))
                      [[(view_prop, [])],[(modify_prop, [])], [(update_prop, [])]]
     |> apply_txt ctxt 
         ("auto simp add: lens_to_focus_components lens_modify_def " 
          ^ focus_def ^ " " ^ lens_valid ^ " " ^ lens_view_update_modify)
     |> Proof.global_done_proof
    end

  \<comment>\<open>Prove extractable code equations for record field foci, via generic definition.
  Unfolding of definitions is necessary to avoid ML value restriction.\<close>
  fun prove_record_field_focus_code_equations_generic rec_name field ctxt = let
    val (_, rec_name_full) = prepare_rec_name ctxt rec_name 
    val focus = focus_name rec_name field
    val focus_def = focus |> Thm.def_name
    val lens = lens_name rec_name field
    val lens_valid = lens ^ "_valid"
    val lens_view_update_modify = lens ^ "_view_update_modify"
    val code_eq_prop_str = "Rep_focus " ^ focus ^ " = make_focus_raw " ^
           "(\<lambda>s. Some (" ^ rec_name ^ "." ^ field ^ " s))" ^
           "(\<lambda>y. " ^ rec_name_full ^ ".update_" ^ field ^ "(\<lambda>_. y))"
    val _ = code_eq_prop_str |> tracing
    val code_eq_prop = code_eq_prop_str |> Syntax.read_prop ctxt
    val prop_name = focus ^ "_code"
    fun after_qed name thms ctxt = ctxt
       |> Local_Theory.note (name, flat thms) |> snd
       |> Local_Theory.note ((Binding.empty, @{attributes [code]}), thms |> flat) |> snd
    in
        ctxt
     |> Proof.theorem NONE
                      (after_qed ((Binding.name prop_name), []))
                      [[(code_eq_prop, [])]]
     |> apply_txt ctxt 
         ("clarsimp simp add: lens_to_focus_raw_def lens_to_focus.rep_eq " 
          ^ focus_def ^ " " ^ lens_valid ^ " " ^ lens_view_update_modify)
     |> Proof.global_done_proof
     |> declare_attribs @{attributes [THEN HOL.meta_eq_to_obj_eq, symmetric, 
                                      focus_simps, lens_focus_conversions, code_unfold]} focus_def
    end

   \<comment>\<open>Theory transformation adding lens validity lemmas\<close>
   fun focus_autogen_make_field_foci attribs rec_name thy =
      let val fields = get_fields rec_name thy in thy 
       |> fold (make_rec_field_focus_generic @{attributes []} rec_name) fields
       |> fold (prove_record_field_focus_components_generic attribs rec_name) fields
       |> fold (prove_record_field_focus_code_equations_generic rec_name) fields
      end

\<close>

context AutoLensExample
begin
local_setup\<open>focus_autogen_make_field_foci [] "foo"\<close>
print_theorems
\<comment>\<open>\<^verbatim>\<open>  foo_beef_focus_code: Rep_focus foo_beef_focus = 
         make_focus_raw (\<lambda>s. Some (beef s)) (\<lambda>y. update_beef (\<lambda>_. y))
  foo_beef_focus_def: foo_beef_focus \<equiv> \<integral>\<^sub>l foo_beef_lens
  foo_beef_focus_view_update_modify:
      \<down>{foo_beef_focus} ?x \<doteq> beef ?x
      \<nabla>{foo_beef_focus} = update_beef
      focus_update foo_beef_focus = (\<lambda>x. update_beef (\<lambda>_. x))
  foo_cheese_focus_code: Rep_focus foo_cheese_focus = make_focus_raw (\<lambda>s. Some (cheese s)) (\<lambda>y. update_cheese (\<lambda>_. y))
  foo_cheese_focus_def: foo_cheese_focus \<equiv> \<integral>\<^sub>l foo_cheese_lens
  foo_cheese_focus_view_update_modify:
      \<down>{foo_cheese_focus} ?x \<doteq> cheese ?x
      \<nabla>{foo_cheese_focus} = update_cheese
      focus_update foo_cheese_focus = (\<lambda>x. update_cheese (\<lambda>_. x))
  foo_ham_focus_code: Rep_focus foo_ham_focus = make_focus_raw (\<lambda>s. Some (ham s)) (\<lambda>y. update_ham (\<lambda>_. y))
  foo_ham_focus_def: foo_ham_focus \<equiv> \<integral>\<^sub>l foo_ham_lens
  foo_ham_focus_view_update_modify:
      \<down>{foo_ham_focus} ?x \<doteq> ham ?x
      \<nabla>{foo_ham_focus} = update_ham
      focus_update foo_ham_focus = (\<lambda>x. update_ham (\<lambda>_. x))\<close>\<close>
end

subsubsection\<open>Other commonly used identities for lenses\<close>

text\<open>This section autoderives further useful identities about the lenses associated with record fields:\<close>

ML\<open>
  fun prove_update_eqns_for_lens attribs_simp attribs_intro rec_name fields field ctxt = let
    fun join' sep lst = fold (fn x => fn y => y ^ sep ^ x) lst ""
    val join = join' " "
    val make_rec = "make_" ^ rec_name
    val update_fun = "update_" ^ field
    val view_fun = field

    val prop_update_explicit_name = rec_name ^ "_" ^ field ^ "_update_explicit"
    val prop_update_local_name = rec_name ^ "_" ^ field ^ "_update_localI"

    val prop_update_explicit_str =
      "\<And> f " ^ join fields ^ " . " ^ update_fun ^ " f (" ^ (join (make_rec::fields)) ^ ") = "
      ^ (join (make_rec::(map (fn t => if t = field then "(f " ^ field ^ ")" else t) fields)))
    val prop_update_explicit = prop_update_explicit_str |> Syntax.read_prop ctxt

    val prop_update_local_str = "\<And> f g r. f (" ^ view_fun ^ " r)  = g(" ^ view_fun ^ " r) \<Longrightarrow> " ^ update_fun ^ " f r = " ^ update_fun ^ " g r"
    val prop_update_local = prop_update_local_str |> Syntax.read_prop ctxt
    fun after_qed named_theorems name thms ctxt = ctxt
      |> Local_Theory.note (name, flat thms) |> snd
      |> Local_Theory.note ((Binding.empty,named_theorems), thms |> flat) |> snd
    in
        ctxt
     |> Proof.theorem NONE
          (after_qed attribs_simp ((Binding.name prop_update_explicit_name), []))
          [[(prop_update_explicit, [])]]
     |> apply_txt ctxt ("simp add: " ^ rec_name ^ ".expand")
     |> Proof.global_done_proof

     |> Proof.theorem NONE
          (after_qed attribs_intro ((Binding.name prop_update_local_name), []))
          [[(prop_update_local, [])]]
     |> apply_txt ctxt ("simp add: " ^ rec_name ^ ".expand")
     |> Proof.global_done_proof
    end

   \<comment>\<open>Theory transformation proving update equations for lenses of a record\<close>
   fun lens_autogen_prove_update_equations attribs_simp attribs_intro rec_name thy =
     let val fields = get_fields rec_name thy in
       thy |> (fold (prove_update_eqns_for_lens attribs_simp attribs_intro rec_name fields) fields)
     end
\<close>

context AutoLensExample
begin
local_setup\<open>lens_autogen_prove_update_equations [] [] "foo"\<close>
print_theorems
\<comment>\<open>\<^verbatim>\<open>  foo_beef_update_explicit: update_beef ?f (make_foo ?beef ?ham ?cheese) = make_foo (?f ?beef) ?ham ?cheese
  foo_beef_update_localI: ?f (beef ?r) = ?g (beef ?r) \<Longrightarrow> update_beef ?f ?r = update_beef ?g ?r
  foo_cheese_update_explicit: update_cheese ?f (make_foo ?beef ?ham ?cheese) = make_foo ?beef ?ham (?f ?cheese)
  foo_cheese_update_localI: ?f (cheese ?r) = ?g (cheese ?r) \<Longrightarrow> update_cheese ?f ?r = update_cheese ?g ?r
  foo_ham_update_explicit: update_ham ?f (make_foo ?beef ?ham ?cheese) = make_foo ?beef (?f ?ham) ?cheese
  foo_ham_update_localI: ?f (ham ?r) = ?g (ham ?r) \<Longrightarrow> update_ham ?f ?r = update_ham ?g ?r\<close>\<close>
end

(*<*)
end
(*>*)

