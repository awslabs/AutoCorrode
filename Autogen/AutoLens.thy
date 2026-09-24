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

   \<comment>\<open>Generated names shared by every record-autogen phase.\<close>
   fun lens_name rec_name field = rec_name ^ "_" ^ field ^ "_lens"
   fun focus_name rec_name field = rec_name ^ "_" ^ field ^ "_focus"

   datatype autolens_record_backend =
       AutoLens_Datatype_Record of
         {constructor: term,
          constructor_simps: thm list,
          exhaust: thm,
          selector_simps: thm list}
     | AutoLens_HOL_Record

   type autolens_field_descriptor =
     {index: int,
      base_name: string,
      selector_name: string,
      selector: term,
      field_type: typ,
      updater_name: string,
      updater: term,
      updater_def: thm option,
      lens_name: string,
      focus_name: string}

   type autolens_record_descriptor =
     {source_name: string,
      type_name: string,
      record_type: typ,
      backend: autolens_record_backend,
      fields: autolens_field_descriptor list,
      expand_rules: thm list}

   type autolens_lens_definition_artifact =
     {field: autolens_field_descriptor,
      lens: term,
      lens_def: thm}

   type autolens_lens_components_artifact =
     {field: autolens_field_descriptor,
      lens: term,
      lens_def: thm,
      view_modify_valid: thm,
      lens_components: thm list}

   type autolens_lens_artifact =
     {field: autolens_field_descriptor,
      lens: term,
      lens_def: thm,
      view_modify_valid: thm,
      lens_components: thm list,
      lens_valid: thm}

   type autolens_update_artifact =
     {field: autolens_field_descriptor,
      update_explicit: thm,
      update_local: thm}

   type autolens_focus_definition_artifact =
     {lens_artifact: autolens_lens_artifact,
      focus: term,
      focus_def: thm}

   type autolens_focus_components_artifact =
     {lens_artifact: autolens_lens_artifact,
      focus: term,
      focus_def: thm,
      focus_components: thm list}

   type autolens_focus_artifact =
     {field: autolens_field_descriptor,
      focus: term,
      focus_def: thm,
      focus_components: thm list,
      focus_code: thm}

   fun check_application ctxt name args =
     Syntax.check_term ctxt
       (list_comb (Const (name, dummyT), args))

   fun check_equality_prop ctxt lhs rhs =
     Syntax.check_term ctxt
       (HOLogic.mk_Trueprop
         (Const (\<^const_name>\<open>HOL.eq\<close>, dummyT) $ lhs $ rhs))

   fun define_typed_constant name rhs lthy =
     let
       val binding = Binding.qualified_name name
     in
       Local_Theory.define
         ((binding, Mixfix.NoSyn),
          ((Thm.def_binding binding,
            [Code.singleton_default_equation_attrib]), rhs)) lthy
     end

   fun prove_autogen_prop_with ctxt ctxt' asms prop tac =
     let
       val thm = Goal.prove ctxt' [] asms prop tac
     in
       Variable.export ctxt' ctxt [thm] |> the_single
     end

   \<comment>\<open>Looks up a datatype record in the given context, and returns the list of fields (fully qualified)\<close>

   fun get_fields_full rec_name thy =
     let
       val ctxt = Local_Theory.target_of thy
       val theory = Proof_Context.theory_of ctxt
       val (ty, _) =
         Term.dest_Type
           (Proof_Context.read_type_name
             {proper = true, strict = false} ctxt rec_name)
       fun standard_record_hierarchy name =
         let
           val info = Record.the_info theory name
           val parents =
             (case #parent info of
                NONE => []
              | SOME (_, parent_name) =>
                  standard_record_hierarchy parent_name)
         in
           parents @ [info]
         end
     in
       case Ctr_Sugar.ctr_sugar_of ctxt ty of
         SOME sugar =>
           hd (#selss sugar) |> map (fst o Term.dest_Const)
       | NONE =>
           (case Record.get_info theory ty of
              SOME _ =>
                standard_record_hierarchy ty
                |> maps #fields
                |> map fst
            | NONE =>
                error ("Unknown datatype or record type " ^ quote rec_name))
     end

   fun get_fields rec_name thy =
          get_fields_full rec_name thy
       |> map Long_Name.base_name

  fun extract_const_core ((Const ("_type_constraint_", _)) $ t) = extract_const_core t
    | extract_const_core (Abs (_, _, t)) = extract_const_core t
    | extract_const_core t = t |> Term.strip_comb |> fst |> Term.dest_Const

  val extract_const = extract_const_core #> fst

  fun field_update rec_name field = rec_name ^ "." ^ "update_" ^ field

  fun get_field_updates_full rec_name thy =
    let
      val ctxt = Local_Theory.target_of thy
      val theory = Proof_Context.theory_of ctxt
      val (ty, _) =
        Term.dest_Type
          (Proof_Context.read_type_name
            {proper = true, strict = false} ctxt rec_name)
    in
      case Record.get_info theory ty of
        SOME _ => get_fields_full rec_name thy |> map (suffix Record.updateN)
      | NONE =>
          get_fields rec_name thy
          |> List.map (field_update rec_name
                       #> Syntax.parse_term thy
                       #> extract_const)
    end

   fun specialize_result_type ctxt result_type t =
     let
       val thy = Proof_Context.theory_of ctxt
       val term_type = fastype_of t
       val matching_binders =
         Term.binder_types term_type
         |> filter (fn T => Type.could_unify (T, result_type))
       val matching_types = Term.body_type term_type :: matching_binders
       val tyenv =
         fold (fn T => Sign.typ_match thy (T, result_type))
           matching_types Vartab.empty
     in
       Envir.subst_term_types tyenv t
     end

   fun specialize_term_type ctxt expected_type t =
     let
       val thy = Proof_Context.theory_of ctxt
       val tyenv =
         Sign.typ_match thy (fastype_of t, expected_type)
           Vartab.empty
     in
       Envir.subst_term_types tyenv t
     end

   fun defined_const thm =
     (case Thm.prop_of thm of
        Const (\<^const_name>\<open>Pure.eq\<close>, _) $ lhs $ _ =>
          SOME (Term.dest_Const (Term.head_of lhs) |> fst)
      | _ => NONE)
     handle TERM _ => NONE

   fun datatype_updater_defs ctxt =
     fold
       (fn thm =>
         (case defined_const thm of
            SOME name => Symtab.update (name, thm)
          | NONE => I))
       (Named_Theorems.get ctxt
         \<^named_theorems>\<open>datatype_record_update\<close>)
       Symtab.empty

   fun prepare_record_descriptor rec_name lthy : autolens_record_descriptor =
     let
       val ctxt = Local_Theory.target_of lthy
       val theory = Proof_Context.theory_of ctxt
       val raw_record_type =
         Proof_Context.read_type_name
           {proper = true, strict = false} ctxt rec_name
       val (type_name, _) = Term.dest_Type raw_record_type
       val selector_names = get_fields_full rec_name lthy
       fun read_const name =
         Proof_Context.read_const {proper = true, strict = true} ctxt name
       fun build_fields updater_def_of selectors updater_names updaters =
         let
           fun build _ [] [] [] [] = []
             | build index (selector_name :: selector_names)
                 (selector :: selectors) (updater_name :: updater_names)
                 (updater :: updaters) =
                 let
                   val base_name = Long_Name.base_name selector_name
                   val updater_name_full = Term.dest_Const updater |> fst
                 in
                   {index = index,
                    base_name = base_name,
                    selector_name = selector_name,
                    selector = selector,
                    field_type = Term.body_type (fastype_of selector),
                    updater_name = updater_name_full,
                    updater = updater,
                    updater_def = updater_def_of updater_name_full,
                    lens_name = lens_name rec_name base_name,
                    focus_name = focus_name rec_name base_name}
                   :: build (index + 1) selector_names selectors updater_names
                        updaters
                 end
             | build _ _ _ _ _ =
                 error ("Inconsistent selector/updater metadata for record "
                   ^ quote rec_name)
         in
           build 0 selector_names selectors updater_names updaters
         end
       fun fallback_expand_rules () =
         (case try (lookup_thm ctxt) (rec_name ^ ".expand") of
            SOME thm => [thm]
          | NONE => [])
     in
       case Ctr_Sugar.ctr_sugar_of ctxt type_name of
         SOME sugar =>
           let
             val record_type = #T sugar
             val constructor =
               (case #ctrs sugar of
                  [constructor] => constructor
                | _ => error ("Expected one constructor for record "
                    ^ quote rec_name))
             val selectors =
               (case #selss sugar of
                  [selectors] => selectors
                | _ => error ("Expected one selector family for record "
                    ^ quote rec_name))
             val updater_names =
               map (prefix "update_" o Long_Name.base_name) selector_names
             val updaters =
               map (specialize_result_type ctxt record_type o read_const)
                 updater_names
             val updater_defs = datatype_updater_defs ctxt
             fun updater_def_of name = Symtab.lookup updater_defs name
             val expand_rules =
               if null (#expands sugar) then fallback_expand_rules ()
               else #expands sugar
           in
             {source_name = rec_name,
              type_name = type_name,
              record_type = record_type,
              backend = AutoLens_Datatype_Record
                {constructor = constructor,
                 constructor_simps = #case_thms sugar,
                 exhaust = #exhaust sugar,
                 selector_simps = flat (#sel_thmss sugar)},
              fields =
                build_fields updater_def_of
                  selectors updater_names updaters,
              expand_rules = expand_rules}
           end
       | NONE =>
           let
             val (record_type0, _) = prepare_rec_name ctxt rec_name
             val record_type = record_type0
             val updater_names = get_field_updates_full rec_name lthy
             val selectors = map read_const selector_names
             val updaters = map read_const updater_names
             val _ =
               if is_some (Record.get_info theory type_name) then ()
               else error ("Unknown datatype or record type " ^ quote rec_name)
           in
             {source_name = rec_name,
              type_name = type_name,
              record_type = record_type,
              backend = AutoLens_HOL_Record,
              fields =
                build_fields (lookup_def_opt ctxt)
                  selectors updater_names updaters,
              expand_rules = fallback_expand_rules ()}
           end
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
   fun prove_view_modify_valid_from
       (descriptor : autolens_record_descriptor)
       (field : autolens_field_descriptor) lthy =
     let
       val ([selector, updater], ctxt') =
         Variable.importT_terms [#selector field, #updater field] lthy
       val validity =
         check_application ctxt'
           \<^const_name>\<open>is_valid_lens_view_modify\<close>
           [selector, updater]
         |> HOLogic.mk_Trueprop
       val rules =
         Proof_Context.get_thm ctxt'
           "is_valid_lens_view_modify_def"
           :: #expand_rules descriptor
     in
       prove_autogen_prop_with lthy ctxt' [] validity
         (fn {context, ...} =>
           asm_full_simp_tac (context addsimps rules) 1)
     end

   fun define_lens_from
       (descriptor : autolens_record_descriptor)
       (field : autolens_field_descriptor) lthy =
     let
       val ([selector, updater], definition_lthy) =
         Variable.importT_terms
           [#selector field, #updater field] lthy
       val rhs =
         check_application definition_lthy
           \<^const_name>\<open>make_lens_via_view_modify\<close>
           [selector, updater]
       val ((lens, (_, lens_def)), lthy') =
         define_typed_constant (#lens_name field) rhs definition_lthy
     in
       ({field = field,
         lens = lens,
         lens_def = lens_def}
        : autolens_lens_definition_artifact,
        lthy')
     end

   fun lens_autogen_defs_from
       (descriptor : autolens_record_descriptor) lthy =
     fold_map (define_lens_from descriptor) (#fields descriptor) lthy

   fun lookup_lens_definitions_from
       (descriptor : autolens_record_descriptor) lthy =
     let
       fun lookup field =
         let
           val lens =
             Proof_Context.read_const
               {proper = true, strict = true} lthy (#lens_name field)
           val lens_def =
             Proof_Context.get_thm lthy
               (Thm.def_name (#lens_name field))
         in
           {field = field,
            lens = lens,
            lens_def = lens_def}
           : autolens_lens_definition_artifact
         end
     in
       map lookup (#fields descriptor)
     end

   \<comment>\<open>Theory transformation adding lens definitions for a record\<close>
   fun lens_autogen_defs rec_name lthy =
     let
       val descriptor = prepare_record_descriptor rec_name lthy
     in
       lens_autogen_defs_from descriptor lthy |> snd
     end
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
   fun make_lens_component_props
       (artifact : autolens_lens_definition_artifact) ctxt =
     let
       val {field, lens, ...} = artifact
       val view =
         check_application ctxt \<^const_name>\<open>lens_view\<close> [lens]
       val modify =
         check_application ctxt \<^const_name>\<open>lens_modify\<close> [lens]
       val update =
         check_application ctxt \<^const_name>\<open>lens_update\<close> [lens]
       val selector =
         specialize_term_type ctxt (fastype_of view) (#selector field)
       val updater =
         specialize_term_type ctxt (fastype_of modify) (#updater field)
       val (field_type, _) = Term.dest_funT (fastype_of update)
       val update_rhs =
         Abs ("x", field_type,
           updater $ Abs ("_", field_type, Bound 1))
     in
       [check_equality_prop ctxt view selector,
        check_equality_prop ctxt modify updater,
        check_equality_prop ctxt update update_rhs]
     end

   fun prove_lens_component lthy lens_def rule core prop =
     Goal.prove lthy [] [] prop
       (fn {context, ...} =>
         Local_Defs.unfold_tac context [lens_def] THEN
         resolve_tac context [rule] 1 THEN
         (case core of
            SOME thm => resolve_tac context [thm] 1
          | NONE => all_tac))

   fun prove_lens_components_from attribs
       (descriptor : autolens_record_descriptor)
       (artifact : autolens_lens_definition_artifact) lthy =
     let
       val {field, lens, lens_def} = artifact
       val view_modify_valid =
         prove_view_modify_valid_from descriptor field lthy
       val props = make_lens_component_props artifact lthy
       val rules =
         Proof_Context.get_thms lthy
           "make_lens_via_view_modify_components"
       val components =
         [prove_lens_component lthy lens_def
            (nth rules 0)
            NONE (nth props 0),
          prove_lens_component lthy lens_def
            (nth rules 2)
            (SOME view_modify_valid) (nth props 1),
          prove_lens_component lthy lens_def
            (nth rules 1)
            NONE (nth props 2)]
       val (_, lthy') =
         Local_Theory.note
           ((Binding.name (#lens_name field ^ "_view_update_modify"),
             attribs),
            components) lthy
     in
       ({field = field,
         lens = lens,
         lens_def = lens_def,
         view_modify_valid = view_modify_valid,
         lens_components = components}
        : autolens_lens_components_artifact,
        lthy')
     end

   fun lens_autogen_defining_equations_from attribs
       (descriptor : autolens_record_descriptor) artifacts lthy =
     fold_map (prove_lens_components_from attribs descriptor)
       artifacts lthy

   \<comment>\<open>Theory transformation adding defining equations for all fields of a record.\<close>
   fun lens_autogen_defining_equations attribs rec_name lthy =
     let
       val descriptor = prepare_record_descriptor rec_name lthy
       val artifacts = lookup_lens_definitions_from descriptor lthy
     in
       lens_autogen_defining_equations_from
         attribs descriptor artifacts lthy
       |> snd
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
   fun lookup_lens_components_from
       (descriptor : autolens_record_descriptor) lthy =
     let
       val definitions = lookup_lens_definitions_from descriptor lthy
       fun lookup
           ({field, lens, lens_def}
             : autolens_lens_definition_artifact) =
         {field = field,
          lens = lens,
          lens_def = lens_def,
          view_modify_valid =
            prove_view_modify_valid_from descriptor field lthy,
          lens_components =
            Proof_Context.get_thms lthy
              (#lens_name field ^ "_view_update_modify")}
         : autolens_lens_components_artifact
     in
       map lookup definitions
     end

   fun prove_lens_validity_from attribs
       (artifact : autolens_lens_components_artifact) lthy =
     let
       val {field, lens, lens_def, view_modify_valid, lens_components} =
         artifact
       val validity_prop =
         check_application lthy \<^const_name>\<open>is_valid_lens\<close> [lens]
         |> HOLogic.mk_Trueprop
       val lens_valid =
         Goal.prove lthy [] [] validity_prop
           (fn {context, ...} =>
             Local_Defs.unfold_tac context [lens_def] THEN
             resolve_tac context
               [Proof_Context.get_thm context
                  "is_valid_lens_via_modifyI'"] 1 THEN
             resolve_tac context [view_modify_valid] 1)
       val (_, lthy') =
         Local_Theory.note
           ((Binding.name (#lens_name field ^ "_valid"), attribs),
            [lens_valid]) lthy
     in
       ({field = field,
         lens = lens,
         lens_def = lens_def,
         view_modify_valid = view_modify_valid,
         lens_components = lens_components,
         lens_valid = lens_valid}
        : autolens_lens_artifact,
        lthy')
     end

   fun lens_autogen_prove_lens_validity_from attribs
       (_ : autolens_record_descriptor) artifacts lthy =
     fold_map (prove_lens_validity_from attribs) artifacts lthy

   fun lookup_lens_artifacts_from
       (descriptor : autolens_record_descriptor) lthy =
     let
       val components = lookup_lens_components_from descriptor lthy
       fun lookup
           ({field, lens, lens_def, view_modify_valid, lens_components}
             : autolens_lens_components_artifact) =
         {field = field,
          lens = lens,
          lens_def = lens_def,
          view_modify_valid = view_modify_valid,
          lens_components = lens_components,
          lens_valid =
            Proof_Context.get_thm lthy (#lens_name field ^ "_valid")}
         : autolens_lens_artifact
     in
       map lookup components
     end

   \<comment>\<open>Theory transformation adding lens validity lemmas\<close>
   fun lens_autogen_prove_lens_validity attribs rec_name lthy =
     let
       val descriptor = prepare_record_descriptor rec_name lthy
       val artifacts = lookup_lens_components_from descriptor lthy
     in
       lens_autogen_prove_lens_validity_from
         attribs descriptor artifacts lthy
       |> snd
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

   fun make_focus_component_props
       (lens_artifact : autolens_lens_artifact) focus ctxt =
     let
       val {field, lens, ...} = lens_artifact
       val lens_view =
         check_application ctxt \<^const_name>\<open>lens_view\<close> [lens]
       val focus_view =
         check_application ctxt \<^const_name>\<open>focus_view\<close> [focus]
       val focus_modify =
         check_application ctxt \<^const_name>\<open>focus_modify\<close> [focus]
       val focus_update =
         check_application ctxt \<^const_name>\<open>focus_update\<close> [focus]
       val selector =
         specialize_term_type ctxt (fastype_of lens_view)
           (#selector field)
       val updater =
         specialize_term_type ctxt (fastype_of focus_modify)
           (#updater field)
       val (record_type, field_type) =
         Term.dest_funT (fastype_of selector)
       val ([x_name], ctxt') = Variable.variant_fixes ["x"] ctxt
       val x = Free (x_name, record_type)
       val view_rhs =
         check_application ctxt' \<^const_name>\<open>Some\<close>
           [selector $ x]
       val update_rhs =
         Abs ("x", field_type,
           updater $ Abs ("_", field_type, Bound 1))
     in
       ([check_equality_prop ctxt' (focus_view $ x) view_rhs,
         check_equality_prop ctxt' focus_modify updater,
         check_equality_prop ctxt' focus_update update_rhs],
        selector, updater, ctxt')
     end

   fun prove_focus_component lthy ctxt' prop rules =
     prove_autogen_prop_with lthy ctxt' [] prop
       (fn {context, ...} =>
         asm_full_simp_tac
           (put_simpset HOL_basic_ss context addsimps rules) 1)

   fun make_focus_code_prop focus selector updater ctxt =
     let
       val rep_focus =
         check_application ctxt \<^const_name>\<open>Rep_focus\<close> [focus]
       val (record_type, field_type) =
         Term.dest_funT (fastype_of selector)
       val view =
         Abs ("s", record_type,
           Const (\<^const_name>\<open>Some\<close>, dummyT) $
             (selector $ Bound 0))
       val update =
         Abs ("y", field_type,
           updater $ Abs ("_", field_type, Bound 1))
       val rhs =
         check_application ctxt \<^const_name>\<open>make_focus_raw\<close>
           [view, update]
     in
       check_equality_prop ctxt rep_focus rhs
     end

   fun define_focus_from
       (lens_artifact : autolens_lens_artifact) lthy =
     let
       val {field, lens, ...} = lens_artifact
       val rhs =
         check_application lthy \<^const_name>\<open>lens_to_focus\<close>
           [lens]
       val ((focus, (_, focus_def)), lthy') =
         define_typed_constant (#focus_name field) rhs lthy
     in
       ({lens_artifact = lens_artifact,
         focus = focus,
         focus_def = focus_def}
        : autolens_focus_definition_artifact,
        lthy')
     end

   fun prove_focus_components_from attribs
       (artifact : autolens_focus_definition_artifact) lthy =
     let
       val {lens_artifact, focus, focus_def} = artifact
       val {field, lens_components, lens_valid, ...} = lens_artifact
       val (props, selector, updater, component_ctxt) =
         make_focus_component_props lens_artifact focus lthy
       val generic_components =
         Proof_Context.get_thms lthy "lens_to_focus_components"
       val component_rules =
         focus_def :: lens_valid ::
           (generic_components @ lens_components @
             [Proof_Context.get_thm lthy "comp_apply"])
       val focus_components =
         map (fn prop =>
           prove_focus_component lthy component_ctxt
             prop component_rules) props
       val (_, lthy') =
         Local_Theory.note
           ((Binding.name (#focus_name field ^ "_view_update_modify"),
             attribs),
            focus_components) lthy
     in
       ({lens_artifact = lens_artifact,
         focus = focus,
         focus_def = focus_def,
         focus_components = focus_components}
        : autolens_focus_components_artifact,
        lthy')
     end

   fun prove_focus_code_from
       (artifact : autolens_focus_components_artifact) lthy =
     let
       val {lens_artifact, focus, focus_def, focus_components} =
         artifact
       val {field, lens_components, lens_valid, ...} = lens_artifact
       val (_, selector, updater, _) =
         make_focus_component_props lens_artifact focus lthy
       val code_prop =
         make_focus_code_prop focus selector updater lthy
       val code_rules =
         [focus_def, lens_valid,
          Proof_Context.get_thm lthy "lens_to_focus_raw_def",
          Proof_Context.get_thm lthy "lens_to_focus.rep_eq"]
           @ lens_components
       val focus_code =
         Goal.prove lthy [] [] code_prop
           (fn {context, ...} =>
             asm_full_simp_tac
               (put_simpset HOL_basic_ss context
                 addsimps code_rules) 1)
       val (_, lthy') =
         Local_Theory.note
           ((Binding.name (#focus_name field ^ "_code"),
             @{attributes [code]}),
            [focus_code]) lthy
       val (_, lthy'') =
         Local_Theory.note
           ((Binding.empty,
             @{attributes [THEN HOL.meta_eq_to_obj_eq, symmetric,
                           focus_simps, lens_focus_conversions,
                           code_unfold]}),
            [focus_def]) lthy'
     in
       ({field = field,
         focus = focus,
         focus_def = focus_def,
         focus_components = focus_components,
         focus_code = focus_code}
        : autolens_focus_artifact,
        lthy'')
     end

   fun focus_autogen_defs_from
       (_ : autolens_record_descriptor) lens_artifacts lthy =
     fold_map define_focus_from lens_artifacts lthy

   fun focus_autogen_components_from attribs
       (_ : autolens_record_descriptor) focus_definitions lthy =
     fold_map (prove_focus_components_from attribs)
       focus_definitions lthy

   fun focus_autogen_code_from
       (_ : autolens_record_descriptor) focus_components lthy =
     fold_map prove_focus_code_from focus_components lthy

   fun focus_autogen_make_field_foci_from attribs
       (descriptor : autolens_record_descriptor) lens_artifacts lthy =
     let
       val (focus_definitions, lthy1) =
         focus_autogen_defs_from descriptor lens_artifacts lthy
       val (focus_components, lthy2) =
         focus_autogen_components_from attribs descriptor
           focus_definitions lthy1
     in
       focus_autogen_code_from descriptor focus_components lthy2
     end

   \<comment>\<open>Theory transformation adding record field foci.\<close>
   fun focus_autogen_make_field_foci attribs rec_name lthy =
     let
       val descriptor = prepare_record_descriptor rec_name lthy
       val lens_artifacts =
         lookup_lens_artifacts_from descriptor lthy
     in
       focus_autogen_make_field_foci_from
         attribs descriptor lens_artifacts lthy
       |> snd
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
  fun prove_update_eqns_for_lens_legacy attribs_simp attribs_intro
      rec_name fields field ctxt = let
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

   fun make_update_explicit_prop constructor
       (fields : autolens_field_descriptor list)
       (field : autolens_field_descriptor) ctxt =
     let
       val ([constructor', updater], imported_ctxt) =
         Variable.importT_terms [constructor, #updater field] ctxt
       val field_types = Term.binder_types (fastype_of constructor')
       val _ =
         if length field_types = length fields then ()
         else error "Constructor arity does not match record fields"
       val suggested_names = "f" :: map #base_name fields
       val (fixed_names, ctxt') =
         Variable.variant_fixes suggested_names imported_ctxt
       val field_type = nth field_types (#index field)
       val f =
         Free (hd fixed_names, field_type --> field_type)
       val args =
         map2 (fn name => fn T => Free (name, T))
           (tl fixed_names) field_types
       val record = list_comb (constructor', args)
       val updated_args =
         map_index
           (fn (index, arg) =>
             if index = #index field then f $ arg else arg)
           args
       val lhs = updater $ f $ record
       val rhs = list_comb (constructor', updated_args)
     in
       (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)), ctxt')
     end

   fun make_update_local_goal (field : autolens_field_descriptor) ctxt =
     let
       val ([selector, updater], imported_ctxt) =
         Variable.importT_terms [#selector field, #updater field] ctxt
       val (record_type, field_type) =
         Term.dest_funT (fastype_of selector)
       val (fixed_names, ctxt') =
         Variable.variant_fixes ["f", "g", "r"] imported_ctxt
       val f =
         Free (nth fixed_names 0,
           field_type --> field_type)
       val g =
         Free (nth fixed_names 1,
           field_type --> field_type)
       val r = Free (nth fixed_names 2, record_type)
       val selected = selector $ r
       val premise =
         HOLogic.mk_Trueprop
           (HOLogic.mk_eq (f $ selected, g $ selected))
       val conclusion =
         HOLogic.mk_Trueprop
           (HOLogic.mk_eq
             (updater $ f $ r, updater $ g $ r))
     in
       (premise, conclusion, r, ctxt')
     end

   fun prove_generated_prop_with ctxt ctxt' asms prop tac =
     let
       val thm =
         Goal.prove_future ctxt' [] asms prop tac
     in
       Variable.export ctxt' ctxt [thm] |> the_single
     end

   fun prove_generated_prop ctxt ctxt' prop rules =
     prove_generated_prop_with ctxt ctxt' [] prop
       (fn {context, ...} =>
         asm_full_simp_tac (context addsimps rules) 1)

   fun prove_update_local ctxt ctxt' premise conclusion r
       updater_def exhaust rules =
     prove_generated_prop_with ctxt ctxt' [premise] conclusion
       (fn {context, prems} =>
         Method.insert_tac context prems 1 THEN
         Induct_Tacs.case_tac context (Term.term_name r) []
           (SOME exhaust) 1 THEN
         asm_full_simp_tac
           (put_simpset HOL_basic_ss context
             addsimps (updater_def :: rules @ prems)) 1)

   fun note_update_eqns attribs_simp attribs_intro rec_name
       ((field : autolens_field_descriptor), explicit, local_thm) lthy =
     let
       val base = rec_name ^ "_" ^ #base_name field
       val (_, lthy') =
         Local_Theory.note
           ((Binding.name (base ^ "_update_explicit"), attribs_simp),
            [explicit]) lthy
       val (_, lthy'') =
         Local_Theory.note
           ((Binding.name (base ^ "_update_localI"), attribs_intro),
            [local_thm]) lthy'
     in
       lthy''
     end

   fun lens_autogen_prove_update_equations_from
       attribs_simp attribs_intro
       (descriptor : autolens_record_descriptor) lthy =
     let
       val {source_name, backend, fields, ...} =
         descriptor
     in
       case backend of
         AutoLens_Datatype_Record
           {constructor, constructor_simps, exhaust, selector_simps} =>
           let
             fun prove_field field =
               let
                 val (explicit_prop, explicit_ctxt) =
                   make_update_explicit_prop constructor fields field
                     lthy
                 val (local_premise, local_conclusion, local_record,
                      local_ctxt) =
                   make_update_local_goal field lthy
                 val updater_def =
                   (case #updater_def field of
                      SOME thm => thm
                    | NONE =>
                        error ("No definition theorem for updater "
                          ^ quote (#updater_name field)))
                 val explicit =
                   prove_generated_prop lthy explicit_ctxt
                     explicit_prop (updater_def :: constructor_simps)
                 val local_thm =
                   prove_update_local lthy local_ctxt
                     local_premise local_conclusion local_record
                     updater_def exhaust
                     (constructor_simps @ selector_simps)
               in
                 {field = field,
                  update_explicit = explicit,
                  update_local = local_thm}
                 : autolens_update_artifact
               end
             val artifacts = map prove_field fields
             val _ =
               Thm.consolidate
                 (maps
                   (fn ({update_explicit, update_local, ...}
                         : autolens_update_artifact) =>
                     [update_explicit, update_local])
                   artifacts)
             fun note
                 ({field, update_explicit, update_local}
                   : autolens_update_artifact) =
               note_update_eqns attribs_simp attribs_intro source_name
                 (field, update_explicit, update_local)
           in
             (artifacts, fold note artifacts lthy)
           end
       | AutoLens_HOL_Record =>
           let
             val field_names = map #base_name fields
             fun prove_legacy
                 ((field : autolens_field_descriptor), field_name)
                 current_lthy =
               let
                 val lthy' =
                   prove_update_eqns_for_lens_legacy
                     attribs_simp attribs_intro source_name
                     field_names field_name current_lthy
                 val base = source_name ^ "_" ^ field_name
               in
                 ({field = field,
                   update_explicit =
                     Proof_Context.get_thm lthy'
                       (base ^ "_update_explicit"),
                   update_local =
                     Proof_Context.get_thm lthy'
                       (base ^ "_update_localI")}
                  : autolens_update_artifact,
                  lthy')
               end
           in
             fold_map prove_legacy (fields ~~ field_names) lthy
           end
     end

   \<comment>\<open>Theory transformation proving update equations for lenses of a record\<close>
   fun lens_autogen_prove_update_equations attribs_simp attribs_intro rec_name thy =
     let
       val descriptor = prepare_record_descriptor rec_name thy
     in
       lens_autogen_prove_update_equations_from
         attribs_simp attribs_intro descriptor thy
       |> snd
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
