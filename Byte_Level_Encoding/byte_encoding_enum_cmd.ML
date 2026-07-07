(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* The `define_byte_enum` command.  Given a name and a list of (constructor,
   discriminant byte) pairs, it
     (1) defines the enumeration type via the existing `enum` command,
     (2) generates the discriminant encoding `<T>_to_byte` / `<T>_from_byte`,
     (3) defines `<T>_byte_prism` as an instance of `enum_byte_prism`, and
     (4) proves `<T>_byte_prism_valid` (the round-trip law) automatically.
   The type and its byte serialization from one declaration, with the
   round-trip proof discharged automatically. *)

signature BYTE_ENCODING_ENUM_CMD =
sig
  val define_byte_enum: binding -> (binding * int) list -> local_theory -> local_theory
end

structure Byte_Encoding_Enum_Cmd : BYTE_ENCODING_ENUM_CMD =
struct

(* Define a constant `<bind>` with body given as a string, returning its
   defining theorem and the updated context. *)
fun define_from_string bind rhs_str lthy =
  let
    val rhs = Syntax.read_term lthy rhs_str
    val ((_, (_, def_thm)), lthy') = lthy
      |> Local_Theory.define ((bind, NoSyn), ((Binding.suffix_name "_def" bind, []), rhs))
  in
    (def_thm, lthy')
  end

fun define_byte_enum typ_binding (specs : (binding * int) list) lthy =
  let
    val _ = if null specs then error "define_byte_enum: empty enum not allowed" else ()
    val typ_name = Binding.name_of typ_binding
    val ctors = map fst specs
    val ctor_names = map Binding.name_of ctors
    val discrs = map snd specs

    (* Step 1: define the enumeration type via the existing `enum` command,
       inside a nested target so its declarations (case syntax, [simp] rules)
       are committed before we build terms that refer to them. *)
    val lthy1 = lthy
      |> Local_Theory.begin_nested |> snd
      |> Enum_Cmd.enum_cmd (typ_binding, map (fn c => (c, [])) ctors)
      |> Local_Theory.end_nested

    (* Step 2: <T>_to_byte e = (<T>.case d0 d1 ... dn e :: byte) *)
    val to_byte_bind = Binding.suffix_name "_to_byte" typ_binding
    val case_args = space_implode " " (map string_of_int discrs)
    val to_byte_str =
      "(\<lambda>e. " ^ typ_name ^ ".case " ^ case_args ^ " e) :: " ^ typ_name ^ " \<Rightarrow> byte"
    val (to_byte_def, lthy2) = define_from_string to_byte_bind to_byte_str lthy1

    (* Step 3: <T>_from_byte w = if w = d0 then Some C0 else ... else None *)
    val from_byte_bind = Binding.suffix_name "_from_byte" typ_binding
    val clauses =
      map (fn (c, d) =>
            "if w = " ^ string_of_int d ^ " then Some " ^ typ_name ^ "." ^ c ^ " else ")
          (ctor_names ~~ discrs)
    val from_byte_str =
      "\<lambda>w::byte. " ^ implode clauses ^ "None"
    val (from_byte_def, lthy3) = define_from_string from_byte_bind from_byte_str lthy2

    (* Step 4: <T>_byte_prism = enum_byte_prism <T>_to_byte <T>_from_byte *)
    val prism_bind = Binding.suffix_name "_byte_prism" typ_binding
    val prism_str =
      "enum_byte_prism " ^ Binding.name_of to_byte_bind ^ " " ^ Binding.name_of from_byte_bind
    val (prism_def, lthy4) = define_from_string prism_bind prism_str lthy3

    (* Step 5: prove <T>_byte_prism_valid automatically.

       After `enum_byte_prism_valid` we face two goals:
         (1)  from_byte (to_byte e) = Some e
         (2)  from_byte w = Some e ==> to_byte e = w
       Goal (1) is discharged by induction on `e` (the enum command provides
       `<T>.induct`): each constructor reduces `to_byte` to its discriminant and
       then `from_byte` decodes it back.  Goal (2) is a case split on the nested
       `if` in `from_byte`. *)
    val induct_thm = Proof_Context.get_thm lthy4 (typ_name ^ ".induct")
    val valid_prop =
      Syntax.read_prop lthy4 ("is_valid_prism " ^ Binding.name_of prism_bind)
    (* The <T>.cases reduction rules are already [simp] (declared by the enum
       command), so we add only the encoding definitions.  Re-adding the case
       rules would trigger "Ignoring duplicate rewrite rule" warnings. *)
    val encoding_simps = [to_byte_def, from_byte_def]
    val simp_ctxt =
      fold Splitter.add_split @{thms if_split if_split_asm} (lthy4 addsimps encoding_simps)

    val valid_thm = Goal.prove lthy4 [] [] valid_prop
      (fn {context = ctxt, ...} =>
        Local_Defs.unfold_tac ctxt [prism_def]
        THEN resolve_tac ctxt @{thms enum_byte_prism_valid} 1
        (* Goal 1: induct on e, reducing each constructor case.  The same simp
           (with the if-splits and the constructor reduction rules) also closes
           the goal-2 cases. *)
        THEN resolve_tac ctxt [induct_thm] 1
        THEN ALLGOALS (asm_full_simp_tac simp_ctxt))
    val valid_bind = Binding.suffix_name "_byte_prism_valid" typ_binding
    val (_, lthy5) = lthy4
      |> Local_Theory.note ((valid_bind, []), [valid_thm])

    (* Step 6: declare the encoding definitions as code equations, so the enum's
       encoding is executable (needed once the enum focus below is run in a
       parser).  The prism/to_byte/from_byte are plain definitions; their
       defining equations become the code equations. *)
    val lthy6 = lthy5
      |> Code.declare_default_eqns [(prism_def, true), (to_byte_def, true), (from_byte_def, true)]

    (* Step 7: define <T>_focus = enum_byte_focus <T>_to_byte <T>_from_byte.
       This is the enum as a (typedef) focus, ready to be composed into a parser
       by the record command.  It is a plain definition on the generic guarded
       enum_byte_focus, so no per-enum lift_definition is needed. *)
    val focus_bind = Binding.suffix_name "_focus" typ_binding
    val focus_str =
      "enum_byte_focus " ^ Binding.name_of to_byte_bind ^ " " ^ Binding.name_of from_byte_bind
    val (_, lthy7) = define_from_string focus_bind focus_str lthy6

    (* Step 8: <T>_focus_rep [code abstract] --- discharge the guard of the
       generic enum_byte_focus so the focus is executable.  First prove the guard
       (the two round-trip facts, by induction/if-split as in Step 5); then the
       focus reduces to its real branch prism_to_focus_raw <T>_byte_prism. *)
    val focus_name = Binding.name_of focus_bind
    val focus_def = Proof_Context.get_thm lthy7 (focus_name ^ "_def")
    val to_str = Binding.name_of to_byte_bind
    val from_str = Binding.name_of from_byte_bind
    val guard_prop =
      Syntax.read_prop lthy7
        ("(\<forall>e. " ^ from_str ^ " (" ^ to_str ^ " e) = Some e) \<and> " ^
         "(\<forall>w e. " ^ from_str ^ " w = Some e \<longrightarrow> " ^ to_str ^ " e = w)")
    val rep_simp_ctxt =
      fold Splitter.add_split @{thms if_split if_split_asm} (lthy7 addsimps encoding_simps)
    val guard_thm = Goal.prove lthy7 [] [] guard_prop
      (fn {context = ctxt, ...} =>
        (resolve_tac ctxt @{thms conjI} 1
         THEN resolve_tac ctxt @{thms allI} 1
         THEN resolve_tac ctxt [induct_thm] 1
         THEN ALLGOALS (asm_full_simp_tac rep_simp_ctxt))
        THEN ALLGOALS (asm_full_simp_tac rep_simp_ctxt))
    val rep_prop =
      Syntax.read_prop lthy7
        ("Rep_focus " ^ focus_name ^ " = prism_to_focus_raw " ^ Binding.name_of prism_bind)
    val rep_thm = Goal.prove lthy7 [] [] rep_prop
      (fn {context = ctxt, ...} =>
        Local_Defs.unfold_tac ctxt [focus_def]
        THEN asm_full_simp_tac
               (lthy7 addsimps [@{thm enum_byte_focus.rep_eq}, @{thm if_P} OF [guard_thm], prism_def]) 1)
    val lthy8 = lthy7
      |> Code.declare_abstract_eqn rep_thm
  in
    lthy8
  end

end

(* Parser: `define_byte_enum <name> = <C0>: <d0> | <C1>: <d1> | ...` *)
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>define_byte_enum\<close>
    "define an enumeration type together with its byte serialization"
    (Parse.binding --
      (Parse.$$$ "=" |--
        Parse.enum1 "|" (Parse.binding --| Parse.$$$ ":" -- Parse.nat))
      >> (fn (b, specs) => Byte_Encoding_Enum_Cmd.define_byte_enum b specs))
