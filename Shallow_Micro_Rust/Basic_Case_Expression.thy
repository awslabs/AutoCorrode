(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Basic_Case_Expression
  imports Main
begin
(*>*)

section\<open>Basic \<^text>\<open>case\<close> expressions\<close>

subsection\<open>Motivation\<close>

text\<open>Isabelle/HOL's in-built \<^text>\<open>case\<close> expression allows for pattern matching on specific values
rather than mere constructor shapes. While powerful on the one hand, this may lead to conflict if a
constructor  argument within a \<^text>\<open>case\<close> branch is given a variable name which is also the name of
a constant in  some background theory.\<close>

subsubsection\<open>Toy example\<close>

text\<open>The following example demonstrates the problem: Assuming \<^text>\<open>foo\<close> is undefined, the following
definition and application of an unwrap-with-default operation for \<^term>\<open>nat option\<close> works fine:\<close>

ML\<open>  
let 
   val func = @{term \<open>
     \<lambda>(x_opt :: nat option). 
      case x_opt of 
        Some foo \<Rightarrow> foo
      | None     \<Rightarrow> (0 :: nat)   
   \<close>};
   val arg = @{term \<open>(Some 1) :: nat option\<close>}
in
   Value_Command.value @{context} (func $ arg) \<comment>\<open>Should go through fine!\<close>
end
\<close>

text\<open>However, if \<^text>\<open>foo\<close> is actually a defined constant, the definition either fails to typecheck
or is not what we intended. Note that while here we define \<^text>\<open>foo\<close> ourselves for demonstrative
purposes, the issue in the 'real world' is that you wouldn't necessarily know about the union of all
constants defined in all background theories, silently changing the semantics of your \<^text>\<open>case\<close>
expression. For example, \<^text>\<open>size\<close> would be a common variable name, but it conflicts with
\<^term>\<open>size\<close> from the typeclass \<^class>\<open>Nat.size\<close>.\<close>

ML\<open>  
let 
   val func = @{term \<open>
     \<lambda>(x_opt :: nat option). 
      case x_opt of 
        Some foo \<Rightarrow> foo
      | None     \<Rightarrow> (0 :: nat)  
   \<close>};
   val arg = @{term \<open>(Some 1) :: nat option\<close>}
in
   (Value_Command.value @{context} (func $ arg); ())
      handle Match => writeln "Pattern matching failure!"
end
\<close>

subsection\<open>A simplified \<^text>\<open>case\<close> expression\<close>

text\<open>We add a simpler version of HOL's built-in \<^text>\<open>case\<close> expression which is restricted
to patterns of the form \<^text>\<open>C arg0 arg1 \<dots> argn\<close> where all arguments are identifiers. In
particular, we do not allow nested matches, nor matches where an argument value is fixed.

Luckily, we don't have to re-do all of \<^text>\<open>case\<close> -- which would likelyg also lead to issues
with common pattern matching tactics: The logic of identifying global constants in \<^text>\<open>case\<close>
pattern is part of the "parsing frontend". By merely writing a new parsing frontend, we (hopefully)
get the desired strictier semantics of \<^text>\<open>case\<close> while still leveraging existing "backend"
infrastructure  for HOL's built-in\<^text>\<open>case\<close>.\<close> 

subsubsection\<open>Syntax\<close>

text\<open>Here we define the restricted syntax of our new \<^text>\<open>case\<close>-expression. To avoid clashes with
existing notation, we call it \<^text>\<open>bcase\<close> (for "basic case"). Its syntax is a subset of the
\<^text>\<open>case\<close> syntax.\<close>

nonterminal case_basic_pattern 
nonterminal case_basic_pattern_arg
nonterminal case_basic_pattern_args
nonterminal case_basic_branch
nonterminal case_basic_branches

syntax
  \<comment>\<open>Basic case expressions\<close>
  "_case_basic_syntax" :: "['a, case_basic_branches] \<Rightarrow> 'b"  ("(bcase _ of/ _)" [20, 20]20) 
  \<comment>\<open>Basic case branches\<close>
  "_case_basic1" :: "[case_basic_pattern, 'b] \<Rightarrow> case_basic_branches"  ("(2_ \<Rightarrow>/ _)" [100, 20] 21)
  "_case_basic2" :: "[case_basic_branches, case_basic_branches] \<Rightarrow> case_basic_branches"  ("_/ | _" [21, 20]20)
  \<comment>\<open>Basic case patterns, restricted to constructor identifiers followed by a potentially empty list of argument identifiers\<close>
  "_case_basic_pattern_other" :: \<open>case_basic_pattern\<close>
    ("'_")
  "_case_basic_pattern_constr_no_args" :: \<open>id \<Rightarrow> case_basic_pattern\<close>
    ("_")
  "_case_basic_pattern_constr_with_args" :: \<open>id \<Rightarrow> case_basic_pattern_args \<Rightarrow> case_basic_pattern\<close>
    ("_ _"[1000,100]100)
  "_case_basic_pattern_arg_id" :: \<open>id \<Rightarrow> case_basic_pattern_arg\<close>
    ("_")
  "_case_basic_pattern_arg_dummy" :: \<open>case_basic_pattern_arg\<close>
    ("'_")
  "_case_basic_pattern_arg_pattern" :: \<open>case_basic_pattern \<Rightarrow> case_basic_pattern_arg\<close>
  "_case_basic_pattern_args_single" :: \<open>case_basic_pattern_arg \<Rightarrow> case_basic_pattern_args\<close>
    ("_")
  "_case_basic_pattern_args_app" :: \<open>case_basic_pattern_arg \<Rightarrow> case_basic_pattern_args \<Rightarrow> case_basic_pattern_args\<close>
    ("_ _"[1000,100]100)

subsection\<open>Semantic frontend\<close>

text\<open>Next, we define a parse translation for our new "frontend" \<^text>\<open>bcase\<close> syntax into the existing
"backend" syntax of \<^text>\<open>case\<close>, built from the constants \<^const>\<open>case_abs\<close>, \<^const>\<open>case_nil\<close>, \<^const>\<open>case_cons\<close>,
\<^text>\<open>case_elem\<close> and \<^const>\<open>case_guard\<close>.\<close>  

ML\<open>
  fun print_term (Const(str, _)) = "CONST " ^ str
    | print_term (Free(str,_)) = "FREE " ^ str
    | print_term (Var((name,nr),_)) = "INDEX(" ^ name ^ "," ^ (Int.toString nr)
    | print_term (Bound(_)) = "BOUND"
    | print_term (Abs(str, _, term)) = "%" ^ str ^ " -> " ^ (print_term term)
    | print_term (t $ u) = "(" ^ (print_term t) ^ " $ " ^ (print_term u) ^ ")";

fun case_error s = error ("Error in bcase expression:\n" ^ s);
fun case_tr err ctxt [t, u] =
      let
        fun abs p t =
          Syntax.const \<^const_syntax>\<open>case_abs\<close> $ Term.absfree (p, dummyT) t;

        fun pattern_args_destruct (Const( \<^syntax_const>\<open>_case_basic_pattern_args_single\<close>,_) $ t) = [t]
          | pattern_args_destruct (Const( \<^syntax_const>\<open>_case_basic_pattern_args_app\<close>,_) $ t $ rem) = t :: (pattern_args_destruct rem)
          | pattern_args_destruct t = case_error ("invalid constructor argument list:" ^ (print_term t))

        fun pattern_get_constructor (Const (\<^syntax_const>\<open>_case_basic_pattern_constr_with_args\<close>, _) $ c $ _) = c
          | pattern_get_constructor (Const (\<^syntax_const>\<open>_case_basic_pattern_constr_no_args\<close>,_) $ c) = c
          | pattern_get_constructor t = case_error ("get_constructor -- invalid pattern: " ^ (print_term t))

        fun pattern_build_term constructor args  =  
               fold (fn a => fn b => (b $ a)) args constructor

        fun dest_id_name id =
              (fst (Term.dest_Free id))
                handle TERM _ => case_error ("invalid pattern identifier: " ^ (print_term id))

        fun known_constructor_name ctxt name =
              let
                val full = Proof_Context.intern_const ctxt name
                val thy = Proof_Context.theory_of ctxt
              in
                if can (Sign.the_const_type thy) full andalso Code.is_constr thy full
                then SOME full
                else NONE
              end

        fun resolve_constructor_id _ (id as Const _) = id
          | resolve_constructor_id ctxt (Free (name, _)) =
              (case known_constructor_name ctxt name of
                SOME full => Syntax.const full
              | NONE => Free (name, dummyT))
          | resolve_constructor_id ctxt t = t

        fun is_constructor_id ctxt id =
              (case id of
                Const _ => true
              | Free (name, _) => Option.isSome (known_constructor_name ctxt name)
              | _ => false)

        fun is_binding_id ctxt id =
              (case id of
                Free _ => not (is_constructor_id ctxt id)
              | _ => false)

        fun strip_convert_arg t =
              (case t of
                Const (name, _) $ u =>
                  if name = "_urust_shallow_match_convert_arg" then strip_convert_arg u else t
              | _ => t)

        fun strip_convert_pattern t =
              (case t of
                Const (name, _) $ u =>
                  if name = "_urust_shallow_match_convert_pattern" then strip_convert_pattern u
                  else if name = "_shallow_match_pattern" then strip_convert_pattern u
                  else t
              | _ => t)

        fun shallow_args_destruct (Const ("_urust_shallow_match_pattern_args_single", _) $ t) = [t]
          | shallow_args_destruct (Const ("_urust_shallow_match_pattern_args_app",_) $ t $ rem) =
              t :: (shallow_args_destruct rem)
          | shallow_args_destruct t = case_error ("invalid shallow constructor argument list:" ^ (print_term t))

        fun urust_args_destruct (Const ("_urust_match_pattern_args_single", _) $ t) = [t]
          | urust_args_destruct (Const ("_urust_match_pattern_args_app",_) $ t $ rem) =
              t :: (urust_args_destruct rem)
          | urust_args_destruct t = case_error ("invalid urust constructor argument list:" ^ (print_term t))

        fun collect_ids_from_pattern pat =
              (case strip_convert_pattern pat of
                Const (\<^syntax_const>\<open>_case_basic_pattern_constr_with_args\<close>, _) $ _ $ args =>
                  fold (fn a => fn acc => (collect_ids_from_arg a) @ acc) (pattern_args_destruct args) []
              | Const (\<^syntax_const>\<open>_case_basic_pattern_constr_no_args\<close>,_) $ id =>
                  if is_binding_id ctxt id then [dest_id_name id] else []
              | Const (\<^syntax_const>\<open>_case_basic_pattern_other\<close>, _) => []
              | Const ("_urust_shallow_match_pattern_constr_with_args", _) $ _ $ args =>
                  fold (fn a => fn acc => (collect_ids_from_arg a) @ acc) (shallow_args_destruct args) []
              | Const ("_urust_shallow_match_pattern_constr_no_args",_) $ id =>
                  if is_binding_id ctxt id then [dest_id_name id] else []
              | Const ("_urust_shallow_match_pattern_other", _) => []
              | Const ("_urust_match_pattern_constr_with_args", _) $ _ $ args =>
                  fold (fn a => fn acc => (collect_ids_from_pattern a) @ acc) (urust_args_destruct args) []
              | Const ("_urust_match_pattern_constr_no_args",_) $ id =>
                  if is_binding_id ctxt id then [dest_id_name id] else []
              | Const ("_urust_match_pattern_other", _) => []
              | t => case_error ("collect_ids -- invalid pattern: " ^ (print_term t)))
        and collect_ids_from_arg arg =
              (case strip_convert_arg arg of
                Const (\<^syntax_const>\<open>_case_basic_pattern_arg_id\<close>,_) $ id => [dest_id_name id]
              | Const (\<^syntax_const>\<open>_case_basic_pattern_arg_pattern\<close>,_) $ pat => collect_ids_from_pattern pat
              | Const (\<^syntax_const>\<open>_case_basic_pattern_arg_dummy\<close>, _) => []
              | Const ("_urust_shallow_match_pattern_arg_id", _) $ id => [dest_id_name id]
              | Const ("_urust_shallow_match_pattern_arg_pattern", _) $ pat => collect_ids_from_pattern pat
              | Const ("_urust_shallow_match_pattern_arg_dummy", _) => []
              | t =>
                  (collect_ids_from_pattern t
                    handle ERROR _ =>
                      case_error ("collect_ids -- invalid pattern arg: " ^ (print_term t))))

        fun pattern_arg_to_term arg used =
              (case strip_convert_arg arg of
                Const ( \<^syntax_const>\<open>_case_basic_pattern_arg_dummy\<close>, _) =>
                  let val (x, used') = Name.variant "x" used
                  in (Free (x, dummyT), [x], used') end
              | (Const (\<^syntax_const>\<open>_case_basic_pattern_arg_id\<close>,_)) $ id =>
                  (id, [dest_id_name id], used)
              | (Const (\<^syntax_const>\<open>_case_basic_pattern_arg_pattern\<close>,_)) $ pat =>
                  pattern_term_of_pattern pat used
              | (Const ("_urust_shallow_match_pattern_arg_id",_)) $ id =>
                  (id, [dest_id_name id], used)
              | (Const ("_urust_shallow_match_pattern_arg_pattern",_)) $ pat =>
                  pattern_term_of_pattern pat used
              | Const ("_urust_shallow_match_pattern_arg_dummy", _) =>
                  let val (x, used') = Name.variant "x" used
                  in (Free (x, dummyT), [x], used') end
              | t =>
                  (pattern_term_of_pattern t used
                    handle ERROR _ =>
                      case_error ("invalid pattern argument: " ^ (print_term t))))

        and pattern_args_to_terms [] used = ([], [], used)
          | pattern_args_to_terms (t :: ts) used =
                let val (t', binders, used') = pattern_arg_to_term t used
                    val (ts', binders', used'') = pattern_args_to_terms ts used'
                in (t' :: ts', binders @ binders', used'') end

        and pattern_term_of_pattern pat used =
              (case strip_convert_pattern pat of
                Const (\<^syntax_const>\<open>_case_basic_pattern_constr_with_args\<close>, _) $ c $ args =>
                  let val args' = pattern_args_destruct args
                      val (arg_terms, binders, used') = pattern_args_to_terms args' used
                  in (pattern_build_term (resolve_constructor_id ctxt c) arg_terms, binders, used') end
              | Const (\<^syntax_const>\<open>_case_basic_pattern_constr_no_args\<close>,_) $ c =>
                  if is_binding_id ctxt c
                  then (c, [dest_id_name c], used)
                  else (resolve_constructor_id ctxt c, [], used)
              | Const (\<^syntax_const>\<open>_case_basic_pattern_other\<close>, _) =>
                  let val (x, used') = Name.variant "x" used
                  in (Free (x, dummyT), [x], used') end
              | Const ("_urust_shallow_match_pattern_constr_with_args", _) $ c $ args =>
                  let val args' = shallow_args_destruct args
                      val (arg_terms, binders, used') = pattern_args_to_terms args' used
                  in (pattern_build_term (resolve_constructor_id ctxt c) arg_terms, binders, used') end
              | Const ("_urust_shallow_match_pattern_constr_no_args", _) $ c =>
                  if is_binding_id ctxt c
                  then (c, [dest_id_name c], used)
                  else (resolve_constructor_id ctxt c, [], used)
              | Const ("_urust_shallow_match_pattern_other", _) =>
                  let val (x, used') = Name.variant "x" used
                  in (Free (x, dummyT), [x], used') end
              | Const ("_urust_match_pattern_constr_with_args", _) $ c $ args =>
                  let val args' = urust_args_destruct args
                      val (arg_terms, binders, used') = pattern_args_to_terms args' used
                  in (pattern_build_term (resolve_constructor_id ctxt c) arg_terms, binders, used') end
              | Const ("_urust_match_pattern_constr_no_args", _) $ c =>
                  if is_binding_id ctxt c
                  then (c, [dest_id_name c], used)
                  else (resolve_constructor_id ctxt c, [], used)
              | Const ("_urust_match_pattern_other", _) =>
                  let val (x, used') = Name.variant "x" used
                  in (Free (x, dummyT), [x], used') end
              | t => case_error ("invalid pattern: " ^ (print_term t)))

        fun handle_pattern (Const (\<^syntax_const>\<open>_case_basic_pattern_other\<close>, _)) exp = 
            let val (constr_str, _) = Name.variant "C" (Term.declare_free_names t Name.context)
                val constr = Free (constr_str, dummyT) in
                abs constr_str (Syntax.const \<^const_syntax>\<open>case_elem\<close> $ constr $ exp) end
          | handle_pattern pattern exp =
            let val used0 = Term.declare_free_names exp Name.context
                val used = fold Name.declare (collect_ids_from_pattern pattern) used0
                val (term, binders, _) = pattern_term_of_pattern pattern used
            in fold abs binders (Syntax.const \<^const_syntax>\<open>case_elem\<close> $ term $ exp) end

        fun dest_case_basic1 (Const (\<^syntax_const>\<open>_case_basic1\<close>, _) $ pattern $ exp) = 
            handle_pattern pattern exp
          | dest_case_basic1 _ = case_error "dest_case_basic1";

        fun dest_case_basic2 (Const (\<^syntax_const>\<open>_case_basic2\<close>, _) $ t $ u) = t :: dest_case_basic2 u
          | dest_case_basic2 t = [t];

        val errt = Syntax.const (if err then \<^const_syntax>\<open>True\<close> else \<^const_syntax>\<open>False\<close>);
      in
        Syntax.const \<^const_syntax>\<open>case_guard\<close> $ errt $ t $
          (fold_rev
            (fn t => fn u => Syntax.const \<^const_syntax>\<open>case_cons\<close> $ dest_case_basic1 t $ u)
            (dest_case_basic2 u)
            (Syntax.const \<^const_syntax>\<open>case_nil\<close>))
      end
  | case_tr _ _ _ = case_error "case_tr";

val _ = Theory.setup (Sign.parse_translation [(\<^syntax_const>\<open>_case_basic_syntax\<close>, case_tr true)]);
structure Basic_Case_Expression = struct val case_tr = case_tr end;
\<close>

subsubsection\<open>Some tests\<close>

datatype test_type = C_Test_One nat  | C_Test_Two nat nat | C_Test_Three nat nat nat

term\<open>\<lambda>(tst :: test_type).
        let x :: nat = 42 in
        let xa :: nat = 42 in 
        bcase (\<lambda>x. x) tst of 
           C_Test_Two a b \<Rightarrow> (a + b)
         | C_Test_One _ \<Rightarrow> x + xa \<comment>\<open>Test that we don't insert used identifiers for wildcards\<close>
         | _ \<Rightarrow> x\<close>

term\<open>\<lambda>(t :: bool).
          bcase t of
            True \<Rightarrow> False
          | False \<Rightarrow> True\<close>  

value\<open>unwrap_default_0 (Some (1 :: nat))\<close>


(*<*)
end
(*>*)
