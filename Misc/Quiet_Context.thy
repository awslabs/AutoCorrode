(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Quiet_Context
  imports Pure
  keywords "quiet_context" :: thy_decl_block
begin
(*>*)

section\<open>Opening a named context without printing it\<close>

text\<open>\<^theory_text>\<open>quiet_context\<close> is logically the same command as
\<^theory_text>\<open>context\<close>. It differs only in that it prints nothing.

\<^theory_text>\<open>quiet_context name begin\<close> and
\<^theory_text>\<open>quiet_context name opening bundles begin\<close> accept exactly the named forms of
\<^theory_text>\<open>context\<close>. They build the local theory with the same function that
\<^theory_text>\<open>context\<close> uses, \<^ML>\<open>Target_Context.context_begin_named_cmd\<close>, on the same
arguments. The resulting context is therefore identical: the same target, fixes, assumptions,
facts, constants, syntax and bundle declarations. Everything declared inside the block goes to the
target exactly as it would under \<^theory_text>\<open>context\<close>. The block is closed by
\<^theory_text>\<open>end\<close>, and \<^theory_text>\<open>end\<close> behaves the same way. Replacing
\<^theory_text>\<open>context\<close> by \<^theory_text>\<open>quiet_context\<close>, or back, changes no fact and
no proof obligation.

The one difference is output. \<^theory_text>\<open>context name begin\<close> always prints the target it
opens, and Isabelle offers no option to turn this off. For a locale, building that text initializes
the locale a second time and activates all of its elements again. This can cost as much as opening
the locale itself, and the text is rarely read. \<^theory_text>\<open>quiet_context\<close> skips it. Use
\<^theory_text>\<open>print_locale\<close> or \<^theory_text>\<open>print_context\<close> when the text is
needed.

The anonymous form \<^theory_text>\<open>context fixes \<dots> begin\<close> is not supported. It prints
nothing already, so there is nothing to skip.\<close>

ML\<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>quiet_context\<close>
    "begin named local theory context without printing the target"
    ((Parse.name_position -- Scan.optional Parse_Spec.opening []) --| Parse.begin
      >> (fn (name, incls) =>
        Toplevel.generic_theory
          (fn Context.Theory thy =>
                Context.Proof (Target_Context.context_begin_named_cmd incls name thy)
            | Context.Proof _ => error "quiet_context: not at theory level")));
\<close>

(*<*)
end
(*>*)
