(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Examples
  imports Separation_Logic_Tactics
begin

section\<open>Examples for custom tactics and helper functions\<close>

subsection\<open>Miscellaneous\<close>

subsubsection\<open>Remove duplicate premises\<close>

lemma
  assumes \<open>P x\<close>
      and \<open>Q y\<close>
      and \<open>P z\<close>
      and \<open>P x\<close>
      and \<open>Q z\<close>
      and \<open>Q y\<close>
      and \<open>Q y\<close>
    shows T
  using assms apply -
  apply (tactic \<open>remove_duplicate_pure_premises @{context} 1\<close>)
  (* This should drop 'P x' and 'Q y' at positions 3, 5, and 6, respectively (0-based) *)
  oops

subsubsection\<open>Remove unnecessary universal quantification\<close>

lemma \<open>\<And>t x y z. P z\<close>
  (* \<And>t x y z. P x z *)
  apply (tactic \<open>CONVERSION (remove_unneeded_meta_quantification_conv @{context}) 1\<close>)
  (* Trying again will fail *)
  (* apply (tactic \<open>CONVERSION (remove_unused_meta_quantifications) 1\<close>) *)
  oops

lemma \<open>\<And>t x y z. P x z\<close>
  (* \<And>t x y z. P x z *)
  apply (tactic \<open>remove_unneeded_meta_quantification @{context} 1\<close>)
  (* \<And>x z. P x z *)
  oops

subsection\<open>Separation logic\<close>

subsubsection\<open>Normalizing associativity of separating conjunctions\<close>

notepad
begin
  fix \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<theta> \<tau> :: \<open>'s::sepalg assert\<close>
  have \<open>(\<alpha> \<star> (\<beta> \<star> \<gamma>)) \<star> ((\<delta> \<star> \<epsilon>) \<star> \<theta>) \<longlongrightarrow> (\<alpha> \<star> (\<beta> \<star> \<gamma>)) \<star> ((\<delta> \<star> \<epsilon>) \<star> \<theta>)\<close>
    apply (aentails_normalize_assoc)
    by (rule aentails_refl)
next
  \<comment>\<open>Normalize LHS only\<close>
  fix \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<theta> \<tau> :: \<open>'s::sepalg assert\<close>
  have \<open>(\<alpha> \<star> (\<beta> \<star> \<gamma>)) \<star> ((\<delta> \<star> \<epsilon>) \<star> \<theta>) \<longlongrightarrow> \<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<epsilon> \<star> \<theta>\<close>
    apply (aentails_normalize_assoc_assms)
    by (rule aentails_refl)
next
  \<comment>\<open>Normalize RHS only\<close>
  fix \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<theta> \<tau> :: \<open>'s::sepalg assert\<close>
  have \<open>\<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<epsilon> \<star> \<theta>  \<longlongrightarrow> (\<alpha> \<star> (\<beta> \<star> \<gamma>)) \<star> ((\<delta> \<star> \<epsilon>) \<star> \<theta>)\<close>
    apply (aentails_normalize_assoc_concls)
    by (rule aentails_refl)
end

subsubsection\<open>Rotating spatial premises and goals\<close>

notepad
begin
  fix \<phi> \<psi> :: \<open>'s::sepalg assert\<close>
  have \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<psi> \<star> \<phi>\<close>
    by (asepconj_rotate_assms, rule aentails_refl)
next
  fix \<phi> \<psi> \<xi> \<tau> \<epsilon> :: \<open>'s::sepalg assert\<close>
  have \<open>(\<phi> \<star> \<psi> \<star> \<xi> \<star> \<tau> \<star> \<epsilon> \<longlongrightarrow> \<xi> \<star> \<tau> \<star> \<epsilon> \<star> \<phi> \<star> \<psi>)\<close>
    apply (asepconj_rotate_assms)
    apply (aentails_rotate_concls)
    \<comment>\<open>Can also call the the underlying tactic directly\<close>
    apply (tactic\<open>Separation_Logic_Tactics.aentails_rotate_concls_tac @{context} 1\<close>)
    apply (aentails_rotate_concls)
    apply (aentails_rotate_concls)
    by (rule aentails_refl)
next
  fix \<phi> \<psi> :: \<open>'s::sepalg assert\<close>
  have \<open>\<phi> \<star> \<psi> \<longlongrightarrow> \<psi> \<star> \<phi>\<close>
    apply (tactic\<open>Separation_Logic_Tactics.aentails_rotate_assms_tac @{context} 1\<close>)
    by (rule aentails_refl)
next
  fix \<phi> \<psi> \<xi> :: \<open>'s::sepalg assert\<close>
  have \<open>\<forall>\<tau> \<epsilon>. (\<phi> \<star> \<psi> \<star> \<xi> \<star> \<tau> \<star> \<epsilon> \<longlongrightarrow> \<xi> \<star> \<tau> \<star> \<epsilon> \<star> \<phi> \<star> \<psi>)\<close>
    apply clarsimp
    apply (asepconj_rotate_assms)
    apply (aentails_rotate_concls)
    apply (aentails_rotate_concls)
    apply (aentails_rotate_concls)
    apply (aentails_rotate_concls)
    by (rule aentails_refl)
end

subsubsection\<open>Picking spatial premises and conclusions\<close>

notepad
begin
  fix \<phi> \<psi> \<gamma> :: \<open>'s::sepalg assert\<close>
  have \<open>\<phi> \<star> \<psi> \<star> \<gamma> \<longlongrightarrow> \<psi> \<star> \<phi> \<star> \<gamma>\<close>
    apply (aentails_pick_concl 1)
    apply (rule aentails_refl)
    done
next
  fix \<phi> \<psi> \<gamma> :: \<open>'s::sepalg assert\<close>
  have \<open>\<phi> \<star> \<psi> \<star> \<gamma> \<longlongrightarrow> \<psi> \<star> \<phi> \<star> \<gamma>\<close>
    \<comment>\<open>Can also call the underlying tactic directly\<close>
    apply (tactic \<open>Separation_Logic_Tactics.aentails_pick_concls_tac 1 @{context} 1\<close>)
    apply (rule aentails_refl)
    done
next
  fix \<phi> \<psi> \<xi> :: \<open>'s::sepalg assert\<close>
  have \<open>\<phi> \<star> \<psi> \<star> \<xi> \<longlongrightarrow> \<xi> \<star> \<psi> \<star> \<phi>\<close>
    apply (aentails_pick_concl 1)
    apply (aentails_pick_assm 1)
    apply (aentails_pick_concl 1)
    apply (aentails_pick_assm 2)
    apply (rule aentails_refl)
    done
next
  fix \<phi> \<psi> \<xi> :: \<open>'s::sepalg assert\<close>
  have \<open>\<phi> \<star> \<psi> \<star> \<xi> \<longlongrightarrow> \<xi> \<star> \<psi> \<star> \<phi>\<close>
    \<comment>\<open>Chain underlying tactics at level of ML\<close>
    apply (tactic\<open>(
            Separation_Logic_Tactics.aentails_pick_concls_tac 1 @{context}
      THEN' Separation_Logic_Tactics.aentails_pick_assms_tac  1 @{context}
      THEN' Separation_Logic_Tactics.aentails_pick_concls_tac 1 @{context}
      THEN' Separation_Logic_Tactics.aentails_pick_assms_tac  2 @{context}
    ) 1\<close>)
    apply (rule aentails_refl)
    done
next
  \<comment>\<open>Can also explicitly specify the number of separating components to be
  considered. This makes a difference when a suffix of a separation conjunction
  should be moved.\<close>
  fix \<phi> \<psi> \<xi> :: \<open>'s::sepalg assert\<close>
  have \<open>\<psi> \<star> \<phi> \<star> \<xi> \<longlongrightarrow> \<xi> \<star> \<psi> \<star> \<phi>\<close>
    \<comment>\<open>Views \<^verbatim>\<open>\<xi> \<star> \<psi> \<star> \<phi>\<close> as 2-component conjunction  \<^verbatim>\<open>\<xi> \<star> (\<psi> \<star> \<phi>)\<close> and hoists \<^verbatim>\<open>\<psi> \<star> \<phi>\<close>:\<close>
    apply (aentails_pick_concl_ext 2 1)
    apply (aentails_normalize_assoc)
    apply (rule aentails_refl)
    done  
end

subsubsection\<open>Floating assumptions/conclusions\<close>

text\<open>There is tactic support for floating pure assumptions and conclusions:\<close>

schematic_goal \<open>\<delta> \<star> \<alpha> \<star> ?\<beta> r \<star> \<langle>\<gamma>\<rangle> \<longlongrightarrow> \<delta> \<star> \<langle>\<gamma>\<rangle> \<star> \<langle>\<beta> r\<rangle> \<star> \<alpha>\<close>
  apply (asepconj_rotate_assms)
  apply (aentails_float_pure_concls)
  apply (aentails_float_pure_assms)
  oops

notepad
begin
  fix \<phi> \<phi>' \<xi> :: \<open>'s::sepalg assert\<close> and P Q R :: \<open>bool\<close>
  have \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
    by (aentails_float_pure_assms, aentails_float_pure_concls, rule aentails_refl)
next
  fix \<phi> \<phi>' \<xi> :: \<open>'s::sepalg assert\<close> and P Q R :: \<open>bool\<close>
  have \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
    \<comment>\<open>Float assumptions and conclusions at the same time\<close>
    by (aentails_float_pure, rule aentails_refl)
next
  fix \<phi> \<phi>' \<xi> :: \<open>'s::sepalg assert\<close> and P Q R :: \<open>bool\<close>
  have \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
    by (aentails_float_pure, rule aentails_refl)
end

text\<open>There is also special support for floating iterated separating conjunctions:\<close>

notepad
begin
  fix \<phi> \<psi> \<xi> :: \<open>'s::sepalg assert\<close>
  fix \<Phi> :: \<open>'s assert multiset\<close>
  have \<open>\<phi> \<star> \<xi> \<star> \<star>\<star>\<Phi>  \<longlongrightarrow> \<star>\<star>\<Phi> \<star> \<phi> \<star> \<xi>\<close>
    apply aentails_float_multi_assms
    apply (rule aentails_refl)
    done
end

text\<open>There is also support for floating points to assumptions:\<close>

context reference
begin
lemma \<open>\<phi>' \<star> r0\<mapsto>\<langle>sh0\<rangle> g0\<down>v0 \<star> \<phi> \<star> r1\<mapsto>\<langle>sh1\<rangle> g1\<down>v1 \<longlongrightarrow> \<psi>\<close>
  apply aentails_float_points_to_assms
  oops
end

subsubsection\<open>Floating matching premises/conclusions\<close>

text\<open>For cancellation, one needs to detect pairs of spatial premises and conclusions that are
in some sense matching -- for example, unifiable.

The most general tactic on the ML level is  \<^verbatim>\<open>aentails_float_match\<close>, which takes a filter
function on pairs of premises/conclusions and floats matching pairs.\<close>

notepad
begin
  \<comment>\<open>Artifical example where we match and float assumptions that are free variables and one
  variable's name is a suffix of the other.\<close>
  fix ink chink \<alpha> \<beta> \<gamma> \<delta> :: \<open>'s::sepalg assert\<close>
  assume R: \<open>ink \<star> \<alpha> \<star> \<beta> \<longlongrightarrow> chink \<star> \<gamma> \<star> \<delta>\<close>
  have \<open>\<alpha> \<star> ink \<star> \<beta> \<longlongrightarrow> \<gamma> \<star> \<delta> \<star> chink\<close>
    ML_prf\<open>fun filter termA termB = let
      val sA = Term.dest_Free termA |> fst
      val sB = Term.dest_Free termB |> fst
      val _ = sA |> tracing
      val _ = sB |> tracing
      in
        String.isSuffix sA sB orelse String.isSuffix sB sA
      end
    \<close>
    apply (tactic \<open>Separation_Logic_Tactics.aentails_float_match @{context} filter 1\<close>)
    apply (rule R)
    done
end

text\<open>This can for example be specialized to float matching pairs of iterated separating conjunctions:\<close>

notepad
begin   
     fix \<phi> \<psi>
     and lst lst' :: \<open>'t list\<close>
     and \<xi> \<xi>' :: \<open>'t \<Rightarrow> 's::sepalg assert\<close>
  assume 1: \<open>\<star>\<star> {# \<xi> \<Colon> lst #} \<star> \<phi> \<star> \<psi> \<longlongrightarrow> \<star>\<star> {# \<xi> \<Colon> lst' #} \<star> \<phi> \<star> \<psi> \<star> \<star>\<star> {# \<xi>' \<Colon> lst' #}\<close>
  have \<open>\<phi> \<star> \<star>\<star>{# \<xi> \<Colon> lst #} \<star> \<psi> \<longlongrightarrow> \<phi> \<star> \<psi> \<star> \<star>\<star>{# \<xi> \<Colon> lst' #} \<star> \<star>\<star>{# \<xi>' \<Colon> lst' #}\<close>
    apply (tactic \<open>Separation_Logic_Tactics.aentails_float_matching_iterated_asepconj @{context} 1\<close>)
    apply (rule 1)
    done
next
  \<comment>\<open>Permuted version of previous example, to show that hoisting of \<^verbatim>\<open>\<xi>\<close> was not a coincidence:\<close>
     fix \<phi> \<psi>
     and lst lst' :: \<open>'t list\<close>
     and \<xi> \<xi>' \<xi>'' \<xi>''' :: \<open>'t \<Rightarrow> 's::sepalg assert\<close>
  assume 1: \<open>\<star>\<star> {# \<xi> \<Colon> lst #} \<star> \<star>\<star> {# \<xi>''' \<Colon> lst' #} \<star> \<phi> \<star> \<psi> \<longlongrightarrow> \<star>\<star> {# \<xi> \<Colon> lst' #} \<star> \<star>\<star> {# \<xi>'' \<Colon> lst' #} \<star> \<phi> \<star> \<psi> \<star> \<star>\<star> {# \<xi>' \<Colon> lst' #}\<close>
  have \<open>\<star>\<star>{# \<xi>''' \<Colon> lst' #} \<star> \<phi> \<star> \<star>\<star>{# \<xi> \<Colon> lst #} \<star> \<psi> \<longlongrightarrow> \<star>\<star>{# \<xi>'' \<Colon> lst' #} \<star> \<phi> \<star> \<psi> \<star> \<star>\<star>{# \<xi> \<Colon> lst' #} \<star> \<star>\<star>{# \<xi>' \<Colon> lst' #}\<close>
    apply (tactic \<open>Separation_Logic_Tactics.aentails_float_matching_iterated_asepconj @{context} 1\<close>)
    apply (rule 1)
    done
end

text\<open>It can also be applied to find pairs of \<^verbatim>\<open>points_to\<close> assertions with the same underlying
reference. Those must be cancellable if the target entailment holds, so even if the values behind
the references are not yet known to be equal, it makes sense to lift the \<^verbatim>\<open>points_to\<close>
assertions:\<close>

context reference
begin
lemma \<open>\<phi>' \<star> r\<mapsto>\<langle>sh\<rangle> g0 \<star> \<phi> \<longlongrightarrow> \<psi> \<star> r\<mapsto>\<langle>sh\<rangle> g1\<close>
  apply (tactic \<open>Separation_Logic_Tactics.asepconj_match_float_points_to_raw_tac @{context} 1\<close>)
  oops

text\<open>It also works for typed references:\<close>

lemma \<open>\<phi>' \<star> r\<mapsto>\<langle>sh\<rangle> g0\<down>v0 \<star> \<phi> \<longlongrightarrow> \<psi> \<star> r\<mapsto>\<langle>sh\<rangle> g1\<down>v1\<close>
  apply (tactic \<open>Separation_Logic_Tactics.asepconj_match_float_points_to_tac @{context} 1\<close>)
  oops

end

subsubsection\<open>Floating assumptions/conclusions, with backtracking\<close>

text\<open>When there are multiple assertions to be floated, an alternative to floating them all at once
is to float one a time and present the different results as alternative tactic outcomes that can be
traversed using backtracking.\<close>

notepad
begin
  fix \<phi> \<phi>' \<xi> :: \<open>'s::sepalg assert\<close> and P Q R :: \<open>bool\<close>
  have \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
    apply aentails_float_pure_assms' \<comment>\<open>Happens to float \<^verbatim>\<open>R\<close>, but other options are available
                                        through backtracking\<close>
    back back
    apply aentails_float_pure_assms
    apply aentails_float_pure_concls
    apply (rule aentails_refl)
    done
next
  \<comment>\<open>Manual backtracking is bad style, but can be powerful in conjunction with the \<^verbatim>\<open>;\<close> operator
  for tactic chaining. For example, in the following example, there are multiple options for floating
  a pure assumption to the front, but only one allows the subsequent application of the introduction
  rule \<^verbatim>\<open>asepconj_mono\<close>:\<close>
  fix \<phi> \<phi>' \<xi> :: \<open>'s::sepalg assert\<close> and P Q R :: \<open>bool\<close>
  have \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>Q\<rangle> \<star> \<langle>P\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
    \<comment>\<open>Backtracking forces floating of \<^verbatim>\<open>Q\<close>, which is not the first choice as we have seen above.\<close>
    apply (aentails_float_pure_assms'; intro asepconj_mono)
    apply aentails_float_pure_assms
    apply aentails_float_pure_concls
    apply (rule aentails_refl)
    done
end

text\<open>Other floating tactics have backtracking versions as well; here's an example for
floating of points to assertions:\<close>

context reference
begin
lemma \<open>\<phi>' \<star> r0\<mapsto>\<langle>sh0\<rangle> g0\<down>v0 \<star> \<phi> \<star> r1\<mapsto>\<langle>sh1\<rangle> g1\<down>v1 \<longlongrightarrow> \<psi>\<close>
  apply aentails_float_points_to_assms' \<comment>\<open>Float one \<^verbatim>\<open>points_to\<close> at a time\<close>
  back \<comment>\<open>Try a different one\<close>
  oops
end

subsubsection\<open>Hoisting pure assumptions/conclusions\<close>

notepad
begin
     fix \<phi> \<phi>' \<xi> :: \<open>'s::sepalg assert\<close>
     and P Q R :: \<open>bool\<close>
  assume \<open>ucincl \<phi>\<close>
     and 1: \<open>\<phi> \<star> \<phi>' \<longlongrightarrow> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
  from this have \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
    apply aentails_hoist_pure_assms
    apply (rule 1)
    done
next
     fix \<phi> \<phi>' \<xi> :: \<open>'s::sepalg assert\<close>
     and P Q R :: \<open>bool\<close>
  assume \<open>ucincl \<phi>\<close>
     and 1: \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>P\<rangle>\<close>
     and 2: \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>Q\<rangle>\<close>
     and 2: \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>R\<rangle>\<close>
     and \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<phi> \<star> \<phi>'\<close>
  from this have \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
    apply aentails_hoist_pure_concls
    apply auto
    done
end

subsubsection\<open>Entailment cancellation\<close>

text\<open>Entailment cancellation detects pairs of unifiable spatial premises and conclusions
and cancels them.

Note that cancellation is not necessarily safe: Pure premises may be lost during cancellation
which they shouldn't since they are duplicable. This could be addressed by retaining the
\<^verbatim>\<open>is_sat\<close> of the precondition, but this is currently not happening.\<close>

notepad
begin
  fix \<phi> \<psi> \<xi> \<tau> :: \<open>'s::sepalg assert\<close>
  assume \<open>\<psi> \<longlongrightarrow> \<xi>\<close>
  from this have \<open>\<phi> \<star> \<psi> \<star> \<tau> \<longlongrightarrow> \<tau> \<star> \<xi> \<star> \<phi>\<close>
    \<comment>\<open>\<^verbatim>\<open>aentails_cancel_once\<close> makes a single attempt at cancellation.\<close>
    apply aentails_cancel_once
    apply aentails_cancel_once
    by assumption
next
  \<comment>\<open>Same example, but this time with \<^verbatim>\<open>aentails_cancel\<close>, which repeats \<^verbatim>\<open>aentails_cancel_once\<close>:\<close>
  fix \<phi> \<psi> \<xi> \<tau> :: \<open>'s::sepalg assert\<close>
  assume \<open>\<psi> \<longlongrightarrow> \<xi>\<close>
  from this have \<open>\<phi> \<star> \<psi> \<star> \<tau> \<longlongrightarrow> \<tau> \<star> \<xi> \<star> \<phi>\<close>
    by aentails_cancel assumption
next
  fix \<phi> \<psi> \<xi> :: \<open>'s::sepalg assert\<close>
  fix \<Phi> :: \<open>'s assert multiset\<close>
  have \<open>\<phi> \<star> \<xi> \<star> \<star>\<star>\<Phi>  \<longlongrightarrow> \<star>\<star>\<Phi> \<star> \<phi> \<star> \<xi>\<close>
    apply (aentails_float_multi_assms)
    apply (rule aentails_refl)
    done
end

text\<open>Cancellation is also able to match and cancel iterated separating conjunctions, provided
their bodies match:\<close>

notepad
begin   
     fix \<phi> \<psi>
     and lst lst' :: \<open>'t list\<close>
     and \<xi> :: \<open>'t \<Rightarrow> 's::sepalg assert\<close>
  assume \<open>\<star>\<star> {# \<xi> . mset lst - mset lst' #} \<star> \<phi> \<star> \<psi> \<longlongrightarrow> \<star>\<star> {# \<xi> . mset lst' - mset lst #} \<star> \<phi> \<star> \<psi>\<close>
  from this have \<open>\<phi> \<star> \<star>\<star>{# \<xi> \<Colon> lst #} \<star> \<psi> \<longlongrightarrow> \<phi> \<star> \<psi> \<star> \<star>\<star>{# \<xi> \<Colon> lst' #}\<close>
    apply aentails_cancel_asepconj_multi
    apply auto
    done
end

text\<open>Finally, cancellation can handle matching \<^verbatim>\<open>points_to\<close> and \<^verbatim>\<open>points_to_raw\<close> assertions:
If reference and share match between a points to premise and goal, they will be cancelled, leaving
the pure goals of showing that the pointed-to values are the same:\<close>

context reference
begin

lemma \<open>\<phi>' \<star> r\<mapsto>\<langle>sh\<rangle> g \<star> \<phi> \<longlongrightarrow> \<psi> \<star> r\<mapsto>\<langle>sh\<rangle> g' \<star> r'\<mapsto>\<langle>sh\<rangle> g''\<close>
  apply aentails_cancel_points_to_raw
  oops

lemma \<open>\<phi>' \<star> r\<mapsto>\<langle>sh\<rangle> g\<down>v \<star> \<phi> \<longlongrightarrow> \<psi> \<star> r\<mapsto>\<langle>sh\<rangle> g'\<down>v' \<star> r'\<mapsto>\<langle>sh\<rangle> g''\<close>
  apply aentails_cancel_points_to
  oops

lemma \<open>\<phi>' \<star>( \<flat> r\<mapsto>\<langle>sh\<rangle> g) \<star> \<phi> \<longlongrightarrow> \<psi> \<star> (r\<mapsto>\<langle>sh\<rangle> g\<down>v) \<star> (r'\<mapsto>\<langle>sh\<rangle> g'\<down>v')\<close>
  apply aentails_cancel_points_to_raw_with_typed
  oops

end

experiment
  fixes f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::sepalg assert\<close>
begin

lemma f_cong:
  assumes \<open>b = b'\<close>
  shows \<open>f a b \<longlongrightarrow> f a b'\<close>
  using assms by (simp add: aentails_refl)

lemma
  assumes \<open>b = b'\<close>
      and \<open>\<alpha> \<star> \<beta> \<star> \<gamma> \<longlongrightarrow> \<delta> \<star> \<theta>\<close>
    shows \<open>\<alpha> \<star> \<beta> \<star> f a b \<star> \<gamma> \<longlongrightarrow> \<delta> \<star> f a b' \<star> \<theta>\<close>
  apply (aentails_crule f_cong)
  using assms apply auto
  done

end

subsubsection\<open>Entailment simplification\<close>

text\<open>\<^verbatim>\<open>aentails_simp_core\<close> attempts a single simplification step for a separating entailment.
It is rarely used on its own but as part of more complex tactics repeating, such as
\<^verbatim>\<open>aentails_simp_basic\<close>:\<close>

notepad
begin
  fix \<phi> \<phi>' \<xi> :: \<open>'s::sepalg assert\<close> and P Q R :: \<open>bool\<close>
  assume \<open>ucincl \<phi>\<close>
  from this have \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
    apply aentails_simp_core \<comment>\<open>Floating assumptions and conclusions\<close>
    apply aentails_simp_core \<comment>\<open>Hoisting pure assumptions\<close>
    apply aentails_simp_core \<comment>\<open>Splitting pure conclusions\<close>
    apply aentails_simp_core
    apply aentails_simp_core
    apply aentails_simp_core
    apply aentails_simp_core
    apply aentails_simp_core
    apply aentails_simp_core
    apply aentails_simp_core
    done
next
  fix \<phi> \<phi>' \<xi> :: \<open>'s::sepalg assert\<close> and P Q R :: \<open>bool\<close>
  assume \<open>ucincl \<phi>\<close>
  from this have \<open>\<phi> \<star> \<langle>P\<rangle> \<star> \<phi>' \<star> \<langle>Q\<rangle> \<star> \<langle>R\<rangle> \<longlongrightarrow> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<phi> \<star> \<phi>' \<star> \<langle>R\<rangle>\<close>
    \<comment>\<open>The same again, but now in one step\<close>
    by aentails_simp_basic
end

text\<open>The method \<^verbatim>\<open>aentails_simp_basic\<close> combines entailment simplification with entailment
cancellation, and is already a fairly practical proof tactic when dealing with separating
entailments.

Note that it gives precedence to \<^verbatim>\<open>aentails_simp_core\<close>, which in particular prevents
cancellation of pure assertions, which can be unsafe.\<close>

notepad
begin
  fix \<alpha> \<beta> \<gamma> :: \<open>'s::sepalg assert\<close> and P Q R :: \<open>bool\<close>
  assume \<open>ucincl \<alpha>\<close>
  from this have \<open>P \<Longrightarrow> \<alpha> \<star> \<langle>Q\<rangle> \<star> \<beta> \<star> \<langle>R\<rangle> \<star> \<gamma> \<longlongrightarrow> \<gamma> \<star> \<langle>P\<rangle> \<star> \<langle>Q\<rangle> \<star> \<beta> \<star> \<alpha> \<star> \<langle>R\<rangle>\<close>
    by aentails_simp_basic
next
  \<comment>\<open>Note, however, that classical simplification is not performed:\<close>
  fix \<alpha> \<beta> \<gamma> :: \<open>'s::sepalg assert\<close> and P Q R :: \<open>bool\<close>
  assume \<open>ucincl \<alpha>\<close>
  from this have \<open>P \<Longrightarrow> \<alpha> \<star> \<langle>Q\<rangle> \<star> \<beta> \<star> \<langle>R\<rangle> \<star> \<gamma> \<longlongrightarrow> \<gamma> \<star> \<langle>P \<and> Q\<rangle> \<star> \<beta> \<star> \<alpha> \<star> \<langle>R\<rangle>\<close>
    apply aentails_simp_basic
    apply simp
    apply aentails_simp_basic
    done
end

subsubsection\<open>Spatial \<^verbatim>\<open>rule\<close>\<close>

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>\<tau>\<longlongrightarrow> \<beta> \<star> \<delta>\<close>
  shows \<open>\<rho> \<longlongrightarrow> \<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<tau> \<star> \<rho>\<close>
  \<comment>\<open>This identifies and floats matching spatial goals to the left, but does not 
  yet apply \<^verbatim>\<open>t\<close>\<close>
  apply (tactic \<open>Separation_Logic_Tactics.aentails_float_rule_concls_tac @{thm t} @{context} 1\<close>)
  apply (tactic \<open>Separation_Logic_Tactics.aentails_normalize_assoc_concls_tac @{context} 1\<close>)
  oops

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>A \<Longrightarrow> \<tau> \<longlongrightarrow> \<beta> \<star> \<delta>\<close>
  shows \<open>\<rho> \<longlongrightarrow> \<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<tau> \<star> \<rho>\<close>
  \<comment>\<open>Match and float goals, apply \<^verbatim>\<open>t\<close>, introduce pure and spatial premises, 
  normalize associativity\<close>
  apply (aentails_rule t)
  oops

subsubsection\<open>Conditional spatial \<^verbatim>\<open>rule\<close>\<close>

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>A \<Longrightarrow> \<psi> [\<rho>]\<longlongrightarrow> \<alpha> \<star> \<tau>\<close>
  shows \<open>\<chi> \<star> \<rho> \<longlongrightarrow> \<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<tau> \<star> \<rho>\<close>
  apply (aentails_cond_rule t)
  oops

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>A \<Longrightarrow> \<psi> [\<rho>]\<longlongrightarrow> \<alpha> \<star> \<tau>\<close>
  shows \<open>\<rho> \<longlongrightarrow> \<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<tau> \<star> \<rho>\<close>
  apply (aentails_cond_rule t)
  oops

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>A \<Longrightarrow> \<psi> [\<rho>]\<longlongrightarrow> \<alpha> \<star> \<tau>\<close>
  shows \<open>\<chi> \<star> \<rho> \<longlongrightarrow> \<tau> \<star> \<alpha>\<close>
  apply (aentails_cond_rule t)
  oops

subsubsection\<open>Spatial \<^verbatim>\<open>drule\<close>\<close>

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>\<beta> \<star> \<rho> \<star> \<delta> \<longlongrightarrow> \<epsilon>\<close>
  shows \<open>\<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<tau> \<star> \<rho> \<longlongrightarrow> \<epsilon>\<close>
  \<comment>\<open>This identifies and floats matching assumptions to the left, but does not 
  yet apply \<^verbatim>\<open>t\<close>\<close>
  apply (tactic \<open>Separation_Logic_Tactics.aentails_float_drule_assms_tac @{thm t} @{context} 1\<close>)
  oops

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> \<beta> \<star> \<rho> \<star> \<delta> \<longlongrightarrow> \<epsilon> \<star> \<iota>\<close>
  shows \<open>\<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<tau> \<star> \<rho> \<longlongrightarrow> \<epsilon>\<close>
  \<comment>\<open>Match and float assumptions, apply \<^verbatim>\<open>t\<close>, introduce pure and spatial premises, 
  normalize associativity\<close>
  apply (aentails_drule t)
  oops

subsection\<open>Conditional spatial \<^verbatim>\<open>drule\<close>\<close>

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>\<beta> \<star> \<rho> \<star> \<delta> \<longlongrightarrow>[C] \<tau>\<close>
      and t' : \<open>\<beta> \<star> \<rho> \<star> \<delta> \<longlongrightarrow>[D] \<tau>\<close>
      and t'' : \<open>\<tau> \<star> \<gamma> \<longlongrightarrow>[E] \<rho> \<close>
    shows \<open>\<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<tau> \<star> \<rho> \<longlongrightarrow> \<epsilon> \<star> C \<star> E\<close>
  (* Does not work because conditional D is not present *)
  (* apply (aentails_cond_drule t') *) 
  (* Works because conditional C is present *)
  apply (aentails_cond_drule t)
  apply (aentails_cond_drule t'')
  oops

\<comment>\<open>Should also work with multiple rules at once\<close>

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>\<beta> \<star> \<rho> \<star> \<delta> \<longlongrightarrow>[C] \<tau>\<close>
      and t' : \<open>\<tau> \<star> \<gamma> \<longlongrightarrow>[E] \<rho>\<close>
    shows \<open>\<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<tau> \<star> \<rho> \<longlongrightarrow> \<epsilon> \<star> C \<star> E\<close>
  apply (aentails_cond_drule t t')+
  oops

\<comment>\<open>Should also work with pure premises\<close>

lemma
  fixes \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<tau> \<rho> :: \<open>'s::sepalg assert\<close>
  assumes t : \<open>A \<Longrightarrow> \<beta> \<star> \<rho> \<star> \<delta> \<longlongrightarrow>[C] \<tau>\<close>
    shows \<open>\<alpha> \<star> \<beta> \<star> \<gamma> \<star> \<delta> \<star> \<tau> \<star> \<rho> \<longlongrightarrow> \<epsilon> \<star> C\<close>
  apply (aentails_cond_drule t)
  oops

subsection\<open>Saturating unfolding of definitions\<close>

notepad
begin
  fix \<alpha> \<beta> :: \<open>'t \<Rightarrow> bool\<close> and y
  assume foo: \<open>\<And>x. \<alpha> x \<equiv> \<beta> x\<close>
  have \<open>\<alpha> y \<Longrightarrow> (\<beta> y \<and> \<alpha> y)\<close>
  apply (sat_unfold foo)       \<comment> \<open>Unfold \<^verbatim>\<open>\<alpha>\<close> but remember that it in folded form.\<close>
  apply (intro conjI)
  apply assumption             \<comment> \<open>Use the destructed form\<close>
  apply (assumption_unfolded)  \<comment> \<open>We can still use the folded form!\<close>
  done
end

subsection\<open>Guards\<close>

context
  fixes problematic :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
    and a :: 'a
    and z :: 'b
begin

lemma add_guard_problematic:
  shows \<open>problematic a b \<equiv> (GUARD b problematic) a b\<close>
  by (clarsimp simp add: GUARD_def)

context
  notes add_guard_problematic[add_guards]
begin

lemma
  shows \<open>\<And>foo. \<exists>z. \<forall>a. problematic a z\<close>
  apply update_guards_deep  \<comment>\<open>No guard, because schematic has not yet been introduced\<close>
  apply (intro exI)                
  apply update_guards       \<comment>\<open>No shallow guard, because a binder is blocking\<close>
  apply update_guards_deep  \<comment>\<open>Guard being added, even under binder\<close>
  apply (clarsimp simp add: GUARD_def) \<comment>\<open>Introduce binder, force-remove guard\<close> 
  apply update_guards       \<comment>\<open>Now even the shallow guard applies\<close>
  oops      

ML\<open>
  val t0 = (Free ("problematic", @{typ "'a \<Rightarrow> 'b \<Rightarrow> bool"}))
           $ (Free ("a", @{typ "'a"})) $ (Var (("z", 0), @{typ "'b"}))
  val t3 = (Const (@{const_name GUARD}, @{typ "'b \<Rightarrow> bool \<Rightarrow> bool"}))
           $ (Var (("z", 0), @{typ "'b"})) $ t0
  val ct0 = Thm.cterm_of @{context} t0
  val ct1 = @{cterm \<open>problematic a z\<close>}
  val ct2 = @{cterm \<open>GUARD z (problematic a z)\<close>}
  val ct3 = Thm.cterm_of @{context} t3
  val ct4 = @{cterm \<open>\<exists>z. problematic a z\<close>}
  val ct5 = @{cterm \<open>\<exists>z. GUARD t problematic a z\<close>}

  val thm0  = Crush_Guards.update_guards_shallow_conv @{context} ct0
  val thm0' = Crush_Guards.update_guards_deep_conv [] @{context} ct0

  val thm1  = Crush_Guards.update_guards_shallow_conv @{context} ct1
  val thm1' = Crush_Guards.update_guards_deep_conv [] @{context} ct1

  val thm2  = Crush_Guards.update_guards_shallow_conv @{context} ct2
  val thm2' = Crush_Guards.update_guards_deep_conv [] @{context} ct2

  val thm3  = Crush_Guards.update_guards_shallow_conv @{context} ct3
  val thm3' = Crush_Guards.update_guards_deep_conv [] @{context} ct3

  val thm4  = Crush_Guards.update_guards_shallow_conv @{context} ct4
  val thm4' = Crush_Guards.update_guards_deep_conv [] @{context} ct4

  val thm5  = Crush_Guards.update_guards_shallow_conv @{context} ct5
  val thm5' = Crush_Guards.update_guards_deep_conv [] @{context} ct5
\<close>

end
end

subsubsection\<open>Detecting bad schematic goals\<close>

text\<open>\<^verbatim>\<open>check_bad_schematic_equality_tac'\<close> tries to detect schematic equalities
which are unsolvable due to lack of parametricity in the schematic. Those are
sometimes encountered in \<^verbatim>\<open>crush\<close> when a schematic was introduced prematurely.\<close>

text\<open>Good case: Schematic is sufficiently parametrized.\<close>
schematic_goal \<open>True &&& (\<And>y. y = ?f y)\<close>
  apply (tactic \<open>check_bad_schematic_equality_tac' @{context} true 1\<close>)
  oops

text\<open>Bad case: Schematic is insufficiently parametrized\<close>
schematic_goal \<open>True &&& (\<And>y0 z. y0 = ?f z)\<close>
  \<comment>\<open>Should see warning message\<close>
  apply (tactic \<open>TRY (check_bad_schematic_equality_tac' @{context} true 2)\<close>)
  oops

text\<open>Unknown case: Both sides are schematic. Here, it could be that
\<^verbatim>\<open>?g y0 z\<close> turns out not to depend on \<^verbatim>\<open>y0\<close>, so it would be premature
to issue a warning here.\<close>
schematic_goal \<open>True &&& (\<And>y0 z. t (?g y0 z)  = ?f z)\<close>
  \<comment>\<open>Should see no warning message\<close>
  apply (tactic \<open>check_bad_schematic_equality_tac' @{context} true 2\<close>)
  oops

subsubsection\<open>Filtering relevant premises\<close>

text\<open>Developed for the original version of \<^verbatim>\<open>sledgehammer\<close>, the \<^emph>\<open>Meng-Paulson\<close> (MePo) relevance filter
estimates the likelihood for a fact to be useful in the proof of a goal. In the context of \<^verbatim>\<open>sledgehammer\<close>,
it applies to the facts in the background theory.

In the context of \<^verbatim>\<open>crush\<close>, we adapt the MePo relevance filter to apply to the \<^emph>\<open>premises\<close> of very large
goals instead.

There are two versions of the MePo premise filter: One where the deemed irrelevant premises are
dropped, and another where they are merely marked as 'ignored'. The former is unsafe but leads to
a faster \<^verbatim>\<open>simp\<close> and \<^verbatim>\<open>clarsimp\<close>, while the latter is safe but it appears to bring smaller performance
benefits.\<close>

text\<open>The underlying premise-transformation tactics are \<^verbatim>\<open>thin_tac_idxs\<close> and
\<^verbatim>\<open>ignore_tac_idxs\<close>:\<close>
lemma 
  assumes t: \<open>B \<Longrightarrow> B'\<close>
  shows \<open>A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E\<close>
  \<comment>\<open>Wrap premises \<^verbatim>\<open>A\<close> and \<^verbatim>\<open>C\<close> into \<^verbatim>\<open>IGNORE\<close>, which has a trivial \<^verbatim>\<open>cong\<close> rule and should therefore
  not complicate simplification much.  Premises are identified by their 0-based index.\<close>
  apply (tactic \<open>MePo_Prem.ignore_tac_idxs @{context} [0,2] 1\<close>)
  \<comment>\<open>\<^verbatim>\<open>IGNORE\<close> can be removed via \<^verbatim>\<open>unignore_tac\<close>:\<close>
  apply (tactic \<open>MePo_Prem.unignore_tac @{context} 1\<close>)
  \<comment>\<open>With \<^verbatim>\<open>thin_tac_idxs\<close>, premises are instead dropped altogether:\<close>
  apply (tactic \<open>thin_tac_idxs @{context} [0,2] 1\<close>)
  oops

text\<open>Next, we see how the premise dropping/ignoring tactics are used in the context 
of the MePo premise filter:\<close>

experiment
  fixes f :: \<open>'a \<Rightarrow> 'b\<close>
   and g :: \<open>'b \<Rightarrow> 'b\<close>
   and t0 t1 :: 'a
   and s0 s1 :: 'b
   and x y z :: nat
begin

lemma
  assumes \<open>x < 42\<close>
      and \<open>g (g (f t0)) = s0\<close>
      and \<open>g (f t1) = s1\<close>
      and \<open>x + y < 10*z\<close>
    shows \<open>10*z < 20\<close>
  using assms apply -
  \<comment>\<open>The premise filter correctly identifies the arithmetic premises as the
  most relevant to the goal. The first parameter is the maximum number of premises
  that should be kept. If it is smaller or equal to the current number of premises,
  nothing will happen (and this path is detected early, so it is safe performance-wise
  to call the tactic in this case:\<close>
  apply (tactic \<open>MePo_Prem.ignore_irrelevant_prems_tac @{context} 2 1\<close>)
  \<comment>\<open>Undo the ignore:\<close>
  apply (tactic \<open>MePo_Prem.unignore_tac @{context} 1\<close>)
  \<comment>\<open>There are also method versions of this:\<close>
  apply (mepo_focus 2)
  apply mepo_unfocus
  \<comment>\<open>Next, let's use the drop-version of the premise filter, removing the deemed
  irrelevant premises:\<close>
  apply (tactic \<open>MePo_Prem.drop_irrelevant_prems_tac @{context} 2 1\<close>)
  oops

\<comment>\<open>The MePo filter never drops premises wrapped as \<^verbatim>\<open>ASSUMPTION\<close>:\<close>
lemma 
  assumes \<open>x < 42\<close>
      and \<open>ASSUMPTION (g (g (f t0)) = s0)\<close>
      and \<open>g (f t1) = s1\<close>
      and \<open>x + y < 10*z\<close>
    shows \<open>10*z < 20\<close>
  using assms apply -
  \<comment>\<open>Keeps \<^verbatim>\<open>(g (g (f t0)) = s0)\<close> which would otherwise have been thrown out.\<close>
  apply (tactic \<open>MePo_Prem.ignore_irrelevant_prems_tac @{context} 2 1\<close>)
  oops

end

subsubsection\<open>Conversions\<close>

text\<open>\<^file>\<open>seplog.ML\<close> contains various combinators for building conversions acting on specific
parts of the goal. This section describes some of them.\<close>

text\<open>To apply a conversion to the uRust expression in a weakest precondition goal, use
\<^verbatim>\<open>aentails_wp_conv'\<close>:\<close>

experiment
  fixes e0 e1 e2 :: \<open>('s :: sepalg, 'v, 'r, 'abort, 'i prompt, 'o prompt_output) expression\<close>
  assumes def0: \<open>e0 \<equiv> e1\<close>
  assumes def1: \<open>e1 = e2\<close>
begin
lemma \<open>\<And>x. P x \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> e0 \<phi> \<psi> \<theta>\<close>
  apply (tactic \<open>CONVERSION (Separation_Logic_Tactics.aentails_wp_conv' (Conv.rewr_conv @{thm def0}) @{context}) 1\<close>)
  \<comment>\<open>The above tactic can also be called directly, and also works with HOL equalities\<close>
  apply (tactic \<open>Separation_Logic_Tactics.aentails_wp_rewrite_tac @{thm def1} @{context} 1\<close>)
  oops
end

subsubsection\<open>Helpers\<close>

ML\<open>local
  open Separation_Logic_Tactics
  (* is_entailment detects terms whose meta goal is an entailment *)
  val _ = assert (is_entailment @{term \<open>\<alpha> \<longlongrightarrow> \<beta>\<close>})
  val _ = assert (is_entailment @{term \<open>\<gamma> \<Longrightarrow> \<alpha> \<longlongrightarrow> \<beta>\<close>})
  val _ = assert (is_entailment @{term \<open>\<And>x y z. \<gamma> x \<Longrightarrow> \<alpha> x y \<longlongrightarrow> \<beta> z\<close>})
  (* HOL implications are not stripped *)
  val _ = assert_not (is_entailment @{term \<open>\<gamma> \<longrightarrow> (\<alpha> \<longlongrightarrow> \<beta>)\<close>})
  val _ = assert     (is_entailment @{term \<open>\<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> \<beta> \<phi> \<tau> \<theta>\<close>})

  (* similarly for is_wp_entailment: Strips pure implications only *)
  val _ = assert_not (is_wp_entailment @{term \<open>\<alpha> \<longlongrightarrow> \<beta>\<close>})
  val _ = assert_not (is_wp_entailment @{term \<open>\<gamma> \<Longrightarrow> \<alpha> \<longlongrightarrow> \<beta>\<close>})
  val _ = assert     (is_wp_entailment @{term \<open>\<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> \<beta> \<phi> \<tau> \<theta>\<close>})
  val _ = assert     (is_wp_entailment @{term \<open>\<gamma> \<Longrightarrow> \<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> \<beta> \<phi> \<tau> \<theta>\<close>})
  val _ = assert     (is_wp_entailment @{term \<open>\<And>x y z. \<gamma> x \<Longrightarrow> \<alpha> x y \<longlongrightarrow> \<W>\<P> \<Gamma> \<beta> \<phi> \<tau> \<theta>\<close>})
  (* HOL implications are not stripped *)
  val _ = assert_not (is_wp_entailment @{term \<open>\<gamma> \<longrightarrow> (\<alpha> \<longlongrightarrow> \<beta>)\<close>})
  val _ = assert     (is_wp_entailment @{term \<open>\<alpha> \<longlongrightarrow> \<W>\<P> \<Gamma> \<beta> \<phi> \<tau> \<theta>\<close>})
in end
\<close>

text\<open>To demonstrate \<^verbatim>\<open>is_points_to\<close>, we need to enter the context of the reference locale.\<close>
locale "examples_experiment0" = 
  (* Two named reference interpretations, one unnamed one *)
  refA: reference reference_typesA update_raw_funA dereference_raw_funA
     reference_raw_funA points_to_raw'A gref_can_storeA new_gref_can_storeA 
     can_alloc_referenceA +
  refB: reference reference_typesB update_raw_funB dereference_raw_funB
     reference_raw_funB points_to_raw'B gref_can_storeB new_gref_can_storeB 
     can_alloc_referenceB +
  reference reference_typesC update_raw_funC dereference_raw_funC
     reference_raw_funC points_to_raw'C gref_can_storeC new_gref_can_storeC
     can_alloc_referenceC for
   reference_typesA :: \<open>'s0::sepalg \<Rightarrow> 'a0 \<Rightarrow> 'b0 \<Rightarrow> 'abort \<Rightarrow> 'i0 prompt \<Rightarrow> 'o0 prompt_output \<Rightarrow> unit\<close> and
   reference_typesB :: \<open>'s1::sepalg \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'abort \<Rightarrow> 'i1 prompt \<Rightarrow> 'o1 prompt_output \<Rightarrow> unit\<close> and
   reference_typesC :: \<open>'s2::sepalg \<Rightarrow> 'a2 \<Rightarrow> 'b2 \<Rightarrow> 'abort \<Rightarrow> 'i2 prompt \<Rightarrow> 'o2 prompt_output \<Rightarrow> unit\<close> and
    update_raw_funA dereference_raw_funA reference_raw_funA 
    points_to_raw'A gref_can_storeA new_gref_can_storeA can_alloc_referenceA and
    update_raw_funB dereference_raw_funB reference_raw_funB 
    points_to_raw'B gref_can_storeB new_gref_can_storeB can_alloc_referenceB and
    update_raw_funC dereference_raw_funC reference_raw_funC 
    points_to_raw'C gref_can_storeC new_gref_can_storeC can_alloc_referenceC
begin
ML\<open>local
  open Separation_Logic_Tactics

  (* is_points_to should detect points_to predicates from all interpretations,
     and for the unnamed one, we should also be able to use the usual points_to syntax. *)
  val _ = assert     (is_points_to_raw @{term \<open>(r :: ('a2, 'b2) gref) \<mapsto>\<langle>sh\<rangle> g\<close>})
  val _ = assert_not (is_points_to_raw @{term \<open>(r :: ('a2, 'b2, _) ref) \<mapsto>\<langle>sh\<rangle> g\<down>v\<close>})
  val _ = assert     (is_points_to_raw @{term \<open>refA.points_to_raw r sh g\<close>})
  val _ = assert_not (is_points_to_raw @{term \<open>refA.points_to r sh g v\<close>})
  val _ = assert     (is_points_to_raw @{term \<open>refB.points_to_raw r sh g\<close>})
  val _ = assert_not (is_points_to_raw @{term \<open>refB.points_to r sh g v\<close>})
  val _ = assert     (is_points_to_raw @{term \<open>points_to_raw r sh g\<close>})
  val _ = assert_not (is_points_to_raw @{term \<open>points_to r sh g v\<close>})

  val _ = assert_not (is_points_to @{term \<open>(r :: ('a2, 'b2) gref) \<mapsto>\<langle>sh\<rangle> g\<close>})
  val _ = assert     (is_points_to @{term \<open>(r :: ('a2, 'b2, _) ref) \<mapsto>\<langle>sh\<rangle> g\<down>v\<close>})
  val _ = assert_not (is_points_to @{term \<open>refA.points_to_raw r sh g\<close>})
  val _ = assert     (is_points_to @{term \<open>refA.points_to r sh g v\<close>})
  val _ = assert_not (is_points_to @{term \<open>refB.points_to_raw r sh g\<close>})
  val _ = assert     (is_points_to @{term \<open>refB.points_to r sh g v\<close>})
  val _ = assert_not (is_points_to @{term \<open>points_to_raw r sh g\<close>})
  val _ = assert     (is_points_to @{term \<open>points_to r sh g v\<close>})

  (* This works because all `points_to` variants are actually _abbreviations_ for the
     generic `points_to` *)
  val _ = @{term \<open>refA.points_to_raw r sh g\<close>} |> print_term |> Pretty.str |> Pretty.writeln

  (* Destructing points_to predicates *)
  val (a,b,c,d) = (dest_points_to @{term \<open>r \<mapsto>\<langle>sh\<rangle> g\<down>v\<close>})
  val _ = [a,b,c,d] |> List.map (Syntax.pretty_term @{context}) |> Pretty.chunks |> Pretty.writeln
  val (a,b,c) = (dest_points_to_raw @{term \<open>r \<mapsto>\<langle>sh\<rangle> g\<close>})
  val _ = [a,b,c] |> List.map (Syntax.pretty_term @{context}) |> Pretty.chunks |> Pretty.writeln
in end\<close>
end

subsubsection\<open>Removing premises\<close>

lemma
  fixes a0 a1 a2 a3 a4 a5 a6 b :: bool
  shows \<open>a0 \<Longrightarrow> a1 \<Longrightarrow> a2 \<Longrightarrow> a3 \<Longrightarrow> a4 \<Longrightarrow> a5 \<Longrightarrow> a6 \<Longrightarrow> b\<close>
  apply (tactic\<open>print_premise_tac @{context} 0 1\<close>)
  apply (tactic \<open>thin_tac_idxs @{context} [0, 3, 5] 1\<close>)
  apply (tactic\<open>rotate_tac 3 1\<close>)
  apply (tactic\<open>thin_tac0 @{context} 1\<close>)
  apply (tactic\<open>rotate_tac (~3) 1\<close>)
  oops

subsection\<open>Schematic goals\<close>

\<comment>\<open>\<^verbatim>\<open>refl_schematic\<close> solves a schematic HOL equality:\<close>
schematic_goal \<open>x = ?y\<close>
  apply refl_schematic
  oops

\<comment>\<open>\<^verbatim>\<open>refl_schematic\<close> solves a schematic pure equality:\<close>
schematic_goal \<open>x \<equiv> ?y\<close>
  apply refl_schematic
  oops

\<comment>\<open>\<^verbatim>\<open>refl_schematic\<close> does not solve more complex goals with
schematics, including the following one which \<^verbatim>\<open>simp\<close> would solve.\<close>
schematic_goal \<open>f x = f ?y\<close>
  apply (refl_schematic | log "didn't work")
  apply simp
  oops

\<comment>\<open>\<^verbatim>\<open>refl_schematic\<close> does also not try to solve goals where
the top-level schematic appears non-trivially on the other side.\<close>
schematic_goal \<open>?y = f ?y\<close>
  apply (refl_schematic | log "didn't work")
  oops

\<comment>\<open>\<^verbatim>\<open>refl_schematic\<close> does handle the trivial case of refl, though:\<close>
schematic_goal \<open>?y = ?y\<close>
  apply refl_schematic
  oops

subsubsection\<open>Profiling\<close>

lemma
  shows \<open>(\<forall>x. \<exists>y. R x y) \<longrightarrow> (\<exists>f. \<forall>x. R x (f x))\<close>
  show_timelogs     (* Nothing showing up *)
  apply\<tau>(time auto) (* time <> is meaningful without auto\<tau>, in which case it only prints
                       the measurments to the tracing output. apply\<tau> means that the measurements
                       will be accumulated in the proof context *)
  show_timelogs
  apply\<tau>(time auto)
  apply\<tau>(time auto)
  enable_print_timings
  apply\<tau>(time auto)
  apply\<tau>(time auto)
  apply\<tau>(time "sleep" \<open>sleep 1\<close>)
  show_timelogs     (* See the update time logs *)
  disable_print_timings
  apply\<tau>(time auto)
  apply\<tau>(time auto)
  reset_timelogs  (* Start again *)
  apply\<tau>(tactic \<open>Crush_Time.TIME @{context} true "auto_tac" (auto_tac @{context})\<close>)
  show_timelogs   (* Shouldn't show anything *)
  apply\<tau>(time auto)
  apply\<tau>(time auto)
  apply\<tau>(time auto)
  apply\<tau>(time auto)
  show_timelogs   (* Logs for the last 4 auto calls *)
  (* apply\<tau> unfortunately never fails -- that seems to be necessary so we are allowed
     to update the proof context. It would be useful to at least have markup indicating
     that the inner method failed, but I don't know how to do that yet. *)
  apply\<tau> (time "clssarsimp" \<open>assumption | auto\<close>)
  show_timelogs
  oops

end