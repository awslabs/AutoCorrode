(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Pair_References
  imports Micro_Rust_Interfaces_Core.References Crush.Crush
begin

section\<open>Combining two reference implementations\<close>

text\<open>The goal of this section is to show that two interpretations of the \<^locale>\<open>reference\<close>
locale living on the same separation algebra can be combined to another interpretation
by taking the disjoint union of address and global value types.

Reference allocation is currently inherited from the first interpretation only.\<close>

subsection\<open>Helper constructions and lemmas\<close>

definition Inl_gref :: \<open>('a0, 'b0) gref \<Rightarrow> ('a0 + 'a1, 'b0 + 'b1) gref\<close>
  where \<open>Inl_gref r \<equiv> make_gref (Inl (gref_address r))\<close>

definition Inr_gref :: \<open>('a1, 'b1) gref \<Rightarrow> ('a0 + 'a1, 'b0 + 'b1) gref\<close>
  where \<open>Inr_gref r \<equiv> make_gref (Inr (gref_address r))\<close>

definition plus_gref :: \<open>('a0 + 'a1, 'b0 + 'b1) gref \<Rightarrow> ('a0, 'b0) gref + ('a1,'b1) gref\<close> 
  where \<open>plus_gref r \<equiv>
    case gref_address r of
       Inl r0 \<Rightarrow> Inl (make_gref r0)
     | Inr r1 \<Rightarrow> Inr (make_gref r1)\<close>

lemma Inl_Inr_plus_gref:
  shows \<open>plus_gref (Inl_gref r) = Inl r\<close>
    and \<open>plus_gref (Inr_gref r) = Inr r\<close>
  by (auto simp add: Inl_gref_def Inr_gref_def plus_gref_def)

lemma Inl_Inr_image_in:
  shows \<open>Inl x \<in> Inl ` A \<longleftrightarrow> x \<in> A\<close> 
    and \<open>Inr y \<in> Inr ` B \<longleftrightarrow> y \<in> B\<close>
    and \<open>Inl x \<in> Inr ` B \<longleftrightarrow> False\<close>
    and \<open>Inr y \<in> Inl ` A \<longleftrightarrow> False\<close>
  by blast+

subsection\<open>Pairing context\<close>

text\<open>The following locale captures the context of two interpretations of the
\<^locale>\<open>reference\<close> locale living on the same separation algebra.

In practice, it is more likely that interpretations will live on separate separation algebras
initially, but in that case they can both be lifted to the product separation algebra first,
by means of reference transfer.\<close>

locale Reference_Pair = refA: reference reference_typesA update_raw_funA dereference_raw_funA
     reference_raw_funA points_to_raw'A gref_can_storeA new_gref_can_storeA 
     can_alloc_referenceA +
  refB: reference reference_typesB update_raw_funB dereference_raw_funB
     reference_raw_funB points_to_raw'B gref_can_storeB new_gref_can_storeB 
     can_alloc_referenceB for
   reference_typesA :: \<open>'s::sepalg \<Rightarrow> 'a0 \<Rightarrow> 'b0 \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> and
   reference_typesB :: \<open>'s::sepalg \<Rightarrow> 'a1 \<Rightarrow> 'b1 \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close> and
    update_raw_funA dereference_raw_funA reference_raw_funA 
    points_to_raw'A gref_can_storeA new_gref_can_storeA can_alloc_referenceA and
    update_raw_funB dereference_raw_funB reference_raw_funB 
    points_to_raw'B gref_can_storeB new_gref_can_storeB can_alloc_referenceB 
begin

text\<open>We now define the reference interface for the combined interpretation. 

The new address type is \<^verbatim>\<open>'a0 + 'a1\<close> -- that is, the disjoint union of the address types
of the input interpretations. Similarly, the global value type is the disjoint union
\<^verbatim>\<open>'b0 + 'b1\<close> of the global value types of the individual interpretations.\<close>

definition update_raw_fun :: 
  \<open>('a0 + 'a1, 'b0 + 'b1) gref \<Rightarrow> 'b0 + 'b1 \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>update_raw_fun r b \<equiv> 
      case (plus_gref r, b) of 
         (Inl r0, Inl b0) \<Rightarrow> update_raw_funA r0 b0
       | (Inr r1, Inr b1) \<Rightarrow> update_raw_funB r1 b1
       | _ \<Rightarrow> FunctionBody \<lbrakk> panic!("Invalid update on pair reference") \<rbrakk>\<close>

definition dereference_raw_fun :: 
  \<open>('a0 + 'a1, 'b0 + 'b1) gref \<Rightarrow> ('s, 'b0 + 'b1, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>dereference_raw_fun r \<equiv> 
      case plus_gref r of 
         Inl r0 \<Rightarrow> FunctionBody \<lbrakk> \<llangle>Inl\<rrangle>\<^sub>1 (dereference_raw_funA (r0)) \<rbrakk>
       | Inr r1 \<Rightarrow> FunctionBody \<lbrakk> \<llangle>Inr\<rrangle>\<^sub>1 (dereference_raw_funB (r1)) \<rbrakk>\<close>

text\<open>Allocations are currently only possible with \<^emph>\<open>one\<close> of the two allocators.
The axioms need suitable generalization if we ever need to combine two reference
interpretations which can both allocate.\<close>
definition reference_raw_fun :: 
  \<open>'b0 + 'b1 \<Rightarrow> ('s, ('a0 + 'a1, 'b0 + 'b1) gref, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>reference_raw_fun b \<equiv> FunctionBody \<lbrakk>
     match b {
       Inl(b0) \<Rightarrow> \<llangle>Inl_gref\<rrangle>\<^sub>1 (reference_raw_funA (b0)),
       Inr(b1) \<Rightarrow> panic!("Invalid allocation") 
     }
  \<rbrakk>\<close>

definition points_to_raw' :: \<open>('a0 + 'a1, 'b0 + 'b1) gref \<Rightarrow> share \<Rightarrow> 'b0 + 'b1 \<Rightarrow> 's set\<close>
  where \<open>points_to_raw' r sh b \<equiv>
     case (plus_gref r, b) of 
         (Inl r0, Inl b0) \<Rightarrow> points_to_raw'A r0 sh b0
       | (Inr r1, Inr b1) \<Rightarrow> points_to_raw'B r1 sh b1
       | _ \<Rightarrow> {}\<close>

definition can_alloc_reference :: \<open>'s set\<close>
  where \<open>can_alloc_reference \<equiv> can_alloc_referenceA\<close>
\<comment>\<open>The \<^verbatim>\<open>reference\<close> locale requires allocator availability to be upwards
closed; the registered fact discharges that interpretation obligation below.\<close>
ucincl_auto can_alloc_reference

definition gref_can_store :: \<open>('a0 + 'a1, 'b0 + 'b1) gref \<Rightarrow> ('b0 + 'b1) set\<close> where
  \<open>gref_can_store r \<equiv>
      case plus_gref r of
         Inl r0 \<Rightarrow> Inl ` (gref_can_storeA r0)
       | Inr r1 \<Rightarrow> Inr ` (gref_can_storeB r1)\<close>

definition new_gref_can_store :: \<open>('b0 + 'b1) set\<close> where
  \<open>new_gref_can_store \<equiv> Inl ` new_gref_can_storeA\<close>

lemma function_contract_empty:
  shows \<open>\<Gamma> ; f \<Turnstile>\<^sub>F make_function_contract {} \<tau>\<close>
  by (intro satisfies_function_contractI; clarsimp simp add: bot_aentails_all wp_to_sstriple)

lemma update_raw_fun_spec:
  \<open>\<Gamma> ; update_raw_fun r g \<Turnstile>\<^sub>F
          reference_defs.update_raw_contract points_to_raw' gref_can_store r g0 g\<close>
  using refA.update_raw_spec refB.update_raw_spec
  by (cases \<open>plus_gref r\<close>; cases g; cases g0; clarsimp simp add: update_raw_fun_def
    points_to_raw'_def gref_can_store_def reference_defs.update_raw_contract_def
    reference_defs.points_to_raw_def Inl_Inr_image_in
    asepconj_simp intro!: function_contract_empty)

lemma dereference_raw_fun_spec:
  \<open>\<Gamma> ; dereference_raw_fun r \<Turnstile>\<^sub>F reference_defs.dereference_raw_contract points_to_raw' r sh g\<close>
  apply (crush_boot f: dereference_raw_fun_def contract:
    reference_defs.dereference_raw_contract_def)
  apply (cases \<open>plus_gref r\<close>; cases g; fastcrush_base
    simp add: reference_defs.points_to_raw_def points_to_raw'_def
    specs add: refA.dereference_raw_spec refB.dereference_raw_spec
    contracts add: refA.dereference_raw_contract_def refB.dereference_raw_contract_def)
  done

lemma reference_raw_fun_spec:
  \<open>\<Gamma> ; reference_raw_fun
                g \<Turnstile>\<^sub>F reference_defs.reference_raw_contract points_to_raw' gref_can_store
                        new_gref_can_store can_alloc_reference g\<close>
  apply (crush_boot f: reference_raw_fun_def contract:
    reference_defs.reference_raw_contract_def)
  apply (cases g; crush_base
    simp add: new_gref_can_store_def can_alloc_reference_def gref_can_store_def Inl_Inr_plus_gref
      reference_defs.points_to_raw_def points_to_raw'_def  gref_can_store_def Inl_Inr_image_in
    specs add: refA.reference_raw_spec
    contracts add: refA.reference_raw_contract_def) 
  apply blast
  done

lemma points_to_combine:
  shows \<open>reference_defs.points_to_raw points_to_raw' r sh1 v1 \<star>
       reference_defs.points_to_raw points_to_raw' r sh2 v2 \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r (sh1 + sh2) v1 \<star> \<langle>v1 = v2\<rangle>\<close>
  using refA.points_to_raw_combine refA.points_to_raw_def 
  using refB.points_to_raw_combine refB.points_to_raw_def 
  by (cases \<open>plus_gref r\<close>; cases v1; cases v2; 
    clarsimp simp add: reference_defs.points_to_raw_def points_to_raw'_def asepconj_simp
      aentails_simp bot_aentails_all) 

lemma points_to_split:
  shows \<open>sh = shA + shB \<Longrightarrow>
       shA \<sharp> shB \<Longrightarrow>
       0 < shA \<Longrightarrow>
       0 < shB \<Longrightarrow>
       reference_defs.points_to_raw points_to_raw' r sh v \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r shA v \<star>
       reference_defs.points_to_raw points_to_raw' r shB v\<close>
  using refA.points_to_raw_split refA.points_to_raw_def 
  using refB.points_to_raw_split refB.points_to_raw_def 
  by (cases \<open>plus_gref r\<close>; cases v; 
    clarsimp simp add: reference_defs.points_to_raw_def points_to_raw'_def asepconj_simp
      aentails_simp bot_aentails_all) 

lemma pair_reference_sublocale: \<open>reference update_raw_fun dereference_raw_fun 
  reference_raw_fun points_to_raw' gref_can_store new_gref_can_store can_alloc_reference\<close>
proof standard
  show \<open>\<And>\<Gamma> r g g0.
       \<Gamma> ; update_raw_fun r
             g \<Turnstile>\<^sub>F reference_defs.update_raw_contract points_to_raw' gref_can_store r g0 g\<close>
    by (rule update_raw_fun_spec)
next
  show \<open>\<And>\<Gamma> r sh g.
       \<Gamma> ; dereference_raw_fun r \<Turnstile>\<^sub>F reference_defs.dereference_raw_contract points_to_raw' r sh g\<close>
    by (rule dereference_raw_fun_spec)
next
  show \<open>\<And>\<Gamma> g. \<Gamma> ; reference_raw_fun
                g \<Turnstile>\<^sub>F reference_defs.reference_raw_contract points_to_raw' gref_can_store
                        new_gref_can_store can_alloc_reference g\<close>
    by (rule reference_raw_fun_spec)
next
  show \<open>ucincl can_alloc_reference\<close>
    by ucincl_solve
next
  show \<open>\<And>r sh1 sh2 v1 v2.
       reference_defs.points_to_raw points_to_raw' r sh1 v1 \<star>
       reference_defs.points_to_raw points_to_raw' r sh2 v2 \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r (sh1 + sh2) v1 \<star> \<langle>v1 = v2\<rangle>\<close>
    by (rule points_to_combine)
next
  show \<open>\<And>sh shA shB r v.
       sh = shA + shB \<Longrightarrow>
       shA \<sharp> shB \<Longrightarrow>
       0 < shA \<Longrightarrow>
       0 < shB \<Longrightarrow>
       reference_defs.points_to_raw points_to_raw' r sh v \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r shA v \<star>
       reference_defs.points_to_raw points_to_raw' r shB v\<close>
    by (rule points_to_split)
qed

end

end