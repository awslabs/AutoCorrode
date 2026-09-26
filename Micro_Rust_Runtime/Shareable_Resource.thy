(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Shareable_Resource
imports
  Separation_Lenses.SLens_Examples
  Separation_Lenses.SLens_Pullback
  Micro_Rust_Interfaces.Read_Write_Resource
  Shallow_Separation_Logic.Shareable_Value
begin

section\<open>Reading/Writing shareable values\<close>

text\<open>A \<^verbatim>\<open>shareable_value\<close> is an abstraction of a resource that can be read and written. We first
define read/write functions on \<^verbatim>\<open>shareable_value\<close> itself and prove its spec. Then, we lift them along
separation lenses to read/write functions on larger separation algebras. We then use the result to
instantiate an abstract interface to read-writable resources.\<close>

definition read_shareable_value_core :: \<open>('v shareable_value, 'v, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>read_shareable_value_core \<equiv> Expression (\<lambda>r.
     case r of
        No_Value \<Rightarrow> Abort DanglingPointer r
      | Shared_Value _ val \<Rightarrow> Success val r
  )\<close>

definition shareable_value_is :: \<open>share \<Rightarrow> 'v \<Rightarrow> 'v shareable_value assert\<close> where
  \<open>shareable_value_is sh v \<equiv> apure (0 < sh) \<star> \<up>\<^sub>s (Shared_Value (Abs_nonempty_share sh) v)\<close>

lemma ucincl_shareable_value_is [simp, ucincl_intros]: \<open>ucincl (shareable_value_is sh v)\<close>
  unfolding shareable_value_is_def by (simp add: uc_state_ucincl ucincl_intros)

lemma shareable_value_is_alt:
  \<open>\<sigma> \<in> shareable_value_is sh v \<longleftrightarrow> 0 < sh \<and> \<sigma> \<in> \<up>\<^sub>s (Shared_Value (Abs_nonempty_share sh) v)\<close>
  by (simp add: shareable_value_is_def uc_state_ucincl asepconj_pure', simp add: apure_def)

lemma shareable_value_is_top_alt:
  shows \<open>shareable_value_is \<top> v = {Shared_Value \<top> v}\<close>
  by (safe; simp add: shareable_value_is_alt)
    (auto simp add: shareable_value_is_def asat_def shareable_value_uc_state_top zero_share_def
       simp flip: top_nonempty_share.abs_eq)

lemma ucincl_shared_value_top[simp, ucincl_intros]:
  shows \<open>ucincl {Shared_Value \<top> v}\<close>
  by (simp flip: shareable_value_is_top_alt add: ucincl_intros)

lemma asepconj_float_pure:
  shows \<open>\<alpha> \<star> apure P = apure P \<star> \<alpha>\<close>
    and \<open>\<alpha> \<star> apure P \<star> \<beta> = apure P \<star> \<alpha> \<star> \<beta>\<close>
  by (simp add: asepconj_comm asepconj_swap_top asepconj_pure)+

lemma shareable_value_split:
  assumes \<open>sh0 \<sharp> sh1\<close>
      and \<open>0 < sh0\<close> and \<open>0 < sh1\<close>
    shows \<open>shareable_value_is (sh0 + sh1) v \<longlongrightarrow> shareable_value_is sh0 v \<star> shareable_value_is sh1 v\<close>
proof -
  from assms have \<open>0 < sh0 + sh1\<close>
    by (simp add: less_supI2 plus_share_def)
  from this show ?thesis
  using assms by (simp add: shareable_value_is_def asepconj_ident uc_state_ucincl asepconj_simp
    Abs_nonempty_share_inverse aentails_def eq_onp_same_args plus_nonempty_share.abs_eq plus_share_def
    shareable_value_uc_state_asepconj zero_share_def)
qed

lemma shareable_value_combine:
  shows \<open>shareable_value_is sh0 v0 \<star> shareable_value_is sh1 v1
             \<longlongrightarrow> \<langle>v0 = v1\<rangle> \<star> \<langle>sh0 \<sharp> sh1\<rangle> \<star>
               shareable_value_is (sh0 + sh1) v0\<close>
proof (intro apure_precise_entailsR)
  assume "is_sat (shareable_value_is sh0 v0 \<star> shareable_value_is sh1 v1)"
  then show "v0 = v1"
    unfolding shareable_value_is_def
    by (metis (no_types, opaque_lifting) asepconj_bot_zero2 asepconj_comm asepconj_float_pure(2) 
        non_is_sat_empty shareable_value_uc_state_asepconj_general)
next
  assume \<section>: "is_sat (shareable_value_is sh0 v0 \<star> shareable_value_is sh1 v1)"
  then obtain "is_sat (apure (0 < sh1))" "is_sat (apure (0 < sh0))"
    by (metis is_sat_pure is_sat_splitE shareable_value_is_def)
  with \<section> show "sh0 \<sharp> sh1"
    apply (simp add: shareable_value_is_def asepconj_float_pure)
    by (simp add: asepconj_simp asepconj_uc_state_general Abs_nonempty_share_inverse zero_share_def split: if_splits)
next
  show "shareable_value_is sh0 v0 \<star> shareable_value_is sh1 v1 \<longlongrightarrow> shareable_value_is (sh0 + sh1) v0"
    apply (simp add: shareable_value_is_def asepconj_float_pure)
    apply (intro apure_entailsL assocL_entails apure_entailsR apure_entailsR0)
     apply (simp_all add: ucincl_intros uc_state_ucincl plus_share_def less_supI2)
    by (simp add: aentails_def eq_onp_same_args plus_nonempty_share.abs_eq shareable_value_uc_state_asepconj_general zero_share_def)
qed 

lemma eval_read_shareable_value_core:
  shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>y,read_shareable_value_core\<rangle> (a, \<sigma>') \<longleftrightarrow> (\<sigma> = No_Value \<and> a = DanglingPointer \<and> \<sigma> = \<sigma>')\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>y,read_shareable_value_core\<rangle> (v, \<sigma>') \<longleftrightarrow> (\<sigma>' = \<sigma> \<and> (case \<sigma> of No_Value \<Rightarrow> False | Shared_Value sh v' \<Rightarrow> v = v'))\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>y,read_shareable_value_core\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
  by (auto simp add: read_shareable_value_core_def evaluates_to_abort_def evaluates_to_value_def
    evaluates_to_return_def deep_evaluates_nondet_basic.simps evaluate_def split!: shareable_value.splits)

corollary eval_value_read_shareable_value_core_local:
  shows \<open>is_local (eval_value y read_shareable_value_core) (shareable_value_is sh v)\<close>
  by (intro is_localI; case_tac \<sigma>_0; case_tac \<sigma>_1;
    auto simp add: shareable_value_is_alt eval_return_def asat_def uc_state_def
      eval_read_shareable_value_core shareable_value_upwards_closure_core eval_value_def)

corollary eval_return_read_shareable_value_core_local:
  shows \<open>is_local (eval_return y read_shareable_value_core) (shareable_value_is sh v)\<close>
  by (intro is_localI; simp add: eval_return_def eval_read_shareable_value_core)

corollary eval_abort_read_shareable_value_core_local:
  shows \<open>is_local (eval_abort y read_shareable_value_core) (shareable_value_is sh v)\<close>
  apply (intro is_localI; simp add: eval_abort_def eval_read_shareable_value_core)
  apply fastforce
  apply (simp add: asat_def shareable_value_is_alt shareable_value_upwards_closure_core(3) uc_state_def)
  done

lemmas eval_read_shareable_value_core_local = 
  eval_value_read_shareable_value_core_local
  eval_return_read_shareable_value_core_local
  eval_abort_read_shareable_value_core_local

definition read_shareable_value :: \<open>('v shareable_value, 'v, 'abort, 'i, 'o) function_body\<close> where
  \<open>read_shareable_value \<equiv> FunctionBody read_shareable_value_core\<close>

definition read_shareable_value_contract :: \<open>'v \<Rightarrow> share \<Rightarrow> ('v shareable_value, 'v, 'abort) function_contract\<close>
  where \<open>read_shareable_value_contract \<equiv> \<lambda>v sh.
     let pre = shareable_value_is sh v in
     let post = \<lambda>r. shareable_value_is sh v \<star> \<langle>r = v\<rangle> in
     make_function_contract pre post\<close>

lemma read_shareable_value_contract_no_abort:
  shows \<open>function_contract_abort (read_shareable_value_contract a b) = \<bottom>\<close>
  by (simp add: read_shareable_value_contract_def)

lemma read_shareable_value_spec:
  shows \<open>\<Gamma>; read_shareable_value \<Turnstile>\<^sub>F read_shareable_value_contract v sh\<close>
  apply (intro satisfies_function_contractI;
    clarsimp intro!: ucincl_intros simp add: read_shareable_value_contract_def)
  apply (intro sstripleI; clarsimp simp add: read_shareable_value_def atriple_rel_def
    asat_apure_precise_distrib2 ucincl_intros asepconj_simp eval_read_shareable_value_core_local; safe?)
  apply (auto simp add: eval_read_shareable_value_core shareable_value_is_alt
    eval_return_def eval_abort_def eval_value_def shareable_value_uc_state asat_def)
  done

definition write_shareable_value_core :: \<open>'v \<Rightarrow> ('v shareable_value, unit, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>write_shareable_value_core val \<equiv> Expression (\<lambda>r.
     case r of
        Shared_Value sh _ \<Rightarrow> if sh = \<top> then Success () (Shared_Value \<top> val) else Abort DanglingPointer r
      | _ \<Rightarrow> Abort DanglingPointer r
  )\<close>

definition shareable_value_is_writable :: \<open>'v shareable_value assert\<close> where
  \<open>shareable_value_is_writable \<equiv> { \<sigma>. case \<sigma> of No_Value \<Rightarrow> False | Shared_Value sh _ \<Rightarrow> sh = top }\<close>

lemma shareable_value_is_writableE:
  assumes \<open>\<sigma> \<Turnstile> shareable_value_is_writable\<close>
  and \<open>\<And>v. \<sigma> = Shared_Value \<top> v \<Longrightarrow> R\<close>
  shows R
  using assms by (auto simp add: asat_def shareable_value_is_writable_def split!: shareable_value.splits)

lemma shareable_value_is_writable_alt:
  shows \<open>(\<Squnion>v0. shareable_value_is \<top> v0) = shareable_value_is_writable\<close>
  by (intro asat_semequivI; 
      simp add: asat_def shareable_value_is_writable_def shareable_value_is_top_alt split!: shareable_value.splits)

lemma shareable_value_is_writable_ucincl[simp, ucincl_intros]:
  shows \<open>ucincl shareable_value_is_writable\<close>
  by (clarsimp intro!: ucincl_intros simp flip: shareable_value_is_writable_alt)

lemma shareable_value_is_writable_basic [simp]:
  shows \<open>Shared_Value \<top> v \<Turnstile> shareable_value_is_writable\<close>
  by (simp add: asat_def shareable_value_is_writable_def)

lemma eval_write_shareable_value_core:
  shows \<open>\<sigma> \<leadsto>\<^sub>a \<langle>y,write_shareable_value_core val\<rangle> (a, \<sigma>') \<longleftrightarrow> ( \<not>(\<sigma> \<Turnstile> shareable_value_is_writable) \<and> a = DanglingPointer \<and> \<sigma> = \<sigma>')\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>v \<langle>y,write_shareable_value_core val\<rangle> (v, \<sigma>') \<longleftrightarrow> (\<sigma> \<Turnstile> shareable_value_is_writable \<and> \<sigma>' = Shared_Value top val)\<close>
    and \<open>\<sigma> \<leadsto>\<^sub>r \<langle>y,write_shareable_value_core val\<rangle> (r, \<sigma>') \<longleftrightarrow> False\<close>
  by (auto simp add: write_shareable_value_core_def evaluates_to_abort_def evaluates_to_value_def
    asat_def shareable_value_is_writable_def evaluates_to_return_def deep_evaluates_nondet_basic.simps evaluate_def
    split!: shareable_value.splits if_splits)

corollary eval_value_write_shareable_value_core_local:
  shows \<open>is_local (eval_value y (write_shareable_value_core val)) shareable_value_is_writable\<close>
  by (intro is_localI) (auto simp: shareable_value_disjoint_top elim!: shareable_value_is_writableE)

corollary eval_return_write_shareable_value_core_local:
  shows \<open>is_local (eval_return y (write_shareable_value_core val)) shareable_value_is_writable\<close>
  by (intro is_localI; simp add: eval_return_def eval_write_shareable_value_core)

corollary eval_abort_write_shareable_value_core_local:
  shows \<open>is_local (eval_abort y (write_shareable_value_core val)) shareable_value_is_writable\<close>
  by (intro is_localI) (auto simp: shareable_value_disjoint_top elim!: shareable_value_is_writableE)

lemmas eval_write_shareable_value_core_local =
  eval_value_write_shareable_value_core_local
  eval_return_write_shareable_value_core_local
  eval_abort_write_shareable_value_core_local

definition write_shareable_value :: \<open>'v \<Rightarrow> ('v shareable_value, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>write_shareable_value val \<equiv> FunctionBody (write_shareable_value_core val)\<close>

definition write_shareable_value_contract :: \<open>'v \<Rightarrow> ('v shareable_value, unit, 'abort) function_contract\<close>
  where \<open>write_shareable_value_contract \<equiv> \<lambda>v.
     let pre = \<Squnion>v0. shareable_value_is \<top> v0 in
     let post = \<lambda>r. shareable_value_is \<top> v in
     make_function_contract pre post\<close>

lemma write_shareable_value_contract_no_abort:
  shows \<open>function_contract_abort (write_shareable_value_contract a) = \<bottom>\<close>
  by (simp add: write_shareable_value_contract_def)

lemma write_shareable_value_spec:
  shows \<open>\<Gamma>; write_shareable_value v \<Turnstile>\<^sub>F write_shareable_value_contract v\<close>
proof -
  have \<open>\<Gamma> ; shareable_value_is_writable \<turnstile>
    function_body (write_shareable_value v) \<stileturn>
    (\<lambda>r. shareable_value_is \<top> v) \<bowtie>
    (\<lambda>r. shareable_value_is \<top> v) \<bowtie> \<bottom>\<close>
    apply (intro sstripleI)
      apply (auto simp add: eval_write_shareable_value_core shareable_value_is_top_alt eval_value_def eval_return_def eval_abort_def
        write_shareable_value_def asepconj_simp atriple_rel_def shareable_value_disjoint_top
        is_local_def elim!: shareable_value_is_writableE)
    done
  then show ?thesis
    by (intro satisfies_function_contractI) (auto simp add: shareable_value_is_writable_alt write_shareable_value_contract_def)
qed

text\<open>In any interesting application, the underlying separation algebra will not be equal to
\<^verbatim>\<open>shareable_value\<close>, but contain it via a separation lens. In this case, we can use the pullback
mechanism to obtain read/write functions on the larger separation algebra:\<close>

type_synonym ('s, 'v) shareable_resource = \<open>('s, 'v shareable_value) lens\<close>

definition resource_is :: \<open>('s::zero, 'v) shareable_resource \<Rightarrow> share \<Rightarrow> 'v \<Rightarrow> 's assert\<close>
  where \<open>resource_is l sh v \<equiv> l\<inverse> (shareable_value_is sh v)\<close>

definition read_resource :: \<open>('s, 'v) shareable_resource \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close>
  where \<open>read_resource l \<equiv> l\<inverse> read_shareable_value\<close>

definition write_resource :: \<open>('s, 'v) shareable_resource\<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
  where \<open>write_resource l v \<equiv> l\<inverse> (write_shareable_value v)\<close>

definition read_resource_contract :: \<open>('s::sepalg, 'v) shareable_resource \<Rightarrow> 'v \<Rightarrow> share \<Rightarrow> ('s, 'v, 'abort) function_contract\<close>
  where \<open>read_resource_contract l v sh \<equiv>
    l\<inverse> (read_shareable_value_contract v sh)\<close>

lemma read_resource_contract_no_abort:
  shows \<open>function_contract_abort (read_resource_contract a b c) = \<bottom>\<close>
  by (simp add: read_shareable_value_contract_no_abort read_resource_contract_def
    pull_back_contract_def pull_back_assertion_def bot_fun_def)

definition write_resource_contract :: \<open>('s::sepalg, 'v) shareable_resource \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort) function_contract\<close>
  where \<open>write_resource_contract l v \<equiv>
    l\<inverse> (write_shareable_value_contract v)\<close>

lemma write_resource_contract_no_abort:
  shows \<open>function_contract_abort (write_resource_contract a b) = \<bottom>\<close>
  by (simp add: write_shareable_value_contract_no_abort write_resource_contract_def
    pull_back_contract_def pull_back_assertion_def bot_fun_def)

lemma resource_is_split:
  assumes \<open>is_valid_slens r\<close>
      and \<open>sh0 \<sharp> sh1\<close>
      and \<open>0 < sh0\<close> and \<open>0 < sh1\<close>
  shows \<open>resource_is r (sh0 + sh1) v \<longlongrightarrow> resource_is r sh0 v \<star> resource_is r sh1 v\<close>
proof -
  from assms(2-4) have source:
    \<open>shareable_value_is (sh0 + sh1) v \<longlongrightarrow>
      shareable_value_is sh0 v \<star> shareable_value_is sh1 v\<close>
    by (rule shareable_value_split)
  from assms(1) source have
    \<open>r\<inverse> (shareable_value_is (sh0 + sh1) v) \<longlongrightarrow>
      r\<inverse> (shareable_value_is sh0 v \<star> shareable_value_is sh1 v)\<close>
    by (rule slens.pull_back_aentailsI[simplified])
  with assms(1) show ?thesis
    by (simp add: resource_is_def slens.pull_back_asepconj[simplified])
qed

lemma resource_is_merge:
  assumes \<open>is_valid_slens r\<close>
  shows \<open>resource_is r sh0 v0 \<star> resource_is r sh1 v1 \<longlongrightarrow>
    \<langle>sh0 \<sharp> sh1\<rangle> \<star> \<langle>v0 = v1\<rangle> \<star>
      resource_is r (sh0 + sh1) v0\<close>
proof -
  from assms shareable_value_combine have pulled:
    \<open>r\<inverse> (shareable_value_is sh0 v0 \<star> shareable_value_is sh1 v1) \<longlongrightarrow>
      r\<inverse> (\<langle>v0 = v1\<rangle> \<star> \<langle>sh0 \<sharp> sh1\<rangle> \<star>
        shareable_value_is (sh0 + sh1) v0)\<close>
    by (rule slens.pull_back_aentailsI[simplified])
  from pulled assms show ?thesis
    by (simp add: resource_is_def slens.pull_back_asepconj[simplified]
      slens.pull_back_assertion_apure_precise[simplified] asepconj_swap_top)
qed

lemma read_resource_spec:
  assumes \<open>is_valid_slens l\<close>
  shows \<open>\<Gamma>; read_resource l \<Turnstile>\<^sub>F read_resource_contract l v sh\<close>
  by (simp add: assms slens.pull_back_spec_universal_precise read_resource_contract_def read_resource_def
    read_shareable_value_spec read_shareable_value_contract_no_abort)

lemma write_resource_spec:
  assumes \<open>is_valid_slens l\<close>
  shows \<open>\<Gamma>; write_resource l v \<Turnstile>\<^sub>F write_resource_contract l v\<close>
  by (simp add: assms slens.pull_back_spec_universal_precise write_resource_contract_def write_resource_def
    write_shareable_value_spec write_shareable_value_contract_no_abort)

lemma resource_is_eval_lens_alt:
  shows \<open>\<sigma> \<Turnstile> resource_is (share_map_eval_lens k) sh v
    \<longleftrightarrow> 0 < sh \<and> Shared_Value (Abs_nonempty_share sh) v \<preceq> rbt_share_map_\<alpha> \<sigma> k
      \<and> \<sigma> = lens_update (share_map_eval_lens k) (rbt_share_map_\<alpha> \<sigma> k) 0\<close>
  by (auto simp add: share_map_eval_lens_def resource_is_def pull_back_assertion_def
    asat_def shareable_value_is_alt uc_state_def)

lemma rbt_share_map_decompose_resource:
  fixes m :: \<open>('k::linorder, 'v) rbt_share_map\<close>
  shows \<open>m \<Turnstile> \<star>\<star>{# resource_is (share_map_eval_lens k) (Rep_nonempty_share sh) v .
                  (k, v, sh) \<leftarrow> rbt_share_map_mset m #}\<close>
  using Rep_nonempty_share by (auto intro!: rbt_share_map_decompose_generic
    simp add: resource_is_eval_lens_alt zero_share_def Rep_nonempty_share_inverse
      rbt_share_map_singleton_def) (simp add: share_map_eval_lens_def)


subsection\<open>Construction RW resources from \<^verbatim>\<open>shareable_value\<close>\<close>

text\<open>In this section, we show that any separation lens to a \<^verbatim>\<open>shareable_value\<close> gives rise to an
interpretation of the above interface.\<close>

text\<open>This is a bit of an odd thing. We don't want the code generator to try to produce code corresponding
to the above set definition, which really only exists for purely logical purposes. So, we tell the
code generator to replace it with an error instead. Note that \<^verbatim>\<open>resource_is\<close> has other arguments
beyond \<^verbatim>\<open>l\<close> on the LHS of its defining equation, so won't be invoked.\<close>
declare [[code abort: resource_is]]

definition rw_resource_from_slens :: \<open>('s::zero, 'v) shareable_resource \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) rw_resource\<close> where
  \<open>rw_resource_from_slens l \<equiv> make_rw_resource (resource_is l) (read_resource l) (write_resource l)\<close>

lemma rw_resource_from_slens_contracts:
  assumes valid: \<open>is_valid_slens l\<close>
  shows \<open>generic_read_contract (rw_resource_is (rw_resource_from_slens l))
          = read_resource_contract l\<close>
    and \<open>generic_write_contract (rw_resource_is (rw_resource_from_slens l))
          = write_resource_contract l\<close>
  using valid by (auto intro!: ext simp add: generic_write_contract_def
    generic_read_contract_def rw_resource_is_def rw_resource_from_slens_def
    resource_is_def read_resource_contract_def read_shareable_value_contract_def
    write_resource_contract_def write_shareable_value_contract_def
    pull_back_contract_def
    slens.pull_back_asepconj[simplified]
    slens.pull_back_assertion_apure_precise[simplified]
    slens.pull_back_assertion_false[simplified]
    slens.pull_back_assert_Union[simplified])

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma read_resource_contract_concrete:
  assumes valid: \<open>is_valid_slens l\<close>
  shows \<open>generic_read_contract (rw_resource_is (rw_resource_from_slens l))
          = read_resource_contract l\<close>
  using assms rw_resource_from_slens_contracts by meson

lemma rw_resource_valid:
  assumes \<open>is_valid_slens l\<close>
  shows \<open>standard_rw_resource (rw_resource_from_slens l)\<close>
proof (intro standard_rw_resourceI)
  fix sh0 sh1 :: share and v0 v1
  from assms show
    \<open>rw_resource_is (rw_resource_from_slens l) sh0 v0
       \<star> rw_resource_is (rw_resource_from_slens l) sh1 v1
     \<longlongrightarrow> \<langle>sh0 \<sharp> sh1\<rangle> \<star> \<langle>v0 = v1\<rangle> \<star>
       rw_resource_is (rw_resource_from_slens l) (sh0 + sh1) v0\<close>
    by (clarsimp simp add: resource_is_merge rw_resource_from_slens_def)
next
  fix sh0 sh1 :: share and v
  assume \<open>0 < sh0\<close> and \<open>0 < sh1\<close> and \<open>sh0 \<sharp> sh1\<close>
  from this and assms show
    \<open>rw_resource_is (rw_resource_from_slens l) (sh0 + sh1) v \<longlongrightarrow>
       rw_resource_is (rw_resource_from_slens l) sh0 v \<star> rw_resource_is (rw_resource_from_slens l) sh1 v\<close>
    by (clarsimp simp add: resource_is_merge rw_resource_from_slens_def resource_is_split)
next
  fix \<Gamma> v
  from assms show \<open>\<Gamma> ; rw_resource_write (rw_resource_from_slens l) v
     \<Turnstile>\<^sub>F generic_write_contract (rw_resource_is (rw_resource_from_slens l)) v\<close>
    by (simp add: rw_resource_from_slens_contracts)
      (simp add: rw_resource_write_def rw_resource_from_slens_def write_resource_spec)
next
  fix \<Gamma> sh v
  from assms show \<open>\<Gamma> ; rw_resource_read (rw_resource_from_slens l)
      \<Turnstile>\<^sub>F generic_read_contract (rw_resource_is (rw_resource_from_slens l)) v sh\<close>
    by (simp add: rw_resource_from_slens_contracts)
      (simp add: rw_resource_read_def rw_resource_from_slens_def read_resource_spec)
qed

lemma rw_resource_is_from_slens:
  assumes \<open>is_valid_slens l\<close>
  shows \<open>\<sigma> \<Turnstile> rw_resource_is (rw_resource_from_slens l) \<top> x
    \<longleftrightarrow> \<sigma> = lens_update l (Shared_Value \<top> x) 0\<close>
  by (clarsimp simp add: rw_resource_from_slens_def asat_def resource_is_def pull_back_assertion_def
    shareable_value_is_top_alt)

end
