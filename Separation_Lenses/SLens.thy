(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory SLens
  imports 
    Lenses_And_Other_Optics.Lens
    Shallow_Separation_Logic.Separation_Algebra 
begin

section \<open>Separation lenses\<close>

text\<open>A \<^emph>\<open>separation lens\<close> is a lens between two separation algebras that is
compatible with the separation algebra structures.

Separation lenses are an axiomatic description of product separation algebras.

We primarily care about separation lenses as they allow for the 'pullback' of
various constructions (programs, specifications, proofs), thereby providing a
convenient way to extend implementations of the standard interfaces (e.g. references,
physical memory) to larger separation algebras and thereby making them composable.\<close>

subsection\<open>Definition\<close>

definition is_valid_slens :: \<open>('a::sepalg, 'b::sepalg) lens \<Rightarrow> bool\<close> where
  [simplified Let_def]: \<open>is_valid_slens l \<equiv>
     let view = lens_view l in
     let update = lens_update l
     in
       (is_valid_lens l) \<and>
       (\<forall>x y. x \<sharp> y \<longrightarrow> view x \<sharp> view y) \<and>
       (\<forall>x y. x \<sharp> y \<longrightarrow> view (x + y) = view x + view y) \<and>
       (\<forall>f x y. x \<sharp> y
          \<longrightarrow> f (view x) \<sharp> view y
          \<longrightarrow> f (view x + view y) = f (view x) + view y
          \<longrightarrow> lens_modify l f (x + y) = lens_modify l f x + y) \<and>
       (\<forall>f x y. x \<sharp> y
          \<longrightarrow> f (view x) \<sharp> view y
          \<longrightarrow> f (view x + view y) = f(view x) + view y
          \<longrightarrow> lens_modify l f x \<sharp> y)\<close>

lemma is_valid_slensI:
  assumes \<open>is_valid_lens l\<close>
      and \<open>\<And>x y. x \<sharp> y \<Longrightarrow> lens_view l x \<sharp> lens_view l y\<close>
      and \<open>\<And>x y. x \<sharp> y \<Longrightarrow> lens_view l (x + y) = lens_view l x + lens_view l y\<close>
      and \<open>\<And>f x y.
          x \<sharp> y
          \<Longrightarrow> f (lens_view l x) \<sharp> lens_view l y
          \<Longrightarrow> f (lens_view l x + lens_view l y) = f (lens_view l x) + lens_view l y
          \<Longrightarrow> lens_modify l f (x + y) = lens_modify l f x + y\<close>
      and \<open>\<And>f x y.
          x \<sharp> y
          \<Longrightarrow> f (lens_view l x) \<sharp> lens_view l y
          \<Longrightarrow> f(lens_view l x + lens_view l y) = f(lens_view l x) + lens_view l y
          \<Longrightarrow> lens_modify l f x \<sharp> y\<close>
    shows \<open>is_valid_slens l\<close>
  using assms unfolding is_valid_slens_def by auto

lemma is_valid_slensE:
  assumes \<open>is_valid_slens l\<close>
      and \<open>is_valid_lens l
           \<Longrightarrow> (\<And>x y. x \<sharp> y \<Longrightarrow> lens_view l x \<sharp> lens_view l y)
           \<Longrightarrow> (\<And>x y. x \<sharp> y \<Longrightarrow> lens_view l (x + y) = lens_view l x + lens_view l y)
           \<Longrightarrow> (\<And>f x y.
                    x \<sharp> y
                    \<Longrightarrow> f (lens_view l x) \<sharp> lens_view l y
                    \<Longrightarrow> f (lens_view l x + lens_view l y) = f (lens_view l x) + lens_view l y
                    \<Longrightarrow> lens_modify l f (x + y) = lens_modify l f x + y)
           \<Longrightarrow> (\<And>f x y.
                    x \<sharp> y
                    \<Longrightarrow> f (lens_view l x) \<sharp> lens_view l y
                    \<Longrightarrow> f(lens_view l x + lens_view l y) = f(lens_view l x) + lens_view l y
                    \<Longrightarrow> lens_modify l f x \<sharp> y)
           \<Longrightarrow> R\<close>
    shows \<open>R\<close>
  using assms unfolding is_valid_slens_def by auto

locale slens =
  fixes l :: \<open>('s::sepalg, 't::sepalg) lens\<close>
  assumes slens_valid: \<open>is_valid_slens l\<close>
declare slens_def[simp]

context slens
begin

lemma is_valid_slens_facts:
  shows lens_valid: \<open>is_valid_lens l\<close>
    and slens_view_local1: \<open>\<And>x y. x \<sharp> y \<Longrightarrow> lens_view l x \<sharp> lens_view l y\<close>
    and slens_view_local2: \<open>\<And>x y. x \<sharp> y \<Longrightarrow> lens_view l (x + y) = lens_view l x + lens_view l y\<close>
    and slens_update_local1: \<open>\<And>x y. 
          x \<sharp> y
          \<Longrightarrow> f (lens_view l x) \<sharp> lens_view l y
          \<Longrightarrow> f (lens_view l x + lens_view l y) = f (lens_view l x) + lens_view l y 
          \<Longrightarrow> lens_modify l f (x + y) = lens_modify l f x + y\<close> 
    and slens_update_local2: \<open>\<And>x y. 
          x \<sharp> y
          \<Longrightarrow> f (lens_view l x) \<sharp> lens_view l y
          \<Longrightarrow> f (lens_view l x + lens_view l y) = f (lens_view l x) + lens_view l y 
          \<Longrightarrow> lens_modify l f x \<sharp> y\<close> 
  using slens_valid by (auto elim: is_valid_slensE)

text\<open>We begin by proving that \<^verbatim>\<open>slens_update_local{1,2}\<close> imply their counterparts for updates
on \<^emph>\<open>constant\<close> functions. This can be safely skipped.\<close>

lemma slens_update_local_constant:
  assumes \<open>x = x0 + x1\<close>
      and \<open>x0 \<sharp> x1\<close>
      and \<open>y0' \<sharp> lens_view l x1\<close>
    shows \<open>lens_update l (y0' + lens_view l x1) x = lens_update l y0' x0 + x1\<close>
      and \<open>lens_update l y0' x0 \<sharp> x1\<close>
proof -
  from assms have view_add: \<open>lens_view l (x0 + x1) = lens_view l x0 + lens_view l x1\<close>
    using slens_view_local2 by fastforce
  let ?f = \<open>\<lambda>t. if t = lens_view l x0 + lens_view l x1 then y0' + lens_view l x1 else y0'\<close>
  { assume \<open>lens_view l x0 \<noteq> lens_view l x0 + lens_view l x1\<close>
    from this and assms have \<open>lens_update l (y0' + lens_view l x1) x = lens_update l y0' x0 + x1\<close>
      using slens_update_local1[of x0 x1 \<open>?f\<close>] slens_update_local2[of x0 x1 \<open>?f\<close>] 
      by (simp add: lens_modify_def view_add) }
  moreover { assume \<open>lens_view l x0 = lens_view l x0 + lens_view l x1\<close>
    from this have \<open>lens_view l x1 = 0\<close>
      by (metis assms(2) sepalg_apart_plus slens_view_local1 unique)
    from this have \<open>lens_update l (y0' + lens_view l x1) x = lens_update l y0' x0 + x1\<close>
      using assms slens_update_local1[of x0 x1 \<open>?f\<close>] slens_update_local2[of x0 x1 \<open>?f\<close>]
      by (simp add: lens_modify_def view_add) }
  ultimately show \<open>lens_update l (y0' + lens_view l x1) x = lens_update l y0' x0 + x1\<close>
    by auto
next
  let ?f = \<open>\<lambda>t. if t = lens_view l x0 + lens_view l x1 then y0' + lens_view l x1 else y0'\<close>
  { assume \<open>lens_view l x0 \<noteq> lens_view l x0 + lens_view l x1\<close>
    from this and assms have \<open>lens_update l y0' x0 \<sharp> x1\<close>
      using slens_update_local2[of x0 x1 \<open>?f\<close>] 
      by (force simp add: lens_modify_def) }
  moreover { assume \<open>lens_view l x0 = lens_view l x0 + lens_view l x1\<close>
    from this have \<open>lens_view l x1 = 0\<close>
      by (metis assms(2) sepalg_apart_plus slens_view_local1 unique)
    from this and \<open>lens_view l x0 = lens_view l x0 + lens_view l x1\<close> have \<open>lens_update l y0' x0 \<sharp> x1\<close>
      using assms lens_valid slens_update_local2[where f=\<open>?f\<close>]
      by (force simp add: lens_modify_def) }
  ultimately show \<open>lens_update l y0' x0 \<sharp> x1\<close>
    by auto
qed

lemma slens_update_local3: \<open>\<And>x x0 x1 y0'. x = x0 + x1 \<Longrightarrow> x0 \<sharp> x1 \<Longrightarrow>  y0' \<sharp> lens_view l x1 \<Longrightarrow>
          lens_update l (y0' + lens_view l x1) x = lens_update l y0' x0 + x1\<close>
  using slens_update_local_constant(1) by blast

lemma slens_update_local4: \<open>\<And>x x0 x1 y0'. x = x0 + x1 \<Longrightarrow> x0 \<sharp> x1 \<Longrightarrow>  y0' \<sharp> lens_view l x1 \<Longrightarrow>
          lens_update l y0' x0 \<sharp> x1\<close>
  using slens_update_local_constant(2) by blast

subsection\<open>Separation lenses as product projections\<close>

text\<open>Our goal, now, is to show that the separation lens axioms imply that the \<^verbatim>\<open>'s\<close> is (isomorphic to)
the \<^emph>\<open>separation algebra product\<close> of \<^verbatim>\<open>'t\<close> and the \<^emph>\<open>kernel\<close> of \<^verbatim>\<open>lens_view l :: 's \<Rightarrow> 't\<close>: Those elements \<^verbatim>\<open>x\<close>
where \<^verbatim>\<open>lens_view l x = 0\<close>. The corresponding embedding \<^verbatim>\<open>'t \<Rightarrow> 's\<close> is given by \<^verbatim>\<open>y \<mapsto> lens_update l (\<lambda>_. y) 0\<close>, and
the projection of \<^verbatim>\<open>'s\<close> onto the kernel of \<^verbatim>\<open>view\<close> is \<^verbatim>\<open>x \<mapsto> lens_update l 0 x\<close>.\<close>

abbreviation slens_embed :: \<open>'t \<Rightarrow> 's\<close> where
  \<open>slens_embed x \<equiv> lens_update l x 0\<close>

abbreviation slens_proj0 :: \<open>'s \<Rightarrow> 's\<close> where
  \<open>slens_proj0 x \<equiv> slens_embed (lens_view l x)\<close>

abbreviation slens_proj1 :: \<open>'s \<Rightarrow> 's\<close> where
  \<open>slens_proj1 x \<equiv> lens_update l 0 x\<close>

abbreviation \<open>slens_view \<equiv> lens_view l\<close>

notation slens_embed ("\<iota>")
notation slens_view ("\<pi>")
notation slens_proj0 ("\<rho>\<^sub>0")
notation slens_proj1 ("\<rho>\<^sub>1")

text\<open>First, we show that indeed every element is the disjoint sum of its two projections:\<close>

lemmas slens_lens_laws = lens_laws[OF lens_valid, simplified]

lemma slens_decompose:
  shows \<open>x = \<rho>\<^sub>0 x + \<rho>\<^sub>1 x\<close>
    and \<open>\<rho>\<^sub>0 x \<sharp> \<rho>\<^sub>1 x\<close>
proof -
  have \<open>x = lens_update l (\<pi> x) x\<close>
    by (simp add: slens_lens_laws)
  moreover from this have \<open>\<rho>\<^sub>0 x + \<rho>\<^sub>1 x = lens_update l (\<pi> x) (0 + \<rho>\<^sub>1 x)\<close>
    using slens_lens_laws
    by (metis (no_types, lifting) sepalg_ident sepalg_ident2 slens_update_local3 zero_disjoint
      zero_disjoint2)
  moreover have \<open>lens_update l (\<pi> x) (0 + \<rho>\<^sub>1 x) = lens_update l (\<pi> x) (\<rho>\<^sub>1 x)\<close>
    by simp
  moreover have \<open>lens_update l (\<pi> x) (\<rho>\<^sub>1 x) = x\<close>
    using slens_lens_laws  by presburger
  ultimately show \<open>x = \<rho>\<^sub>0 x + \<rho>\<^sub>1 x\<close>
    by simp
  show \<open>\<rho>\<^sub>0 x \<sharp> \<rho>\<^sub>1 x\<close>
    using slens_lens_laws slens_update_local4 by auto
qed

text\<open>We also note that the two projections are idempotent:\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma slens_proj0_idempotent:
  shows \<open>\<rho>\<^sub>0 (\<rho>\<^sub>0 x) = \<rho>\<^sub>0 x\<close>
  by (simp add: slens_lens_laws)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma slens_proj1_idempotent:
  shows \<open>\<rho>\<^sub>1 (\<rho>\<^sub>1 x) = \<rho>\<^sub>1 x\<close>
  by (simp add: slens_lens_laws)

lemma slens_complement_disj:
  shows \<open>x \<sharp> \<iota> y \<longleftrightarrow> \<pi> x \<sharp> y\<close>
  using slens_lens_laws by (metis disjoint_sym slens_update_local4 slens_view_local1 zero_disjoint2)

text\<open>The images of the two projections are disjoint:\<close>

lemma slens_proj_disjoint:
  shows \<open>\<rho>\<^sub>0 x \<sharp> \<rho>\<^sub>1 y\<close>
  using slens_lens_laws  slens_update_local4 by force

text\<open>If we know a decomposition of an element into its \<^verbatim>\<open>\<rho>\<^sub>0\<close> and \<^verbatim>\<open>\<rho>\<^sub>1\<close>-components,
applying \<^verbatim>\<open>\<rho>\<^sub>0\<close> forgets the \<^verbatim>\<open>\<rho>\<^sub>1\<close>-component:\<close>

lemma slens_proj0_sum:
  shows \<open>\<rho>\<^sub>0 (\<rho>\<^sub>0 x + \<rho>\<^sub>1 y) = \<rho>\<^sub>0 x\<close>
  using slens_lens_laws by (metis slens_decompose(1))

text\<open>Before establishing the analogue of \<^verbatim>\<open>slens_proj0_sum\<close> for \<^verbatim>\<open>\<rho>\<^sub>1\<close>, we first prove the following
useful characterization of \<^verbatim>\<open>update\<close> as updating the \<^verbatim>\<open>\<rho>\<^sub>0\<close>-component only:\<close>
corollary slens_update_components:
  shows \<open>\<rho>\<^sub>0 (lens_update l y x) = \<iota> y\<close>
    and \<open>\<rho>\<^sub>1 (lens_update l y x) = \<rho>\<^sub>1 x\<close>
  using slens_lens_laws by force+

lemma slens_update_alt:
  shows \<open>lens_update l y x = \<rho>\<^sub>1 x + \<iota> y\<close>
    and \<open>\<rho>\<^sub>1 x \<sharp> \<iota> y\<close>
  using slens_lens_laws
  apply (metis sepalg_comm slens_decompose(1) slens_proj_disjoint)
  using slens_lens_laws slens_update_local2
  apply (simp add: slens_complement_disj)
  done

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma slens_proj1_sum:
  shows \<open>\<rho>\<^sub>1 (\<rho>\<^sub>0 x + \<rho>\<^sub>1 y) = \<rho>\<^sub>1 y\<close>
  using slens_lens_laws by (metis slens_decompose(1))

text\<open>Next, we establish that the 'extension-by-0' embedding \<^verbatim>\<open>\<iota>: 't \<Rightarrow> 's\<close> is additive:\<close>

lemma slens_embed_additive:
  assumes \<open>y0 \<sharp> y1\<close>
  shows \<open>\<iota> y0 \<sharp> \<iota> y1\<close>
    and \<open> \<iota> (y0 + y1) = \<iota> y0 + \<iota> y1\<close>
  using slens_lens_laws apply -
  apply (simp add: assms slens_complement_disj)
  apply (metis assms slens_update_alt(1) slens_update_alt(2) slens_update_local3)
  done

lemma slens_complement_cancel_core:
  assumes \<open>\<pi> x = 0\<close>
  shows \<open>\<rho>\<^sub>1 (x + \<iota> y) = x\<close>
  using slens_lens_laws by (metis assms slens_update_alt(1))

lemma slens_complement_cancel:
  assumes \<open>x \<sharp> lens_update l y 0\<close>
  shows \<open>\<rho>\<^sub>1 (x + \<iota> y) = \<rho>\<^sub>1 x\<close>
proof -
  have \<open>x = \<rho>\<^sub>1 x + \<rho>\<^sub>0 x\<close>
    using slens_decompose by simp
  from this have \<open>\<rho>\<^sub>1 (x + \<iota> y) = \<rho>\<^sub>1 (\<rho>\<^sub>1 x + (\<rho>\<^sub>0 x + \<iota> y))\<close>
    by (metis assms sepalg_assoc slens_update_alt(2) slens_update_local4 slens_view_local1 zero_disjoint2)
  moreover have \<open>\<rho>\<^sub>0 x + \<iota> y = \<iota> (\<pi> x + y)\<close>
     by (metis assms slens_complement_disj slens_embed_additive(2))
  moreover from calculation have \<open>\<rho>\<^sub>1 (x + \<iota> y) = \<rho>\<^sub>1 (\<rho>\<^sub>1 x + \<iota> (\<pi> x + y))\<close>
    by presburger
  moreover have \<open>... = \<rho>\<^sub>1 (\<rho>\<^sub>1 x)\<close>
    using slens_lens_laws by (metis slens_update_alt(1))
  ultimately show ?thesis
    using slens_lens_laws by presburger
qed

lemma slens_complement_additive:
  assumes \<open>x0 \<sharp> x1\<close>
  shows \<open>\<rho>\<^sub>1 x0 \<sharp> \<rho>\<^sub>1 x1\<close>
    and \<open>\<rho>\<^sub>1 (x0 + x1) = \<rho>\<^sub>1 x0 + \<rho>\<^sub>1 x1\<close>
proof -
  let ?x00 = \<open>lens_update l (\<pi> x0) 0\<close>
  let ?x01 = \<open>lens_update l 0 x0\<close>
  let ?x10 = \<open>lens_update l (\<pi> x1) 0\<close>
  let ?x11 = \<open>lens_update l 0 x1\<close>
  have dec_x0: \<open>x0 = ?x00 + ?x01\<close>
    and dec_x1: \<open>x1 = ?x10 + ?x11\<close>
    and dec_x0_disj: \<open>?x00 \<sharp> ?x01\<close>
    and dec_x1_disj: \<open>?x10 \<sharp> ?x11\<close>
    using slens_decompose by blast+
  moreover from this and \<open>x0 \<sharp> x1\<close> have \<open>?x00 \<sharp> ?x10\<close> and \<open>?x00 \<sharp> ?x11\<close>
    and \<open>?x01 \<sharp> ?x10\<close> and \<open>?x01 \<sharp> ?x11\<close>
    using slens_update_local4 slens_view_local1 by auto
  moreover from this show \<open>?x01 \<sharp> ?x11\<close> by simp
  moreover from calculation have \<open>lens_update l 0 (x0 + x1)
     = lens_update l 0 (?x00 + ?x01 + ?x11 + ?x10)\<close>
    by (metis assms disjoint_sym sepalg_apart_plus2 sepalg_assoc sepalg_comm)
  moreover from calculation have \<open>?x00 + ?x01 + ?x11 + ?x10 = (?x00 + ?x01 + ?x11) + ?x10\<close>
    by blast
  moreover have \<open>lens_update l 0 ((?x00 + ?x01 + ?x11) + ?x10) = lens_update l 0 (?x00 + ?x01 + ?x11)\<close>
    using slens_complement_cancel
    by (metis assms dec_x0 dec_x1 sepalg_apart_assoc2 sepalg_comm slens_update_alt(2))
  ultimately show \<open>lens_update l 0 (x0 + x1) = ?x01 + ?x11\<close>
    by (metis sepalg_ident2 slens_lens_laws(1,3) slens_update_local3 zero_disjoint slens_update_local4)
qed

text\<open>Finally, we can show that \<^verbatim>\<open>update\<close> can be computed componentwise for disjoint decompositions.
Note that the separation lens axioms only give this in the case where one factor is unmodified.\<close>

lemma slens_update_general:
  assumes \<open>x0 \<sharp> x1\<close>
      and \<open>y0 \<sharp> y1\<close>
      and \<open>y0' \<sharp> y1'\<close>
    shows \<open>lens_update l (y0' + y1') (x0 + x1) = lens_update l y0' x0 + lens_update l y1' x1\<close>
proof -
  obtain #: \<open>\<rho>\<^sub>1 x0 \<sharp> \<rho>\<^sub>1 x1\<close> \<open>\<rho>\<^sub>1 x0 \<sharp> \<iota> y0'\<close> \<open>\<rho>\<^sub>1 x0 \<sharp> \<iota> y1'\<close> \<open> \<iota> y0' \<sharp> \<rho>\<^sub>1 x1\<close>
    using assms(1) slens_complement_additive(1) slens_update_alt(2) by auto
  with assms obtain disj: \<open>\<rho>\<^sub>1 x0 \<sharp> \<rho>\<^sub>1 x1 + \<iota> y1'\<close> \<open>\<iota> y0' \<sharp> \<rho>\<^sub>1 x1 + \<iota> y1'\<close>
    by (metis disjoint_sym slens_lens_laws(1) slens_update_alt(1) slens_update_local4 zero_disjoint2)
  have \<open>lens_update l (y0' + y1') (x0 + x1) = \<rho>\<^sub>1 (x0 + x1) + \<iota> (y0' + y1')\<close>
    using slens_update_alt(1) by blast
  also have \<open>... = \<rho>\<^sub>1 x0 + \<rho>\<^sub>1 x1 + (\<iota> y0' + \<iota> y1')\<close>
    using assms(1) assms(3) slens_complement_additive(2) slens_embed_additive(2) by presburger
  also have \<open>... = \<rho>\<^sub>1 x0 + (\<rho>\<^sub>1 x1 + (\<iota> y0' + \<iota> y1'))\<close>
    using # assms
    by (metis sepalg_assoc slens.slens_update_alt(2) slens_axioms slens_embed_additive(2))
  also have \<open>\<rho>\<^sub>1 x1 + (\<iota> y0' + \<iota> y1') = \<rho>\<^sub>1 x1 + \<iota> y0' + \<iota> y1'\<close>
    by (metis assms(3) sepalg_assoc slens_embed_additive(1) slens_update_alt(2))
  also have \<open>... = \<iota> y0' + (\<rho>\<^sub>1 x1 + \<iota> y1')\<close>
    using disj # assms
    by (metis sepalg_assoc sepalg_comm slens_embed_additive(1) slens_update_alt(2))
  also have \<open>\<rho>\<^sub>1 x0 + (\<iota> y0' + (\<rho>\<^sub>1 x1 + \<iota> y1')) = \<rho>\<^sub>1 x0 + \<iota> y0' + (\<rho>\<^sub>1 x1 + \<iota> y1')\<close>
    using disj # sepalg_assoc by blast
  also have \<open>... = lens_update l y0' x0 + lens_update l y1' x1\<close>
    by (metis slens_update_alt(1))
  finally show ?thesis .
qed

lemma slens_update_disjoint:
  assumes \<open>y0' \<sharp> y1\<close>
    shows \<open>lens_update l (y0' + y1) x0 = lens_update l y0' x0 + lens_update l y1 0\<close>
  by (metis assms sepalg_ident2 slens_update_general zero_disjoint)

text\<open>As a simple corollary to the decomposition of \<^verbatim>\<open>'s\<close> into \<^verbatim>\<open>'t\<close> and its complement, we obtain
liftability of decompositions in \<^verbatim>\<open>'t\<close> to \<^verbatim>\<open>'s\<close>:\<close>

lemma slens_lift_decomposition:
  assumes \<open>\<pi> x = y0 + y1\<close>
     and \<open>y0 \<sharp> y1\<close>
   obtains x0 x1 where \<open>\<pi> x0 = y0\<close> and \<open>\<pi> x1 = y1\<close> and \<open>x0 \<sharp> x1\<close> and \<open>x = x0 + x1\<close>
proof -
  let ?x0 = \<open>lens_update l y0 0\<close>
  let ?x1 = \<open>lens_update l y1 x\<close>
  have \<open>lens_view l ?x0 = y0\<close> and \<open>lens_view l ?x1 = y1\<close>
    using slens_lens_laws by simp+
  moreover have \<open>?x0 \<sharp> ?x1\<close>
    using slens_lens_laws by (metis assms(2) disjoint_sym slens_complement_disj)
  moreover have \<open>x = ?x0 + ?x1\<close>
    using slens_lens_laws
    by (metis (no_types, opaque_lifting) assms sepalg_ident slens_update_general zero_disjoint2)
  ultimately show ?thesis
    using that by blast
qed

no_notation slens_embed ("\<iota>")
no_notation slens_view ("\<pi>")
no_notation slens_proj0 ("\<rho>\<^sub>0")
no_notation slens_proj1 ("\<rho>\<^sub>1")

end

end
