(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Lens
  imports Prism
begin
(*>*)

section\<open>Lenses: functional references\<close>

text \<open>We use a \<^verbatim>\<open>lens\<close> or \<^emph>\<open>functional reference\<close> to model in-place update or reads of
deeply-nested fields within our model of the Rust language.  A lens over a record or other
product-like type (e.g., a tuple), here represented by the polymorphic type \<^typ>\<open>'s\<close>, consists of
two components:
\begin{enumerate*}
\item
A \<^emph>\<open>view\<close> function which allows us to view, or ``zoom in on'', some field of a record or
product-like datatype.  Here, the field of the record is modelled as a polymorphic type \<^typ>\<open>'a\<close>.
\item
A \<^emph>\<open>modification\<close> function which allows us to modify a field nested (potentially deeply) within a
record.
\end{enumerate*}

Various laws, introduced later, will be used to ensure that these two functions behave correctly, as
one would expect for a reference-like object, and which will introduce a notion of \<^emph>\<open>well-formed\<close>
lens.

Mathematically, one can think of as a lens as a \<^emph>\<open>quotient\<close> with specified lifting operations.\<close>
datatype_record ('s, 'a) lens =
  lens_view :: \<open>'s \<Rightarrow> 'a\<close>
  lens_update :: \<open>'a \<Rightarrow> 's \<Rightarrow> 's\<close>

text \<open>We can define an \<^emph>\<open>update\<close> function which sets the value of a field nested within a record
easily using the modification function of the lens:\<close>
definition lens_modify :: \<open>('s, 'a) lens \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's\<close> where
  \<open>lens_modify l f v \<equiv> lens_update l (f (lens_view l v)) v\<close>

text \<open>The following predicate introduces a notion of \<^emph>\<open>well-formed\<close> lens.  In particular, we have:
\begin{itemize*}
\item
If one views the content of a field after modifying it then they observe the modification,
\item
If a modification to a field is unobservable then updating the field with that modification has no
effect,
\item
Modifying a field twice, with two modifications, is the same as modifying the field once with a
single compound modification.
\item
Modifying a field is the same as updating a viewed field (this is a form of extensionality).
\end{itemize*}\<close>
definition is_valid_lens :: \<open>('s, 'a) lens \<Rightarrow> bool\<close> where
  \<open>is_valid_lens l \<longleftrightarrow>
     ((\<forall>x y. lens_view l (lens_update l y x) = y) \<and>
      (\<forall>x. lens_update l (lens_view l x) x = x) \<and>
      (\<forall>x y0 y1. lens_update l y1 (lens_update l y0 x) = lens_update l y1 x))\<close>

lemma is_valid_lensI:
  assumes \<open>\<forall>x y. lens_view l (lens_update l y x) = y\<close>
      and \<open>\<forall>x. lens_update l (lens_view l x) x = x\<close>
      and \<open>\<forall>x y0 y1. lens_update l y1 (lens_update l y0 x) = lens_update l y1 x\<close>
    shows \<open>is_valid_lens l\<close>
  using assms unfolding is_valid_lens_def by simp

lemma is_valid_lensE:
  assumes \<open>is_valid_lens l\<close>
      and \<open>(\<And>x y. lens_view l (lens_update l y x) = y)
        \<Longrightarrow> (\<And>x. lens_update l (lens_view l x) x = x)
        \<Longrightarrow> (\<And>x y0 y1. lens_update l y1 (lens_update l y0 x) = lens_update l y1 x)
        \<Longrightarrow> R\<close>
    shows \<open>R\<close>
  using assms unfolding is_valid_lens_def by simp

definition is_valid_lens_view_modify :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> bool\<close>
  where \<open>is_valid_lens_view_modify view modify \<equiv>
     (\<forall>f s. view (modify f s) = f (view s)) \<and>
     (\<forall>f s. f (view s) = view s \<longrightarrow> modify f s = s) \<and>
     (\<forall>f g s. modify f (modify g s) = modify (\<lambda>x. (f (g x))) s)
  \<close>

lemma is_valid_lens_view_modify_modify_via_update:
  assumes \<open>is_valid_lens_view_modify view modify\<close>
  shows \<open>modify f x = modify (\<lambda>_. f (view x)) x\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  let ?g = \<open>\<lambda>_. f (view x)\<close>
  have \<open>?lhs = modify ?g ?lhs\<close> 
    by (metis assms is_valid_lens_view_modify_def)
  moreover have \<open>?rhs = modify ?g ?rhs\<close>
    by (metis assms is_valid_lens_view_modify_def)
  moreover have \<open>modify ?g ?lhs = ?rhs\<close> 
    using assms by (clarsimp simp add: is_valid_lens_view_modify_def comp_def)
  ultimately show ?thesis
    by presburger
qed

definition make_lens_via_view_modify :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> ('a, 'b) lens\<close>
  where \<open>make_lens_via_view_modify view modify \<equiv>
    make_lens view (\<lambda>y. modify (\<lambda>_. y))\<close>

\<comment>\<open>Inline this definition during code generation to avoid bumping into ML value restriction for
polymorphic lens definitions (e.g. field lenses for polymorphic records):\<close>
declare make_lens_via_view_modify_def[code_unfold]

lemma is_valid_lens_via_modifyI':
  assumes \<open>is_valid_lens_view_modify view modify\<close>
  shows \<open>is_valid_lens (make_lens_via_view_modify view modify)\<close>
  using assms unfolding is_valid_lens_view_modify_def
  by (intro is_valid_lensI; clarsimp simp add: make_lens_via_view_modify_def)

lemma make_lens_via_view_modify_components:
  shows \<open>lens_view (make_lens_via_view_modify view modify) = view\<close>
    and \<open>lens_update (make_lens_via_view_modify view modify) = (\<lambda>y. modify (\<lambda>_. y))\<close>
    and \<open>is_valid_lens_view_modify view modify
           \<Longrightarrow> lens_modify (make_lens_via_view_modify view modify) = modify\<close>
  apply (intro ext; clarsimp simp add: make_lens_via_view_modify_def lens_modify_def)+
  using is_valid_lens_view_modify_modify_via_update by fastforce
  
lemma is_valid_lens_via_modifyI'':
  assumes \<open>is_valid_lens l\<close>
  shows \<open>is_valid_lens_view_modify (lens_view l) (lens_modify l)\<close>
    and \<open>l = make_lens_via_view_modify (lens_view l) (lens_modify l)\<close>
proof -
  show \<open>is_valid_lens_view_modify (lens_view l) (lens_modify l)\<close>
  using assms by (elim is_valid_lensE; clarsimp simp add: is_valid_lens_view_modify_def
    lens_modify_def make_lens_via_view_modify_def) 
next
  have \<open>lens_view (make_lens_via_view_modify (lens_view l) (lens_modify l)) = lens_view l\<close>
    by (clarsimp simp add: is_valid_lens_view_modify_def
        lens_modify_def make_lens_via_view_modify_def)
  moreover have \<open>lens_update (make_lens_via_view_modify (lens_view l) (lens_modify l)) = lens_update l\<close>
    by (intro ext, clarsimp simp add: is_valid_lens_view_modify_def
        lens_modify_def make_lens_via_view_modify_def)
  ultimately show \<open>l = make_lens_via_view_modify (lens_view l) (lens_modify l)\<close> 
    by (simp add: lens.expand)
qed

lemma lens_laws_update:
  assumes \<open>is_valid_lens l\<close>
  shows \<open>\<And>x y. lens_view l (lens_update l y x) = y\<close>
    and \<open>\<And>x. lens_update l (lens_view l x) x = x\<close>
    and \<open>\<And>x y0 y1. lens_update l y1 (lens_update l y0 x) = lens_update l y1 x\<close>
  using assms by (auto elim: is_valid_lensE)

lemma lens_laws_modify:
  assumes \<open>is_valid_lens l\<close>
  shows \<open>\<And>f s. lens_view l (lens_modify l f s) = f (lens_view l s)\<close>
    and \<open>\<And>f s. f (lens_view l s) = lens_view l s \<longrightarrow> lens_modify l f s = s\<close>
    and \<open>\<And>f g s. lens_modify l f (lens_modify l g s) = lens_modify l (\<lambda>x. (f (g x))) s\<close>
  using is_valid_lens_via_modifyI''(1)[OF assms]
  by (auto simp add: is_valid_lens_view_modify_def)

lemmas lens_laws = lens_laws_update lens_laws_modify

lemma is_valid_lens_via_modifyI:
  assumes \<open>\<And>f s. lens_view l (lens_modify l f s) = f (lens_view l s)\<close>
    and \<open>\<And>f s. f (lens_view l s) = lens_view l s \<longrightarrow> (lens_modify l f s = s)\<close>
    and \<open>\<And>f g s. lens_modify l f (lens_modify l g s) = lens_modify l (\<lambda>x. f (g x)) s\<close>
  shows \<open>is_valid_lens l\<close>
  using assms by (auto simp add: is_valid_lens_def lens_modify_def)

lemma is_valid_lens_via_modifyE:
  assumes \<open>is_valid_lens l\<close>
    and \<open>(\<And>f s. lens_view l (lens_modify l f s) = f (lens_view l s)) \<Longrightarrow>
         (\<And>f s. f (lens_view l s) = lens_view l s \<longrightarrow> (lens_modify l f s = s)) \<Longrightarrow>
         (\<And>f g s. lens_modify l f (lens_modify l g s) = lens_modify l (\<lambda>x. f (g x)) s) \<Longrightarrow>
         R\<close>
  shows \<open>R\<close>
  using is_valid_lens_via_modifyI''[OF assms(1)] assms (2)
  by (auto simp add: lens_modify_def make_lens_via_view_modify_def is_valid_lens_view_modify_def)

text\<open>The following is a \<^emph>\<open>congruence\<close> rule which describes what it means for two modifications to a
well-formed lens to be identical:\<close>
lemma lens_modify_congI [focus_intros]:
  assumes \<open>is_valid_lens l\<close>
      and \<open>f (lens_view l s) = g (lens_view l s)\<close>
    shows \<open>lens_modify l f s = lens_modify l g s\<close>
  using assms by (simp add: lens_modify_def)

subsection\<open>Lens disjointness\<close>

text \<open>We say that two lenses are disjoint if modifications to the underlying state
using those lenses commute.\<close>
definition disjoint_lenses :: \<open>('s, 'a) lens \<Rightarrow> ('s,'b) lens \<Rightarrow> bool\<close> where
  \<open>disjoint_lenses l\<^sub>1 l\<^sub>2 \<longleftrightarrow>
     (\<forall>f g s. lens_modify l\<^sub>1 f (lens_modify l\<^sub>2 g s) = lens_modify l\<^sub>2 g (lens_modify l\<^sub>1 f s))\<close>

text \<open>The following are introduction and elimination rules for the disjoint lens predicate:\<close>
lemma disjoint_lensesI [focus_intros]:
  assumes \<open>\<And>f g s. lens_modify l\<^sub>1 f (lens_modify l\<^sub>2 g s) = lens_modify l\<^sub>2 g (lens_modify l\<^sub>1 f s)\<close>
    shows \<open>disjoint_lenses l\<^sub>1 l\<^sub>2\<close>
  using assms by (simp add: disjoint_lenses_def)

lemma disjoint_lensesE [focus_elims]:
  assumes \<open>disjoint_lenses l\<^sub>1 l\<^sub>2\<close>
      and \<open>(\<And>f g s. lens_modify l\<^sub>1 f (lens_modify l\<^sub>2 g s) = lens_modify l\<^sub>2 g (lens_modify l\<^sub>1 f s)) \<Longrightarrow> R\<close>
    shows \<open>R\<close>
  using assms by (simp add: disjoint_lenses_def)

text\<open>The disjoint lens predicate is commutative:\<close>
lemma disjoint_lens_commute:
  shows \<open>disjoint_lenses l\<^sub>1 l\<^sub>2 = disjoint_lenses l\<^sub>2 l\<^sub>1\<close>
  by (auto simp add: disjoint_lenses_def)

text \<open>The following pair of results capture the fact that, for disjoint and valid lenses, modifying
through one lens will not affect view through the other lens:\<close>
lemma disjoint_lens_view1:
  assumes \<open>disjoint_lenses l\<^sub>1 l\<^sub>2\<close>
      and \<open>is_valid_lens l\<^sub>1\<close>
    shows \<open>lens_view l\<^sub>1 (lens_modify l\<^sub>2 f s) = lens_view l\<^sub>1 s\<close>
proof -
  from assms have \<open>s = lens_modify l\<^sub>1 (\<lambda>_. lens_view l\<^sub>1 s) s\<close>
    by (metis is_valid_lensE lens_modify_def)
  from this and assms have
       \<open>lens_modify l\<^sub>2 f s = lens_modify l\<^sub>1 (\<lambda>_. lens_view l\<^sub>1 s) (lens_modify l\<^sub>2 f s)\<close>
    by (auto elim: focus_elims)
  from this and assms show ?thesis
    by (metis is_valid_lens_via_modifyE)
qed

lemma disjoint_lens_view2:
  assumes \<open>disjoint_lenses l\<^sub>2 l\<^sub>1\<close>
      and \<open>is_valid_lens l\<^sub>1\<close>
    shows \<open>lens_view l\<^sub>1 (lens_modify l\<^sub>2 f s) = lens_view l\<^sub>1 s\<close>
  using assms by (meson disjoint_lens_commute disjoint_lens_view1)

subsection\<open>Basic lenses, and building more complex ones\<close>

text \<open>With a dedicate type of lenses we may now also introduce a few basic lenses, and an \<^emph>\<open>algebra\<close>
of operations over lenses satisfying various laws that allows us to combine them together.

First, we introduce the \<^emph>\<open>unit\<close> lens which makes no modification and has no effect:\<close>

definition lens_id :: \<open>('a, 'a) lens\<close> ("id\<^sub>L") where
  \<open>id\<^sub>L \<equiv> make_lens (\<lambda>x. x) (\<lambda>y _. y)\<close>

text \<open>Note that this unit lens is valid:\<close>
lemma unit_lens_is_valid_lensI [focus_intros, intro]:
  shows \<open>is_valid_lens id\<^sub>L\<close>
  by (simp add: lens_id_def is_valid_lens_def)

text\<open>Second, the \<^emph>\<open>zero\<close> lens which projects to the singleton type:\<close>

definition zero_lens :: \<open>('a, unit) lens\<close> ("0\<^sub>L") where
  \<open>0\<^sub>L \<equiv> make_lens (\<lambda>_. ()) (\<lambda>_ x. x)\<close>

text \<open>Note that this unit lens is valid:\<close>
lemma zero_lens_is_valid_lensI [focus_intros, intro]:
  shows \<open>is_valid_lens 0\<^sub>L\<close>
  by (simp add: zero_lens_def is_valid_lensI lens_update_def)

text \<open>We can also \<^emph>\<open>compose\<close> lenses together.  If we are given one lens that modifies a field, \<^verbatim>\<open>F\<close>,
nested within a record, \<^verbatim>\<open>R\<close>, and another lens that modifies a field, \<^verbatim>\<open>G\<close>, nested deeply within the
record type of the first field, \<^verbatim>\<open>F\<close>, then we can obtain a derived lens that performs the update of
field \<^verbatim>\<open>G\<close> with respect to \<^verbatim>\<open>R\<close>.  Note that this allows us to model in-place updates and reads of
fields within nested hierarchies of records using the ``dot operator'', \<^verbatim>\<open>R.F.G\<close>, familiar from
languages like Java and Rust:\<close>
definition compose_lens :: \<open>('a, 'b) lens \<Rightarrow> ('b, 'c) lens \<Rightarrow> ('a, 'c) lens\<close> (infixr \<open>\<circ>\<^sub>L\<close> 54) where
  \<open>l\<^sub>1 \<circ>\<^sub>L l\<^sub>2 \<equiv> make_lens_via_view_modify
      (lens_view l\<^sub>2 \<circ> lens_view l\<^sub>1) (lens_modify l\<^sub>1 \<circ> lens_modify l\<^sub>2)\<close>

lemma compose_lens_is_valid_core:
  assumes \<open>is_valid_lens l1\<close>
      and \<open>is_valid_lens l2\<close>
    shows \<open>is_valid_lens_view_modify (lens_view l2 \<circ> lens_view l1) (lens_modify l1 \<circ> lens_modify l2)\<close>
  using assms unfolding is_valid_lens_view_modify_def
  by (elim is_valid_lensE; clarsimp simp add: comp_def
    make_lens_via_view_modify_def lens_modify_def)

text \<open>If two lenses are valid then their composition is, also:\<close>
lemma compose_lens_is_valid_lens_preserving [focus_intros, intro]:
  assumes \<open>is_valid_lens l\<^sub>1\<close>
      and \<open>is_valid_lens l\<^sub>2\<close>
  shows \<open>is_valid_lens (l\<^sub>1 \<circ>\<^sub>L l\<^sub>2)\<close>
  by (simp add: assms compose_lens_def compose_lens_is_valid_core is_valid_lens_via_modifyI')

lemma compose_lens_components:
  shows \<open>lens_update (l\<^sub>1 \<circ>\<^sub>L l\<^sub>2) y x = lens_update l\<^sub>1 (lens_update l\<^sub>2 y (lens_view l\<^sub>1 x)) x\<close>
    and \<open>lens_view (l\<^sub>1 \<circ>\<^sub>L l\<^sub>2) = lens_view l\<^sub>2 \<circ> lens_view l\<^sub>1\<close>
    and \<open>is_valid_lens l\<^sub>1 \<Longrightarrow> is_valid_lens l\<^sub>2 \<Longrightarrow> 
         lens_modify (l\<^sub>1 \<circ>\<^sub>L l\<^sub>2) = lens_modify l\<^sub>1 \<circ> lens_modify l\<^sub>2\<close>
  by (auto simp add: compose_lens_def lens_modify_def compose_lens_is_valid_core
      make_lens_via_view_modify_components)

text \<open>The following pair of lemmas captures the fact that composing any lens, \<^verbatim>\<open>L\<close>, with the unit
lens that does nothing is equivalent to \<^verbatim>\<open>L\<close>:\<close>
lemma compose_lens_unit [focus_simps]:
  shows \<open>id\<^sub>L \<circ>\<^sub>L l = l\<close>
  by (cases l; auto intro!: ext simp add: compose_lens_def lens_id_def 
    make_lens_via_view_modify_def lens_modify_def)

lemma compose_lens_unit2 [focus_simps]:
  shows \<open>l \<circ>\<^sub>L id\<^sub>L = l\<close>
  by (cases l; auto intro!: ext simp add: compose_lens_def lens_id_def 
    make_lens_via_view_modify_def lens_modify_def)

lemma compose_lens_zero:
  assumes \<open>is_valid_lens l\<close>
  shows \<open>l \<circ>\<^sub>L 0\<^sub>L = 0\<^sub>L\<close>
  using assms by (cases l; auto elim!: is_valid_lensE intro!: ext simp add: compose_lens_def 
    zero_lens_def make_lens_via_view_modify_def lens_modify_def)

text \<open>Composition is associative for lenses.  This captures the idea that the ``dot operator'' of
Java and Rust is also associative, so \<^verbatim>\<open>(R.F).G\<close> is equivalent to \<^verbatim>\<open>R.(F.G)\<close> and therefore the
parentheses can be dispensed with:\<close>
lemma compose_lens_assoc [focus_simps]:
  shows \<open>(l\<^sub>1 \<circ>\<^sub>L l\<^sub>2) \<circ>\<^sub>L l\<^sub>3 = l\<^sub>1 \<circ>\<^sub>L (l\<^sub>2 \<circ>\<^sub>L l\<^sub>3)\<close>
  by (auto simp add: compose_lens_def make_lens_via_view_modify_def lens_modify_def intro!: ext)

text \<open>Moreover, if we have a pair of disjoint lenses then composing either one of them with a third
lens retains their disjoint character:\<close>
lemma disjoint_compose:
  assumes \<open>disjoint_lenses l\<^sub>1 l\<^sub>2\<close>
    shows \<open>disjoint_lenses l\<^sub>1 (l\<^sub>2 \<circ>\<^sub>L l\<^sub>3)\<close>
  using assms by (auto simp add: make_lens_via_view_modify_def disjoint_lenses_def compose_lens_def
    lens_modify_def) (metis lens_modify_def)

text \<open>The following pair of lenses can be used to view or modify the first- and second-projections
of a tuple type, respectively:\<close>
definition lens_fst :: \<open>('a \<times> 'b, 'a) lens\<close> ("fst\<^sub>L") where
  \<open>fst\<^sub>L \<equiv> make_lens fst (\<lambda>y0 (y, x). (y0, x))\<close>

definition lens_snd :: \<open>('a \<times> 'b, 'b) lens\<close> ("snd\<^sub>L") where
  \<open>snd\<^sub>L \<equiv> make_lens snd (\<lambda>y0 (x, y). (x, y0))\<close>

text \<open>Both of these lenses are also valid:\<close>
lemma lens_fst_is_valid_lensI [focus_intros, intro]:
  shows \<open>is_valid_lens fst\<^sub>L\<close>
  by (auto simp add: lens_fst_def lens_update_def is_valid_lens_def)

lemma lens_snd_is_valid_lensI [focus_intros, intro]:
  shows \<open>is_valid_lens snd\<^sub>L\<close>
  by (auto simp add: lens_snd_def lens_update_def is_valid_lens_def)

subsection\<open>The lens locale\<close>
locale lens_defs =
  fixes
    view :: \<open>'s \<Rightarrow> 't\<close> and
    update :: \<open>'t \<Rightarrow> 's \<Rightarrow> 's\<close>
begin

abbreviation \<open>get_lens \<equiv> make_lens view update\<close>
abbreviation \<open>modify \<equiv> lens_modify get_lens\<close>

end

locale lens = lens_defs +
  assumes
    lens_valid: \<open>is_valid_lens (make_lens view update)\<close>

(*<*)
end
(*>*)
