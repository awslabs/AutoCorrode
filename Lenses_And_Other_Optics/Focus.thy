(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Focus
  imports Lens Prism
begin
(*>*)

section\<open>Foci\<close>

text\<open>A focus is a common generalization of focuses and prisms. With focuses roughly corresponding
to quotients and prisms to subsets, a focus can be seen as a way of representing a subquotient.

Typically, foci do not arise directly, but rather as the composition of (the liftings to foci of)
focuses and prisms.

Note that one could also use the type \<^typ>\<open>('a \<Rightarrow> 'a) \<Rightarrow> ('s \<Rightarrow> 's option)\<close> in the type of the
modification function, here, allowing the ``lifted'' function to return \<^term>\<open>None\<close> on values
outside of the domain the view. Here, we instead expect (and axiomatize below) that the modification
function is simply the identity on those inputs:\<close>
datatype_record ('s, 'a) focus_raw =
  focus_raw_view   :: \<open>'s \<Rightarrow> 'a option\<close>
  focus_raw_update :: \<open>'a \<Rightarrow> 's \<Rightarrow> 's\<close>

definition focus_raw_dom :: \<open>('v, 'w) focus_raw \<Rightarrow> 'v set\<close> where
  \<open>focus_raw_dom f \<equiv> dom (focus_raw_view f)\<close>

lemma focus_raw_domI:
  assumes \<open>focus_raw_view l x = Some y\<close>
    shows \<open>x \<in> focus_raw_dom l\<close>
using assms unfolding focus_raw_dom_def by auto

lemma focus_raw_domE:
  assumes \<open>x \<in> focus_raw_dom l\<close>
      and \<open>\<And>y. focus_raw_view l x = Some y \<Longrightarrow> R\<close>
    shows R
using assms unfolding focus_raw_dom_def by auto

text\<open>We never modify a value that's not in the domain of the focus, so the use of \<^term>\<open>the\<close> in the 
following definition should not cause problems:\<close>
definition focus_raw_modify :: \<open>('s, 'a) focus_raw \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's\<close> where
  \<open>focus_raw_modify l f s \<equiv> focus_raw_update l (f (the (focus_raw_view l s))) s\<close>

abbreviation focus_raw_is_view :: \<open>('s, 'a) focus_raw \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>focus_raw_is_view f s a \<equiv> focus_raw_view f s = Some a\<close>

text \<open>As generalisations of both focuses and prisms, a focus also has a notion of well-formedness.
Specifically, we have:
\begin{enumerate*}
\item
Viewing a focus after a modification is the same as applying the modification directly to the result
of viewing the focus,
\item
If a modification cannot be observed then applying the modification to a type has no effect,
\item
Applying two modifications in sequence is the same as applying a single, compound modification.
\item
Modifying a field is the same as updating a viewed field.
\end{enumerate*}

Note that these are straightforward generalisations of the laws of focus validity to focuses!\<close>
definition is_valid_focus :: \<open>('s, 'a) focus_raw \<Rightarrow> bool\<close> where
  \<open>is_valid_focus l \<longleftrightarrow>
      (\<forall>x y0 y1. focus_raw_view l x = Some y0  \<longrightarrow> focus_raw_view l (focus_raw_update l y1 x) = Some y1) \<and>
      (\<forall>x y. focus_raw_view l x = None  \<longrightarrow> focus_raw_view l (focus_raw_update l y x) = None) \<and>
      (\<forall>x y. focus_raw_view l x = Some y \<longrightarrow> focus_raw_update l y x = x) \<and>
      (\<forall>x y. focus_raw_view l x = None \<longrightarrow> focus_raw_update l y x = x) \<and>
      (\<forall>x y0 y1 y2. focus_raw_view l x = Some y0 \<longrightarrow> 
          focus_raw_update l y2 (focus_raw_update l y1 x) = focus_raw_update l y2 x)\<close>

text\<open>Any two types admit a valid focus between them. This is irrelevant in practice, but technically
important because it allows us to form the subtype of valid foci later.\<close>
definition dummy_focus :: \<open>('a, 'b) focus_raw\<close> where
  \<open>dummy_focus \<equiv> make_focus_raw (\<lambda>_. None) (\<lambda>_ x. x)\<close>

lemma dummy_focus_is_valid:
  shows \<open>is_valid_focus dummy_focus\<close>
by (simp add: dummy_focus_def is_valid_focus_def)

text \<open>The following are basic introduction and elimination rules for working with the
\<^verbatim>\<open>is_valid_focus\<close> predicate:\<close>
lemma is_valid_focusI:
  assumes \<open>\<And>x y0 y1. focus_raw_view l x = Some y0 \<Longrightarrow> focus_raw_view l (focus_raw_update l y1 x) = Some y1\<close>
      and \<open>\<And>x y. focus_raw_view l x = None  \<longrightarrow> focus_raw_view l (focus_raw_update l y x) = None\<close>
      and \<open>\<And>x y. focus_raw_view l x = Some y \<Longrightarrow> focus_raw_update l y x = x\<close>
      and \<open>\<And>x y. focus_raw_view l x = None \<Longrightarrow> focus_raw_update l y x = x\<close>
      and \<open>\<And>x y0 y1 y2. focus_raw_view l x = Some y0 \<Longrightarrow>
              focus_raw_update l y2 (focus_raw_update l y1 x) = focus_raw_update l y2 x\<close>
    shows \<open>is_valid_focus l\<close>
using assms by (auto simp add: is_valid_focus_def)

lemma is_valid_focusE:
  assumes \<open>is_valid_focus l\<close>
      and \<open>(\<And>x y0 y1. focus_raw_view l x = Some y0 \<Longrightarrow> focus_raw_view l (focus_raw_update l y1 x) = Some y1) \<Longrightarrow>
              (\<And>x y. focus_raw_view l x = None  \<longrightarrow> focus_raw_view l (focus_raw_update l y x) = None) \<Longrightarrow>
              (\<And>x y. focus_raw_view l x = Some y \<Longrightarrow> focus_raw_update l y x = x) \<Longrightarrow>
              (\<And>x y. focus_raw_view l x = None \<Longrightarrow> focus_raw_update l y x = x) \<Longrightarrow>
              (\<And>x y0 y1 y2. focus_raw_view l x = Some y0 \<Longrightarrow>
                focus_raw_update l y2 (focus_raw_update l y1 x) = focus_raw_update l y2 x) \<Longrightarrow> R\<close>
    shows R
using assms by (auto simp add: is_valid_focus_def)

lemma focus_raw_laws_update:
  assumes \<open>is_valid_focus l\<close>
    shows \<open>(\<And>x y0 y1. focus_raw_view l x = Some y0 \<Longrightarrow> focus_raw_view l (focus_raw_update l y1 x) = Some y1)\<close>
      and \<open>\<And>x y. focus_raw_view l x = None  \<longrightarrow> focus_raw_view l (focus_raw_update l y x) = None\<close>
      and \<open>\<And>x y. focus_raw_view l x = Some y \<Longrightarrow> focus_raw_update l y x = x\<close>
      and \<open>\<And>x y. focus_raw_view l x = None \<Longrightarrow> focus_raw_update l y x = x\<close>
      and \<open>\<And>x y0 y1 y2. focus_raw_view l x = Some y0 \<Longrightarrow>
            focus_raw_update l y2 (focus_raw_update l y1 x) = focus_raw_update l y2 x\<close>
using assms by (auto elim: is_valid_focusE)

text\<open>The following is an alternative axiomatization of foci in terms of update functions:\<close>
lemma is_valid_focus_via_modify:
  assumes \<open>is_valid_focus l\<close>
    shows \<open>\<And>f s. focus_raw_view l (focus_raw_modify l f s) = map_option f (focus_raw_view l s)\<close>
      and \<open>\<And>f s. map_option f (focus_raw_view l s) = focus_raw_view l s \<Longrightarrow> focus_raw_modify l f s = s\<close>
      and \<open>\<And>f g s. focus_raw_modify l f (focus_raw_modify l g s) = focus_raw_modify l (\<lambda>x. f (g x)) s\<close>
proof -
  fix f s show \<open>focus_raw_view l (focus_raw_modify l f s) = map_option f (focus_raw_view l s)\<close>
    using \<open>is_valid_focus l\<close> 
    by (cases \<open>focus_raw_view l s\<close>; auto elim!: is_valid_focusE simp add: focus_raw_modify_def)
next
  fix f s show \<open>map_option f (focus_raw_view l s) = focus_raw_view l s \<Longrightarrow> focus_raw_modify l f s = s\<close>
    using \<open>is_valid_focus l\<close> 
    by (clarsimp elim!: is_valid_focusE simp add: focus_raw_modify_def)
       (metis option.exhaust_sel option.map_sel)
next
  fix f g s show \<open>focus_raw_modify l f (focus_raw_modify l g s) 
                     = focus_raw_modify l (\<lambda>x. f (g x)) s\<close>
    using \<open>is_valid_focus l\<close> 
    by (cases \<open>focus_raw_view l s\<close>; auto elim!: is_valid_focusE simp add: focus_raw_modify_def)
qed

lemma focus_raw_laws_modify:
  assumes \<open>is_valid_focus l\<close>
    shows \<open>\<And>f s. focus_raw_view l (focus_raw_modify l f s) = map_option f (focus_raw_view l s)\<close>
      and \<open>\<And>f s. map_option f (focus_raw_view l s) = focus_raw_view l s \<Longrightarrow> focus_raw_modify l f s = s\<close>
      and \<open>\<And>f g s. focus_raw_modify l f (focus_raw_modify l g s) = focus_raw_modify l (\<lambda>x. f (g x)) s\<close>
using assms by (auto simp add: is_valid_focus_via_modify)

lemmas focus_raw_laws = focus_raw_laws_update focus_raw_laws_modify

lemma is_valid_focus_via_modifyE:
  assumes \<open>is_valid_focus l\<close>
      and \<open>(\<And>f s. focus_raw_view l (focus_raw_modify l f s) = map_option f (focus_raw_view l s)) \<Longrightarrow>
              (\<And>f s. map_option f (focus_raw_view l s) = focus_raw_view l s \<Longrightarrow> focus_raw_modify l f s = s) \<Longrightarrow>
              (\<And>f g s. focus_raw_modify l f (focus_raw_modify l g s) = focus_raw_modify l (\<lambda>x. f (g x)) s) \<Longrightarrow> R\<close>
    shows R
by (simp add: assms is_valid_focus_via_modify)

text\<open>The axioms in \<^verbatim>\<open>is_valid_focus_via_modify\<close> are indeed sufficient to construct a valid focus:\<close>
definition is_valid_view_modify :: \<open>('a \<Rightarrow> 'b option) \<Rightarrow> (('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> bool\<close> where
  \<open>is_valid_view_modify view modify \<longleftrightarrow>
     ((\<forall>f s. view (modify f s) = map_option f (view s)) \<and>
      (\<forall>f s. map_option f (view s) = view s \<longrightarrow> modify f s = s) \<and>
      (\<forall>f g s. modify f (modify g s) = modify (\<lambda>x. f (g x)) s))\<close>

lemma is_valid_view_modify_modify_via_update:
  assumes \<open>is_valid_view_modify view modify\<close>  
    shows \<open>modify f x = modify (\<lambda>_. f (the (view x))) x\<close>
proof -
  { assume \<open>x \<notin> dom view\<close> then have ?thesis 
    by (metis assms domIff is_valid_view_modify_def option.simps(8)) }
  moreover { assume \<open>x \<in> dom view\<close>
    then obtain y where \<open>view x = Some y\<close> 
      by blast
    then have \<open>map_option (\<lambda>_. f y) (view (modify f x)) = view (modify f x)\<close> 
      by (metis assms is_valid_view_modify_def option.simps(9))
    from this and \<open>is_valid_view_modify view modify\<close>  
    have \<open>modify (\<lambda>_. f y) (modify f x) = modify f x\<close> 
      by (metis is_valid_view_modify_def) 
    moreover from \<open>view x = Some y\<close> and \<open>is_valid_view_modify view modify\<close>  
      have \<open>modify (\<lambda>_. f y) (modify f x) = modify (\<lambda>_. f y) x\<close>
      by (clarsimp simp add: is_valid_view_modify_def)
    ultimately have ?thesis 
      using \<open>view x = Some y\<close> by fastforce
  }
  ultimately show ?thesis by auto
qed

lemma is_valid_focus_via_modify':
  assumes \<open>is_valid_focus l\<close>
    shows \<open>is_valid_view_modify (focus_raw_view l) (focus_raw_modify l)\<close>
using assms by (elim is_valid_focus_via_modifyE; clarsimp simp add: is_valid_view_modify_def)

definition make_focus_raw_via_view_modify :: \<open>('v \<Rightarrow> 'w option) \<Rightarrow> (('w \<Rightarrow> 'w) \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
      ('v, 'w) focus_raw\<close> where
  \<open>make_focus_raw_via_view_modify view modify \<equiv> make_focus_raw view (\<lambda>y. modify (\<lambda>_. y))\<close>

lemma is_valid_focus_via_modifyI:
  assumes \<open>\<And>f s. view (modify f s) = map_option f (view s)\<close>
      and \<open>\<And>f s. map_option f (view s) = view s \<Longrightarrow> modify f s = s\<close>
      and \<open>\<And>f g s. modify f (modify g s) = modify (\<lambda>x. f (g x)) s\<close>
    shows \<open>is_valid_focus (make_focus_raw_via_view_modify view modify)\<close>
using assms by (intro is_valid_focusI) (auto simp add: make_focus_raw_via_view_modify_def)

lemma is_valid_focus_via_modifyI':
  assumes \<open>is_valid_view_modify view modify\<close>
    shows \<open>is_valid_focus (make_focus_raw_via_view_modify view modify)\<close>
using assms by (intro is_valid_focus_via_modifyI) (auto simp add: is_valid_view_modify_def)

lemma make_focus_raw_via_view_modify_components:
  shows \<open>focus_raw_view (make_focus_raw_via_view_modify view modify) = view\<close>
    and \<open>focus_raw_update (make_focus_raw_via_view_modify view modify) = (\<lambda>y. modify (\<lambda>_. y))\<close>
    and \<open>is_valid_view_modify view modify \<Longrightarrow> focus_raw_modify (make_focus_raw_via_view_modify view modify) = modify\<close>
proof -
  show \<open>focus_raw_view (make_focus_raw_via_view_modify view modify) = view\<close>
    by (clarsimp simp add: make_focus_raw_via_view_modify_def)
next
  show \<open>focus_raw_update (make_focus_raw_via_view_modify view modify) = (\<lambda>y. modify (\<lambda>_. y))\<close>
    by (clarsimp simp add: make_focus_raw_via_view_modify_def)
next
  assume \<open>is_valid_view_modify view modify\<close>
  moreover {
    fix x y
    from calculation have \<open>focus_raw_modify (make_focus_raw_via_view_modify view modify) x y = modify x y\<close>
      by (clarsimp simp add: focus_raw_modify_def) (metis focus_raw.sel(1) focus_raw.sel(2)
        is_valid_view_modify_modify_via_update make_focus_raw_via_view_modify_def)
  }
  from this show \<open>focus_raw_modify (make_focus_raw_via_view_modify view modify) = modify\<close>
    by (intro ext) force
qed

text \<open>A lens can also be viewed as a focus:\<close>
definition lens_to_focus_raw :: \<open>('s, 'a) lens \<Rightarrow> ('s, 'a) focus_raw\<close> ("\<integral>''\<^sub>l") where
  \<open>lens_to_focus_raw l \<equiv> make_focus_raw (\<lambda>s. Some (lens_view l s)) (lens_update l)\<close>

lemma lens_to_focus_raw_components:
  shows \<open>focus_raw_view (lens_to_focus_raw l) x = Some (lens_view l x)\<close>
    and \<open>focus_raw_update (lens_to_focus_raw l) = lens_update l\<close>
    and \<open>focus_raw_modify (lens_to_focus_raw l) f v = lens_modify l f v\<close>
proof -
  show \<open>focus_raw_view (lens_to_focus_raw l) x = Some (lens_view l x)\<close>
    by transfer (simp add: lens_to_focus_raw_def)
next
  show \<open>focus_raw_update (lens_to_focus_raw l) = lens_update l\<close>
    by transfer (simp add: lens_to_focus_raw_def)
next
  show \<open>focus_raw_modify (lens_to_focus_raw l) f v = lens_modify l f v\<close>
    by transfer (simp add: focus_raw_modify_def lens_modify_def lens_to_focus_raw_def)
qed

text\<open>Lifting a valid focus into a focus grants us a valid focus:\<close>
lemma lens_to_focus_raw_valid:
  assumes \<open>is_valid_lens l\<close>
    shows \<open>is_valid_focus (lens_to_focus_raw l)\<close>
using assms by (intro is_valid_focusI) (auto simp add: lens_to_focus_raw_def is_valid_lens_def)

text\<open>A prism can also be viewed as a focus:\<close>
definition prism_to_focus_raw :: \<open>('s, 'a) prism \<Rightarrow> ('s, 'a) focus_raw\<close> ("\<integral>''\<^sub>p") where
  \<open>prism_to_focus_raw p \<equiv>
      let view  = \<lambda>y. prism_project p y;
          update = \<lambda>y x. if prism_project p x = None then x else prism_embed p y
      in make_focus_raw view update\<close>

lemma prism_to_focus_raw_components:
  shows \<open>focus_raw_view (prism_to_focus_raw p) = prism_project p\<close>
    and \<open>focus_raw_update (prism_to_focus_raw p) y x = (if x \<in> prism_dom p then prism_embed p y else x)\<close>
    and \<open>focus_raw_modify (prism_to_focus_raw p) f x =
        (if prism_project p x \<noteq> None then prism_embed p (f (the (prism_project p x))) else x)\<close>
proof -
  show \<open>focus_raw_view (prism_to_focus_raw p) = prism_project p\<close>
    by transfer (simp add: prism_to_focus_raw_def)
next
  show \<open>focus_raw_update (prism_to_focus_raw p) y x = (if x \<in> prism_dom p then prism_embed p y else x)\<close>
    by transfer (simp add: domIff prism_dom_def prism_to_focus_raw_def)
next
  show \<open>focus_raw_modify (\<integral>'\<^sub>p p) f x = (if prism_project p x \<noteq> None then prism_embed p (f (the (prism_project p x))) else x)\<close>
    by transfer (simp add: focus_raw_modify_def prism_to_focus_raw_def)
qed

text \<open>Lifting a valid prism into a focus grants us a valid focus:\<close>
lemma prism_to_focus_raw_valid:
  assumes \<open>is_valid_prism p\<close>
    shows \<open>is_valid_focus (prism_to_focus_raw p)\<close>
using assms by (intro is_valid_focusI) (auto simp add: is_valid_prism_def prism_to_focus_raw_def
  prism_dom_def)

text\<open>The following builds a focus out of a pair of mutually inverse bijections:\<close>
definition iso_focus_raw :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) focus_raw\<close> ("iso\<^sub>\<integral>") where
  \<open>iso_focus_raw g h \<equiv> prism_to_focus_raw (iso_prism g h)\<close>

lemma iso_focus_raw_components:
  shows \<open>focus_raw_view (iso_focus_raw  g h) x = Some (g x)\<close>
    and \<open>focus_raw_update (iso_focus_raw g h) y x = h y\<close>  
by (auto simp add: iso_focus_raw_def iso_prism_def prism_to_focus_raw_def)

lemma iso_focus_raw_valid:
  assumes \<open>\<And>x. f (g x) = x\<close>
      and \<open>\<And>y. g (f y) = y\<close>
    shows \<open>is_valid_focus (iso_focus_raw f g)\<close>
by (simp add: assms iso_focus_raw_def iso_prism_valid prism_to_focus_raw_valid)
  
text\<open>Like lenses, we may also provide a library of basic focuses. The following is the analogue of
the unit focus, the \<^emph>\<open>unit\<close> focus, which has no effect:\<close>
definition unit_focus_raw :: \<open>('a, 'a) focus_raw\<close> where
  \<open>unit_focus_raw \<equiv> make_focus_raw Some (\<lambda>y x. y)\<close>

text\<open>The unit focus is necessarily a valid, well-behaved focus:\<close>
lemma unit_focus_raw_valid:
  shows \<open>is_valid_focus unit_focus_raw\<close>
by (auto simp add: unit_focus_raw_def is_valid_focus_def focus_raw_update_def)

text\<open>Similarly, we may \<^emph>\<open>compose\<close> focuses together to produce larger, more complex, compound
focuses:\<close>
lemma focus_raw_compose_valid_core:
  assumes \<open>is_valid_focus l1\<close>
      and \<open>is_valid_focus l2\<close>
    shows \<open>is_valid_view_modify
             (\<lambda>x. Option.bind (focus_raw_view l1 x) (focus_raw_view l2))
             (\<lambda>f. focus_raw_modify l1 (focus_raw_modify l2 f))\<close>
using assms by (elim is_valid_focus_via_modifyE) (auto simp add: is_valid_view_modify_def split!:
  Option.bind_splits)

definition focus_raw_compose :: \<open>('a, 'b) focus_raw \<Rightarrow> ('b, 'c) focus_raw \<Rightarrow> ('a, 'c) focus_raw\<close> where
  \<open>focus_raw_compose l1 l2 \<equiv>
     make_focus_raw_via_view_modify (\<lambda>x. Option.bind (focus_raw_view l1 x) (focus_raw_view l2))
        (\<lambda>f. focus_raw_modify l1 (focus_raw_modify l2 f))\<close>
notation focus_raw_compose (infixr "\<diamondop>''" 59)

text\<open>Composing two valid focusses together grants us another valid focus:\<close>
lemma focus_raw_compose_valid:
  assumes \<open>is_valid_focus l1\<close>
      and \<open>is_valid_focus l2\<close>
    shows \<open>is_valid_focus (focus_raw_compose l1 l2)\<close>
by (simp add: assms focus_raw_compose_def focus_raw_compose_valid_core is_valid_focus_via_modifyI')

lemma focus_raw_compose_components:
  assumes \<open>is_valid_focus l1\<close>
      and \<open>is_valid_focus l2\<close>
    shows \<open>focus_raw_view (focus_raw_compose l1 l2)
              = (\<lambda>x. Option.bind (focus_raw_view l1 x) (focus_raw_view l2))\<close>
      and \<open>focus_raw_modify (focus_raw_compose l1 l2)
              = (\<lambda>f. focus_raw_modify l1 (focus_raw_modify l2 f))\<close>
      and \<open>focus_raw_update (focus_raw_compose l1 l2)
              = (\<lambda>y. focus_raw_modify l1 (focus_raw_modify l2 (\<lambda>_. y)))\<close>
using assms by (auto simp add: focus_raw_compose_def make_focus_raw_via_view_modify_components
  focus_raw_compose_valid_core)

text\<open>Prism-to-focus conversion is compatible with prism/focus composition:\<close>
lemma prism_to_focus_raw_compose:
  assumes \<open>is_valid_prism pA\<close>
    shows \<open>\<integral>'\<^sub>p (pA \<diamondop>\<^sub>p pB) = (\<integral>'\<^sub>p pA) \<diamondop>' (\<integral>'\<^sub>p pB)\<close>
using assms by (auto simp add: is_valid_prism_def prism_compose_def focus_raw_compose_def
  prism_to_focus_raw_def focus_raw_modify_def prism_dom_def bind_eq_Some_conv
  make_focus_raw_via_view_modify_def intro!:ext)

text\<open>The following pair of lemmas state that composing any other focus with the unit focus has no
effect:\<close>
lemma focus_raw_compose_unit [focus_simps]:
  shows \<open>unit_focus_raw \<diamondop>' l = l\<close>
by (cases l) (auto intro!: ext simp add: make_focus_raw_via_view_modify_def focus_raw_modify_def
  unit_focus_raw_def focus_raw_compose_def) 

lemma focus_raw_compose_unit2 [focus_simps]:
  shows \<open>l \<diamondop>' unit_focus_raw = l\<close>
by (cases l) (auto intro!: ext simp add: make_focus_raw_via_view_modify_def focus_raw_modify_def 
  unit_focus_raw_def focus_raw_compose_def) 

text\<open>The following are technical introduction, elimination, and destruction rules for working with
views of (potentially composed) \<^verbatim>\<open>focus_raw\<close>s:\<close>
lemma focus_raw_view_composeI [focus_intros]:
  assumes \<open>focus_raw_view l1 v = Some v'\<close>
      and \<open>focus_raw_view l2 v' = Some v''\<close>
    shows \<open>focus_raw_view (focus_raw_compose l1 l2) v = Some v''\<close>
using assms by (clarsimp simp add: focus_raw_compose_def make_focus_raw_via_view_modify_def)

lemma focus_raw_view_compose_destruct:
  assumes \<open>focus_raw_view (focus_raw_compose l1 l2) v = Some v''\<close>
  obtains v' where \<open>focus_raw_view l1 v = Some v'\<close> and \<open>focus_raw_view l2 v' = Some v''\<close>
using assms by (clarsimp simp add: focus_raw_compose_def make_focus_raw_via_view_modify_def)
  (meson focus_raw_compose_def bind_eq_Some_conv)

lemma focus_raw_view_composeE [focus_elims]:
  assumes \<open>focus_raw_view (focus_raw_compose l1 l2) v = Some v''\<close>
      and \<open>\<And>v'. focus_raw_view l1 v = Some v' \<Longrightarrow> focus_raw_view l2 v' = Some v'' \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms focus_raw_view_compose_destruct by metis

text\<open>Composition of focuses is associative, just like focuses:\<close>
lemma focus_raw_compose_assoc:
  assumes \<open>is_valid_focus l1\<close>
      and \<open>is_valid_focus l2\<close>
      and \<open>is_valid_focus l3\<close>
    shows \<open>(l1 \<diamondop>' l2) \<diamondop>' l3 = l1 \<diamondop>' (l2 \<diamondop>' l3)\<close>
using assms by (auto simp add: focus_raw_compose_def make_focus_raw_via_view_modify_def
  focus_raw_modify_def elim!: is_valid_focusE intro!: ext) (metis (full_types) bind.bind_lunit
  option.collapse)

lemma focus_raw_view_lens_assoc:
  shows \<open>focus_raw_view (focus_raw_compose (lens_to_focus_raw l) f) v =
            focus_raw_view f (lens_view l v)\<close>
by (simp add: focus_raw_compose_def lens_to_focus_raw_def make_focus_raw_via_view_modify_def)

text \<open>Similarly, there is also a notion of disjointedness for focuses.  Note that the laws governing
this are straightforward generalisations of the laws for disjoint focuses:\<close>
definition disjoint_focus :: \<open>('s, 'a) focus_raw \<Rightarrow> ('s, 'w) focus_raw \<Rightarrow> bool\<close> where
  \<open>disjoint_focus r\<^sub>1 r\<^sub>2 \<longleftrightarrow> (\<forall>b f g.
     focus_raw_modify r\<^sub>1 f (focus_raw_modify r\<^sub>2 g b) = focus_raw_modify r\<^sub>2 g (focus_raw_modify r\<^sub>1 f b) \<and>
     focus_raw_view r\<^sub>1 (focus_raw_modify r\<^sub>2 g b) = focus_raw_view r\<^sub>1 b \<and>
     focus_raw_view r\<^sub>2 (focus_raw_modify r\<^sub>1 f b) = focus_raw_view r\<^sub>2 b)\<close>

text \<open>The following are technical introduction and elimination rules for working with disjoint
focuses in proofs:\<close>
lemma disjoint_focus_raw_updateI [focus_intros]:
  assumes \<open>\<And>b f g. focus_raw_modify r\<^sub>1 f (focus_raw_modify r\<^sub>2 g b) = focus_raw_modify r\<^sub>2 g (focus_raw_modify r\<^sub>1 f b)\<close>
      and \<open>\<And>b f g. focus_raw_view r\<^sub>1 (focus_raw_modify r\<^sub>2 g b) = focus_raw_view r\<^sub>1 b\<close>
      and \<open>\<And>b f g. focus_raw_view r\<^sub>2 (focus_raw_modify r\<^sub>1 f b) = focus_raw_view r\<^sub>2 b\<close>
    shows \<open>disjoint_focus r\<^sub>1 r\<^sub>2\<close>
using assms by (auto simp add: disjoint_focus_def)

lemma disjoint_focusE [focus_elims]:
  assumes \<open>disjoint_focus r\<^sub>1 r\<^sub>2\<close>
      and \<open>\<And>b f g. focus_raw_modify r\<^sub>1 f (focus_raw_modify r\<^sub>2 g b) = focus_raw_modify r\<^sub>2 g (focus_raw_modify r\<^sub>1 f b) \<Longrightarrow>
             focus_raw_view r\<^sub>1 (focus_raw_modify r\<^sub>2 g b) = focus_raw_view r\<^sub>1 b \<Longrightarrow>
              focus_raw_view r\<^sub>2 (focus_raw_modify r\<^sub>1 f b) = focus_raw_view r\<^sub>2 b \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: disjoint_focus_def)

text\<open>The following definition intuitively captures that the given focus factors through the
(focus of the) prism associated to the given subset.\<close>
abbreviation focus_raw_factors :: \<open>('v set) \<Rightarrow> ('v, 'w) focus_raw \<Rightarrow> bool\<close> where
  \<open>focus_raw_factors P f \<equiv> focus_raw_dom f \<subseteq> P\<close>

lemma focus_raw_dom_compose:
  shows \<open>focus_raw_dom (f0 \<diamondop>' f1) \<subseteq> focus_raw_dom f0\<close> 
by (clarsimp simp add: focus_raw_dom_def focus_raw_compose_def make_focus_raw_via_view_modify_def
  bind_eq_Some_conv)

lemma prism_to_focus_raw_dom[simp]:
  shows \<open>focus_raw_dom (\<integral>'\<^sub>p p) = prism_dom p\<close>
by (simp add: focus_raw_dom_def prism_dom_def prism_to_focus_raw_def)

definition factor_focus_through_prism :: \<open>('v, 't) focus_raw \<Rightarrow> ('v, 'w) prism \<Rightarrow> ('w, 't) focus_raw\<close> where
  \<open>factor_focus_through_prism f p \<equiv>
     let view   = \<lambda>w. focus_raw_view f (prism_embed p w);
         update = \<lambda>(y::'t) (w::'w). the (prism_project p (focus_raw_update f y (prism_embed p w)))
      in make_focus_raw view update\<close>

lemma focus_raw_factors_prism_core:
    fixes p :: \<open>('v, 'w) prism\<close>
      and f :: \<open>('v, 't) focus_raw\<close>
  assumes \<open>is_valid_prism p\<close>
      and \<open>is_valid_focus f\<close>
      and \<open>focus_raw_dom f \<subseteq> prism_dom p\<close>
    shows \<open>let f' = factor_focus_through_prism f p in
            f = \<integral>'\<^sub>p p \<diamondop>' f'\<close>
proof -
  let ?f'_view = \<open>\<lambda>w. focus_raw_view f (prism_embed p w)\<close>
  let ?f'_update = \<open>\<lambda>(y :: 't) (w :: 'w). the (prism_project p (focus_raw_update f y (prism_embed p w)))\<close>
  let ?f' = \<open>make_focus_raw ?f'_view ?f'_update\<close>
  from \<open>focus_raw_dom f \<subseteq> prism_dom p\<close> have \<open>f = \<integral>'\<^sub>p p \<diamondop>' ?f'\<close>
  proof -
  { fix x :: 'v
    have \<open>focus_raw_view f x = focus_raw_view (\<integral>'\<^sub>p p \<diamondop>' ?f') x\<close>
    proof -
    { assume \<open>x \<notin> prism_dom p\<close>
      moreover from this have \<open>x \<notin> focus_raw_dom f\<close>
        using \<open>focus_raw_factors (prism_dom p) f\<close> by auto
        ultimately have \<open>focus_raw_view f x = None\<close> and \<open>focus_raw_view (\<integral>'\<^sub>p p \<diamondop>' ?f') x = None\<close>
        apply (simp add: domIff focus_raw_dom_def)
        using \<open>x \<notin> prism_dom p\<close> focus_raw_dom_compose focus_raw_dom_def apply fastforce
        done
      then have ?thesis
        by simp 
    }
    moreover { 
      assume \<open>x \<in> prism_dom p\<close>
      from this and \<open>is_valid_prism p\<close> obtain w where \<open>x = prism_embed p w\<close>
        using prism_domE' by metis
      from this and \<open>is_valid_prism p\<close> have ?thesis 
        by (simp add: focus_raw_compose_def is_valid_prism_def make_focus_raw_via_view_modify_def 
          prism_to_focus_raw_def) }
      ultimately show ?thesis 
        by auto
      qed
    }
    note A = this
    { fix y :: 't and x :: 'v
      have \<open>focus_raw_update f y x = focus_raw_update (\<integral>'\<^sub>p p \<diamondop>' ?f') y x\<close>
      proof -
      { assume \<open>x \<notin> prism_dom p\<close>
        then have \<open>x \<notin> focus_raw_dom f\<close> 
          using \<open>focus_raw_dom f \<subseteq> prism_dom p\<close> by blast
        from this and \<open>is_valid_focus f\<close> have \<open>focus_raw_update f y x = x\<close>  
          by (simp add: domIff focus_raw_dom_def focus_raw_modify_def is_valid_focus_def)
        moreover from \<open>x \<notin> prism_dom p\<close> have \<open>focus_raw_update (\<integral>'\<^sub>p p \<diamondop>' ?f') y x = x\<close>
          by (clarsimp simp add: prism_dom_def focus_raw_compose_def prism_to_focus_raw_def
            make_focus_raw_via_view_modify_def focus_raw_modify_def split!: option.splits)
        ultimately have ?thesis
          by auto 
      }
      moreover {
        assume \<open>x \<in> prism_dom p\<close> and \<open>x \<notin> focus_raw_dom f\<close>
        from this and \<open>is_valid_prism p\<close> obtain w where \<open>x = prism_embed p w\<close> 
          using prism_domE' by metis
        moreover from assms and \<open>x \<notin> focus_raw_dom f\<close> have \<open>focus_raw_update f y x = x\<close> 
          by (simp add: assms(2) domIff focus_raw_dom_def is_valid_focus_def)
        ultimately have ?thesis
          using  \<open>is_valid_prism p\<close> by (clarsimp simp add: is_valid_prism_def focus_raw_compose_def 
            prism_to_focus_raw_def focus_raw_dom_def make_focus_raw_via_view_modify_def focus_raw_modify_def)
      } 
      moreover {
        assume \<open>x \<in> focus_raw_dom f\<close>
        from this have \<open>x \<in> prism_dom p\<close> 
          using \<open>focus_raw_dom f \<subseteq> prism_dom p\<close> by blast 
        moreover from \<open>x \<in> focus_raw_dom f\<close> have \<open>focus_raw_update f y x \<in> focus_raw_dom f\<close>
          by (clarsimp simp add: domIff focus_raw_dom_def) (meson assms(2) is_valid_focusE)
        moreover from this have \<open>focus_raw_update f y x \<in> prism_dom p\<close>
          using \<open>focus_raw_dom f \<subseteq> prism_dom p\<close>  by blast 
        moreover from this and \<open>is_valid_prism p\<close> obtain w' where \<open>focus_raw_update f y x = prism_embed p w'\<close> 
          using prism_domE' by metis
        ultimately have ?thesis
          using  \<open>is_valid_prism p\<close> by (clarsimp simp add: is_valid_prism_def focus_raw_compose_def 
            prism_to_focus_raw_def focus_raw_dom_def make_focus_raw_via_view_modify_def focus_raw_modify_def
            split!: option.splits elim!: prism_domE) 
      }
      ultimately show ?thesis 
        by blast
      qed 
    }
    note B = this
    from A and B show ?thesis
      by (intro focus_raw.expand; safe; blast)
  qed
  from this show ?thesis 
    by (simp add: factor_focus_through_prism_def)
qed

text\<open>The following validates our intuition for \<^verbatim>\<open>focus_raw_factors P f\<close>: If \<^verbatim>\<open>P = prism_dom p\<close> for
some valid prism \<^verbatim>\<open>p\<close>, then indeed \<^verbatim>\<open>focus_raw_factors P f\<close> captures that \<^verbatim>\<open>f\<close> factors through
\<^verbatim>\<open>\<integral>'\<^sub>p p\<close>:\<close>
lemma focus_raw_factors_prism:
    fixes p :: \<open>('v, 'w) prism\<close>
      and f :: \<open>('v, 't) focus_raw\<close>
  assumes \<open>is_valid_prism p\<close>
      and \<open>is_valid_focus f\<close>
    shows \<open>(focus_raw_dom f \<subseteq> prism_dom p) \<longleftrightarrow> (\<exists>f' :: ('w, 't) focus_raw. f = \<integral>'\<^sub>p p \<diamondop>' f')\<close>
proof -
  { fix f' :: \<open>('w, 't) focus_raw\<close> 
    assume \<open>is_valid_focus f'\<close> and \<open>f = \<integral>'\<^sub>p p \<diamondop>' f'\<close>
    then have \<open>focus_raw_dom f \<subseteq> prism_dom p\<close> 
      using focus_raw_dom_compose by force }
  moreover {
    assume \<open>focus_raw_dom f \<subseteq> prism_dom p\<close>
    then have \<open>(\<exists>f' :: ('w, 't) focus_raw. f = \<integral>'\<^sub>p p \<diamondop>' f')\<close> 
      by (meson assms focus_raw_factors_prism_core)
  }
  ultimately show ?thesis 
    by (metis focus_raw_dom_compose prism_to_focus_raw_dom)
qed

lemma focus_raw_factors_prism_update:
    fixes p :: \<open>('v, 'w) prism\<close>
      and f :: \<open>('v, 't) focus_raw\<close>
  assumes \<open>is_valid_prism p\<close>
      and \<open>is_valid_focus f\<close>
      and \<open>focus_raw_dom f \<subseteq> prism_dom p\<close>
    shows \<open>Some (focus_raw_update (factor_focus_through_prism f p) y x) = 
             prism_project p (focus_raw_update f y (prism_embed p x))\<close>
      and \<open>prism_embed p (focus_raw_update (factor_focus_through_prism f p) y x)
             = focus_raw_update f y (prism_embed p x)\<close>
proof -
  let ?f' = \<open>factor_focus_through_prism f p\<close>
  from focus_raw_factors_prism_core have 
    \<open>\<And>x. focus_raw_update (\<integral>'\<^sub>p p \<diamondop>' ?f') y x = focus_raw_update f y x\<close>
    using assms by fastforce
  from this have \<open>focus_raw_update (\<integral>'\<^sub>p p \<diamondop>' ?f') y (prism_embed p x) = focus_raw_update f y (prism_embed p x)\<close>
    by simp
  from this show \<open>Some (focus_raw_update (factor_focus_through_prism f p) y x) = 
             prism_project p (focus_raw_update f y (prism_embed p x))\<close>
    using \<open>is_valid_prism p\<close> apply (clarsimp simp add: is_valid_prism_def prism_to_focus_raw_def 
      focus_raw_compose_def make_focus_raw_via_view_modify_def focus_raw_modify_def split!: option.splits) 
    by (metis bind.bind_lunit domIff option.distinct(1) option.sel prism_dom_def)
  from this show \<open>prism_embed p (focus_raw_update (factor_focus_through_prism f p) y x)
             = focus_raw_update f y (prism_embed p x)\<close> 
    by (metis assms(1) is_valid_prism_def)
qed

lemma focus_raw_factors_prism_modify:
    fixes p :: \<open>('v, 'w) prism\<close>
      and f :: \<open>('v, 't) focus_raw\<close>
  assumes \<open>is_valid_prism p\<close>
      and \<open>is_valid_focus f\<close>
      and \<open>focus_raw_dom f \<subseteq> prism_dom p\<close>
    shows \<open>Some (focus_raw_modify (factor_focus_through_prism f p) g x) = 
             prism_project p (focus_raw_modify f g (prism_embed p x))\<close>
      and \<open>prism_embed p (focus_raw_modify (factor_focus_through_prism f p) g x)
             = focus_raw_modify f g (prism_embed p x)\<close>
  using assms by (auto simp add: focus_raw_modify_def focus_raw_factors_prism_update)
    (auto simp add: factor_focus_through_prism_def)

text\<open>If a focus factors through a prism, the factorization is unique:\<close>
lemma focus_raw_factors_prism_unique:
    fixes f :: \<open>('v, 't) focus_raw\<close> 
      and p :: \<open>('v, 'w) prism\<close>
      and f' :: \<open>('w, 't) focus_raw\<close>
  assumes \<open>is_valid_focus f\<close>
      and \<open>is_valid_prism p\<close>
      and \<open>f = \<integral>'\<^sub>p p \<diamondop>' f'\<close>
    shows \<open>f' = factor_focus_through_prism f p\<close> (is \<open>_ = ?f''\<close>)
proof -
  let ?f'_view = \<open>\<lambda>w. focus_raw_view f (prism_embed p w)\<close>
  have \<open>\<And>x. focus_raw_view f' x = ?f'_view x\<close>
  proof -
    fix x
    have \<open>Some x = prism_project p (prism_embed p x)\<close> 
      by (metis assms(2) is_valid_prism_def)
    moreover from this have \<open>Option.bind (Some x) (focus_raw_view f')
       = Option.bind (focus_raw_view (\<integral>'\<^sub>p p) (prism_embed p x)) (focus_raw_view f')\<close> 
      by (simp add: prism_to_focus_raw_def)
    moreover from this and \<open>f = \<integral>'\<^sub>p p \<diamondop>' f'\<close> have \<open>... =  focus_raw_view f (prism_embed p x)\<close> 
      by (simp add: focus_raw_compose_def make_focus_raw_via_view_modify_def)
    ultimately show \<open>focus_raw_view f' x = ?f'_view x\<close>
      by (metis bind.bind_lunit)
  qed
  from this have \<open>focus_raw_view f' = focus_raw_view ?f''\<close> 
    by (clarsimp simp add: factor_focus_through_prism_def intro!:ext)
  note A = this
  let ?f'_update = \<open>\<lambda>(y :: 't) (w :: 'w). the (prism_project p (focus_raw_update f y (prism_embed p w)))\<close>
  have \<open>\<And>x y. focus_raw_update f' y x = ?f'_update y x\<close>
  proof -
    fix x y
    have \<open>Some (focus_raw_update f' y x) = focus_raw_view (\<integral>'\<^sub>p p) (prism_embed p (focus_raw_update f' y x))\<close>  
      using assms by (clarsimp simp add: prism_to_focus_raw_def is_valid_prism_def)
    moreover have \<open>... = focus_raw_view (\<integral>'\<^sub>p p) (focus_raw_modify (\<integral>'\<^sub>p p) (focus_raw_update f' y) (prism_embed p x))\<close> 
      using \<open>is_valid_prism p\<close> by (clarsimp simp add: is_valid_prism_def prism_to_focus_raw_def
        assms(2) focus_raw_modify_def prism_domI')
    moreover have \<open>... = focus_raw_view (\<integral>'\<^sub>p p) (focus_raw_update f y (prism_embed p x))\<close> 
      using \<open>f = \<integral>'\<^sub>p p \<diamondop>' f'\<close> by (simp add: focus_raw_compose_def focus_raw_modify_def 
        make_focus_raw_via_view_modify_components(2))
    ultimately have \<open>Some (focus_raw_update f' y x) = prism_project p (focus_raw_update f y (prism_embed p x))\<close>
      by (simp add: prism_to_focus_raw_def)
    from this show \<open>focus_raw_update f' y x = ?f'_update y x\<close> 
      by (metis option.sel)
  qed
  from this have \<open>focus_raw_update f' = focus_raw_update ?f''\<close>
    by (clarsimp simp add: factor_focus_through_prism_def intro!: ext)
  note B = this
  from A B show ?thesis 
    by (clarsimp simp add: focus_raw.expand) 
qed

text\<open>If a valid focus factors through a valid prism, the factorization is also a valid focus:\<close>
lemma focus_raw_factors_prism_valid:
    fixes f :: \<open>('v, 't) focus_raw\<close> 
      and p :: \<open>('v, 'w) prism\<close>
      and f' :: \<open>('w, 't) focus_raw\<close>
  assumes \<open>is_valid_focus f\<close>
      and \<open>is_valid_prism p\<close>
      and \<open>f = \<integral>'\<^sub>p p \<diamondop>' f'\<close>
    shows \<open>is_valid_focus f'\<close> 
proof -
  from assms have eq: \<open>f' = factor_focus_through_prism f p\<close> 
    using focus_raw_factors_prism_unique by blast
  {
    fix x y
    have \<open>focus_raw_update f y (prism_embed p x) \<in> prism_dom p\<close>  
      by (simp add: assms focus_raw_compose_def focus_raw_modify_def make_focus_raw_via_view_modify_def 
        prism_domI' prism_to_focus_raw_def)
    from this have eq': \<open>map_option (prism_embed p) (prism_project p (focus_raw_update f y (prism_embed p x))) =
              Some (focus_raw_update f y (prism_embed p x))\<close>
      by (metis (no_types, opaque_lifting) assms(2) is_valid_prism_def option.simps(9) prism_domE')
    have \<open>focus_raw_view f' (focus_raw_update f' y x) = Option.bind (Some (focus_raw_update f' y x)) (focus_raw_view f')\<close> 
      by simp
    also have \<open>\<dots> = Option.bind (prism_project p (focus_raw_update f y (prism_embed p x))) (focus_raw_view f')\<close> 
      using eq' by (clarsimp simp add: eq factor_focus_through_prism_def)
    also have \<open>... = Option.bind (prism_project p (focus_raw_update f y (prism_embed p x)))
                           (focus_raw_view f \<circ> prism_embed p)\<close>  
      by (metis comp_apply eq factor_focus_through_prism_def focus_raw.sel(1))
    also have \<open>... = Option.bind (map_option (prism_embed p) (prism_project p (focus_raw_update f y (prism_embed p x))))
                                 (focus_raw_view f)\<close> 
      by (simp add: bind_map_option)
    also from eq' have \<open>... = Option.bind (Some (focus_raw_update f y (prism_embed p x))) (focus_raw_view f)\<close> 
      by force
    also have \<open>... = focus_raw_view f (focus_raw_update f y (prism_embed p x))\<close> 
      by simp
    also have \<open>... = map_option (\<lambda>_. y) (focus_raw_view f (prism_embed p x))\<close>
      using assms(1) by (metis focus_raw_modify_def is_valid_focus_via_modifyE)
    finally have \<open>focus_raw_view f' (focus_raw_update f' y x) = map_option (\<lambda>_. y) (focus_raw_view f' x)\<close> 
      by (simp add: eq factor_focus_through_prism_def)
  }
  note A = this
  { 
    fix y x
    assume \<open>map_option (\<lambda>_. y) (focus_raw_view f' x) = focus_raw_view f' x\<close>
    then have \<open>map_option (\<lambda>_. y) (focus_raw_view f (prism_embed p x)) = focus_raw_view f (prism_embed p x)\<close>
      using \<open>is_valid_prism p\<close> by (clarsimp simp add: \<open>f = \<integral>'\<^sub>p p \<diamondop>' f'\<close> focus_raw_compose_def 
        prism_to_focus_raw_def is_valid_prism_def make_focus_raw_via_view_modify_def) 
    from this have \<open>focus_raw_update f y (prism_embed p x) = prism_embed p x\<close>
      using \<open>is_valid_focus f\<close> is_valid_focus_def by (metis focus_raw_modify_def is_valid_focus_via_modify(2))
    from this have \<open>Some (focus_raw_update f' y x) = Some x\<close> 
      using \<open>is_valid_prism p\<close> 
      by (clarsimp simp add: is_valid_prism_def  eq factor_focus_through_prism_def)
    from this have \<open>focus_raw_update f' y x = x\<close>  
      by simp
  }
  note B = this
  { fix x y y'
    have \<open>Some (focus_raw_update f' y (focus_raw_update f' y' x)) = 
              prism_project p (focus_raw_update f y (prism_embed p (focus_raw_update f' y' x)))\<close>  
      by (metis assms eq focus_raw_dom_compose focus_raw_factors_prism_update(1) prism_to_focus_raw_dom)
    also have \<open>... = prism_project p (focus_raw_update f y (focus_raw_update f y' (prism_embed p x)))\<close> 
      using assms eq focus_raw_dom_compose focus_raw_factors_prism_update(2) by fastforce
    also have \<open>... = prism_project p (focus_raw_update f y (prism_embed p x))\<close> 
      by (metis assms(1) is_valid_focusE not_Some_eq)
    also have \<open>... = Some (focus_raw_update f' y x)\<close>
      by (metis assms eq focus_raw_dom_compose focus_raw_factors_prism_update(1) prism_to_focus_raw_dom)
    finally have \<open>focus_raw_update f' y (focus_raw_update f' y' x) = focus_raw_update f' y x\<close> 
      by force
  }  
  note C = this
  from A B C show ?thesis
    by (intro is_valid_focusI; clarsimp)
qed

lemma focus_raw_factors_prism_valid':
  assumes \<open>is_valid_prism p\<close>
      and \<open>is_valid_focus (\<integral>'\<^sub>p p \<diamondop>' f)\<close>
    shows \<open>is_valid_focus f\<close>
using assms focus_raw_factors_prism_valid by blast
  
text\<open>One can form the product of foci:\<close>
definition pair_option :: \<open>'a option \<times> 'b option \<Rightarrow> ('a \<times> 'b) option\<close> where
  \<open>pair_option t \<equiv> case t of (Some x, Some y) \<Rightarrow> Some (x,y) | _ \<Rightarrow> None\<close>

definition product_focus_raw :: \<open>('a, 'b) focus_raw \<Rightarrow> ('c, 'd) focus_raw \<Rightarrow>
      ('a \<times> 'c, 'b \<times> 'd) focus_raw\<close> where
  \<open>product_focus_raw f0 f1 \<equiv> 
     let view   = \<lambda>(x0,x1). pair_option (focus_raw_view f0 x0, focus_raw_view f1 x1);
         update = \<lambda>(y0,y1) (x0,x1). 
        \<comment> \<open>There's a pitfall here: we can't just update component-wise, because the axioms force
            us to do nothing in case the view is \<^verbatim>\<open>None\<close>.\<close>
        case view (x0,x1) of None \<Rightarrow> (x0,x1)
           | _ \<Rightarrow> (focus_raw_update f0 y0 x0, focus_raw_update f1 y1 x1)
      in make_focus_raw view update\<close>

lemma product_focus_raw_valid:
  assumes \<open>is_valid_focus f0\<close>
      and  \<open>is_valid_focus f1\<close>
    shows  \<open>is_valid_focus (product_focus_raw f0 f1)\<close>
using assms by (auto intro!: is_valid_focusI elim!: is_valid_focusE simp add: pair_option_def
  product_focus_raw_def Let_def   split!: option.splits)

subsection\<open>Type of valid foci\<close>

subsubsection\<open>Definition\<close>

typedef (overloaded) ('a, 'b) focus = \<open>{ l :: ('a, 'b) focus_raw . is_valid_focus l }\<close>
  by (rule_tac x=\<open>dummy_focus\<close> in exI; clarsimp simp add: dummy_focus_is_valid)

setup_lifting type_definition_focus

instantiation focus :: (type,type)equal
begin

definition equal_focus :: \<open>('a, 'b) focus \<Rightarrow> ('a, 'b) focus \<Rightarrow> bool\<close> where
  \<open>equal_focus f g \<equiv> f = g\<close>

instance
proof
  fix x y :: \<open>('a, 'b) focus\<close>
  show \<open>equal_class.equal x y \<longleftrightarrow> (x = y)\<close>
    by (auto simp add: equal_focus_def)
qed

end

lift_definition focus_view   :: \<open>('a, 'b) focus \<Rightarrow> 'a \<Rightarrow> 'b option\<close> is \<open>focus_raw_view\<close> .
lift_definition focus_update :: \<open>('a, 'b) focus \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'a\<close> is \<open>focus_raw_update\<close> .
lift_definition focus_modify :: \<open>('a, 'b) focus \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a\<close> is \<open>focus_raw_modify\<close> .
lift_definition focus_dom    :: \<open>('a, 'b) focus \<Rightarrow> 'a set\<close> is \<open>focus_raw_dom\<close> .

abbreviation focus_is_view :: \<open>('s, 'a) focus \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>focus_is_view f s a \<equiv> focus_view f s = Some a\<close>

notation focus_is_view ("\<down>{_} _ \<doteq> _" [0,1000,59]59)
notation focus_update ("\<up>{_/ \<doteq>/ _}" [59,59]59)
notation focus_modify ("\<nabla>{_}" [0]1000)

lemma focus_modify_def':
  shows \<open>focus_modify l f s \<equiv> focus_update l (f (the (focus_view l s))) s\<close>
by (simp add: focus_modify.rep_eq focus_raw_modify_def focus_update.rep_eq focus_view.rep_eq)

lemma focus_laws_modify:
  shows \<open>\<And>f s. focus_view l (focus_modify l f s) = map_option f (focus_view l s)\<close>
    and \<open>\<And>f s. map_option f (focus_view l s) = focus_view l s \<Longrightarrow> focus_modify l f s = s\<close>
    and \<open>\<And>f g s. focus_modify l f (focus_modify l g s) = focus_modify l (\<lambda>x. f (g x)) s\<close>
by (transfer; elim is_valid_focus_via_modifyE; clarsimp)+

lemma focus_laws_update:
  shows \<open>(\<And>x y0 y1. focus_view l x = Some y0 \<Longrightarrow> focus_view l (focus_update l y1 x) = Some y1)\<close>
    and \<open>\<And>x y. focus_view l x = None  \<longrightarrow> focus_view l (focus_update l y x) = None\<close>
    and \<open>\<And>x y. focus_view l x = Some y \<Longrightarrow> focus_update l y x = x\<close>
    and \<open>\<And>x y. focus_view l x = None \<Longrightarrow> focus_update l y x = x\<close>
    and \<open>\<And>x y0 y1 y2. focus_view l x = Some y0 \<Longrightarrow>
            focus_update l y2 (focus_update l y1 x) = focus_update l y2 x\<close>
by (transfer; elim is_valid_focusE; simp)+

lemmas focus_laws = focus_laws_update focus_laws_modify

lift_definition focus_compose:: \<open>('a, 'b) focus \<Rightarrow> ('b, 'c) focus \<Rightarrow> ('a, 'c) focus\<close> (infixr "\<diamondop>" 59)
  is \<open>\<lambda>(f0 :: ('a, 'b) focus_raw) (f1 :: ('b, 'c) focus_raw). focus_raw_compose f0 f1\<close>
by (simp add: focus_raw_compose_valid)

lemma focus_compose_components:
  shows \<open>focus_view (f0 \<diamondop> f1) x = Option.bind (focus_view f0 x) (focus_view f1)\<close>
    and [focus_components]: \<open>focus_modify (f0 \<diamondop> f1) f = focus_modify f0 (focus_modify f1 f)\<close>
    and [focus_components]: \<open>focus_update (f0 \<diamondop> f1) y = focus_modify f0 (focus_modify f1 (\<lambda>_. y))\<close>
by (transfer; simp add: focus_raw_compose_components)+

lift_definition product_focus :: \<open>('a, 'b) focus \<Rightarrow> ('c, 'd) focus \<Rightarrow> ('a \<times> 'c, 'b \<times> 'd) focus\<close> (infixr "\<times>\<^sub>\<integral>" 49)
  is \<open>product_focus_raw\<close>
by (simp add: product_focus_raw_valid)

lemma product_focus_components[focus_components]:
  shows \<open>focus_view (f0 \<times>\<^sub>\<integral> f1) (x0, x1) = pair_option (focus_view f0 x0, focus_view f1 x1)\<close>
    and \<open>focus_update (f0 \<times>\<^sub>\<integral> f1) (y0, y1) (x0, x1) =
        (case focus_view (f0 \<times>\<^sub>\<integral> f1) (x0, x1) of None \<Rightarrow> (x0,x1)
           | _ \<Rightarrow> (focus_update f0 y0 x0, focus_update f1 y1 x1))\<close>
by (transfer; clarsimp simp add: product_focus_raw_def)+

lemma focus_compose_assoc[focus_simps]:
  shows \<open>f0 \<diamondop> (f1 \<diamondop> f2) = (f0 \<diamondop> f1) \<diamondop> f2\<close>
by (transfer; simp add: focus_raw_compose_assoc)

lemma lens_to_focus_raw_components':
  assumes \<open>is_valid_lens l\<close>
    shows \<open>focus_view (Abs_focus (lens_to_focus_raw l)) x = Some (lens_view l x)\<close>
      and \<open>focus_update (Abs_focus (lens_to_focus_raw l)) = lens_update l\<close>
      and \<open>focus_modify (Abs_focus (lens_to_focus_raw l)) f v = lens_modify l f v\<close>
using assms by (auto simp add: eq_onp_same_args focus_view.abs_eq lens_to_focus_raw_components
  Abs_focus_inverse lens_to_focus_raw_valid focus_update.rep_eq focus_modify.abs_eq)

lemma prism_to_focus_components':
  assumes \<open>is_valid_prism p\<close>
    shows \<open>focus_view (Abs_focus (prism_to_focus_raw p)) = prism_project p\<close>
      and \<open>focus_update (Abs_focus (prism_to_focus_raw p)) y x = 
              (if x \<in> prism_dom p then prism_embed p y else x)\<close>
      and \<open>focus_modify (Abs_focus (prism_to_focus_raw p)) f x =
              (if x \<in> prism_dom p then prism_embed p (f (the (prism_project p x))) else x)\<close>
using assms by (auto simp add: eq_onp_same_args focus_view.abs_eq prism_to_focus_raw_components
  prism_to_focus_raw_valid Abs_focus_inverse focus_update.rep_eq focus_modify.abs_eq
  prism_dom_def domIff)

context
    fixes l :: \<open>('a, 'b) lens\<close>
  assumes \<open>is_valid_lens l\<close>
begin

lift_definition lens_to_focus :: \<open>('a, 'b) focus\<close> is \<open>lens_to_focus_raw l\<close> 
by (simp add: \<open>is_valid_lens l\<close> lens_to_focus_raw_valid)

lemma lens_to_focus_components:
  shows \<open>focus_view lens_to_focus = Some \<circ> lens_view l\<close>
    and \<open>focus_update (lens_to_focus) = lens_update l\<close>
    and \<open>focus_modify (lens_to_focus) = lens_modify l\<close>
by (auto intro!: ext simp add: \<open>is_valid_lens l\<close> lens_to_focus.abs_eq lens_to_focus_raw_components')

end

context
    fixes p :: \<open>('a, 'b) prism\<close>
  assumes \<open>is_valid_prism p\<close>
begin

lift_definition prism_to_focus :: \<open>('a, 'b) focus\<close> is \<open>prism_to_focus_raw p\<close> 
by (simp add: \<open>is_valid_prism p\<close> prism_to_focus_raw_valid)

lemma prism_to_focus_components:
  shows [focus_components]: \<open>focus_view prism_to_focus = prism_project p\<close>
    and \<open>focus_update prism_to_focus y x = 
            (if x \<in> prism_dom p then prism_embed p y else x)\<close>
    and \<open>focus_modify prism_to_focus f x =
            (if x \<in> prism_dom p then prism_embed p (f (the (prism_project p x))) else x)\<close>
by (auto intro!: ext simp add: \<open>is_valid_prism p\<close> prism_to_focus.abs_eq prism_to_focus_components')

lemma prism_to_focus_dom[focus_components]:
  shows \<open>focus_dom prism_to_focus = prism_dom p\<close>
by transfer (auto simp add: focus_raw_dom_def prism_dom_def prism_to_focus_raw_components)

end

notation lens_to_focus ("\<integral>\<^sub>l")
notation prism_to_focus ("\<integral>\<^sub>p")

text\<open>The following definition intuitively captures that the given focus factors through the
(focus of the) prism associated to the given subset.\<close>
abbreviation focus_factors :: \<open>('v set) \<Rightarrow> ('v, 'w) focus \<Rightarrow> bool\<close> where
  \<open>focus_factors P f \<equiv> focus_dom f \<subseteq> P\<close>

lemma focus_factors_modify:
  assumes \<open>focus_factors P f\<close>
    shows \<open>\<And>v g. v \<in> P \<Longrightarrow> focus_modify f g v \<in> P\<close> 
using assms by transfer (metis focus_raw_domI focus_raw_modify_def in_mono is_valid_focus_def
  option.collapse)

lemma focus_factors_trans[focus_intros]:
  assumes \<open>focus_factors P f\<close>
    shows \<open>focus_factors P (f \<diamondop> g)\<close> 
using assms by transfer (meson dual_order.trans focus_raw_dom_compose)

subsubsection\<open>Examples\<close>

text\<open>The identity focus:\<close>
lift_definition focus_id :: \<open>('v, 'v) focus\<close> ("id\<^sub>\<integral>") is \<open>make_focus_raw Some (\<lambda>y _. y)\<close> 
by (metis unit_focus_raw_def unit_focus_raw_valid)

lemma focus_id_components[focus_components]:
  shows \<open>focus_view focus_id = Some\<close>
    and \<open>focus_update focus_id y x = y\<close>
by (transfer, clarsimp)+

text\<open>The point/zero focus\<close>
lift_definition focus_zero :: \<open>('v, unit) focus\<close> ("0\<^sub>\<integral>")
  is \<open>make_focus_raw (\<lambda>_. Some ()) (\<lambda>_. id)\<close>
by (simp add: is_valid_focusI)

lemma focus_zero_components[focus_components]:
  shows \<open>focus_view focus_zero = (\<lambda>_. Some ())\<close>
    and \<open>focus_update focus_zero y = id\<close> 
by (transfer, clarsimp)+

text\<open>Projection foci\<close>

lift_definition focus_fst :: \<open>('a \<times> 'b, 'a) focus\<close> ("fst\<^sub>\<integral>") is \<open>\<integral>'\<^sub>l lens_fst\<close> 
  by (simp add: lens_fst_is_valid_lensI lens_to_focus_raw_valid)
lift_definition focus_snd :: \<open>('a \<times> 'b, 'b) focus\<close> ("snd\<^sub>\<integral>") is \<open>\<integral>'\<^sub>l lens_snd\<close> 
  by (simp add: lens_snd_is_valid_lensI lens_to_focus_raw_valid)

text\<open>Use eta expansion during code generation to avoid ML value restriction\<close>
definition \<open>focus_fst_lazy (uu :: unit) = focus_fst\<close>
declare focus_fst_lazy_def[of \<open>()\<close>, symmetric, code_unfold]
declare focus_fst_lazy_def[THEN  arg_cong[where f="Rep_focus"], simplified focus_fst.rep_eq, code]

definition \<open>focus_snd_lazy (uu :: unit) = focus_snd\<close>
declare focus_snd_lazy_def[of \<open>()\<close>, symmetric, code_unfold]
declare focus_snd_lazy_def[THEN  arg_cong[where f="Rep_focus"], simplified focus_snd.rep_eq, code]

lemma focus_fst_snd_components[focus_components]:
  shows \<open>focus_view focus_fst (x,y) = Some x\<close>
    and \<open>focus_view focus_snd (x,y) = Some y\<close>
    and \<open>focus_update focus_fst x (x0,y0) = (x,y0)\<close>
    and \<open>focus_update focus_snd y (x0,y0) = (x0,y)\<close>
by (transfer; clarsimp simp add: lens_to_focus_raw_components;
    clarsimp simp add: lens_fst_def lens_snd_def)+

lift_definition option_focus :: \<open>('v option, 'v) focus\<close>
  is \<open>make_focus_raw (\<lambda>x. x) (\<lambda>y x. Option.bind x (\<lambda>_. Some y))\<close>
by (auto simp add: option.map_comp Fun.comp_def is_valid_focus_def focus_raw_update_def)

lemma option_focus_components[focus_components]:
  shows \<open>focus_view option_focus = id\<close>
    and \<open>focus_update option_focus y x = Option.bind x (\<lambda>_. Some y)\<close>
by (transfer, auto)+

lemma focus_view_modify:
  shows \<open>focus_view l (focus_modify l f s) = map_option f (focus_view l s)\<close>
by (auto simp add: focus_laws)

lemma focus_view_update:
  shows \<open>focus_view l (focus_update l y s) = map_option (\<lambda>_. y) (focus_view l s)\<close>
by (metis focus_laws_modify(1) focus_modify_def')

subsection\<open>Automation setup\<close>

text\<open>In this section, we single out specific formulations of the focus laws which are suitable
for proof automation, marking them as \<^verbatim>\<open>focus_simps\<close> or \<^verbatim>\<open>focus_intros\<close> as appropriate:\<close>

lemma focus_modify_compose [focus_simps]:
  shows \<open>focus_modify l f (focus_modify l g s) = focus_modify l (\<lambda>x. f (g x)) s\<close>
by (auto simp add: focus_laws)

lemma focus_modify_localI[focus_intros]:
  assumes \<open>focus_is_view l s t\<close>
      and \<open>f t = g t\<close>
    shows \<open>focus_modify l f s = focus_modify l g s\<close>
using assms by (simp add: focus_modify_def')

text \<open>Modifying a valid focus with a degenerate update function, which merely returns the contents
of the field, has no effect:\<close>
lemma focus_modify_selfI [focus_intros]:
  assumes \<open>focus_is_view f g v\<close>
    shows \<open>focus_modify f (\<lambda>_. v) g = g\<close>
by (simp add: assms focus_laws_modify)

lemma focus_update_selfI [focus_intros]:
  assumes \<open>focus_is_view f g v\<close>
    shows \<open>focus_update f v g = g\<close>
by (simp add: assms focus_laws_update)

lemma focus_update_selfI':
  assumes \<open>focus_is_view f g v\<close>
      and \<open>v = v'\<close>
    shows \<open>focus_update f v' g = g\<close>
by (simp add: assms focus_laws_update)

declare focus_update_selfI'[focus_intros]
declare focus_update_selfI'[symmetric, focus_intros]

lemma focus_modify_selfI':
  assumes \<open>focus_is_view l s t\<close>
      and \<open>f t = t\<close>
    shows \<open>focus_modify l f s = s\<close>
by (simp add: assms focus_laws_modify)

declare focus_modify_selfI'[focus_intros]
declare focus_modify_selfI'[symmetric, focus_intros]

text\<open>The following two versions of \<^verbatim>\<open>focus_raw_view_modify\<close> would work for weaker focus axioms 
not predescribing any behavior of \<^verbatim>\<open>focus_raw_modify l f\<close> on elements outside of the domain of the
focus:\<close>
lemma focus_view_modify':
  assumes \<open>focus_is_view l s t\<close>
    shows \<open>focus_is_view l (focus_modify l f s) (f t)\<close>
using assms by (simp add: focus_view_modify)

lemma focus_raw_view_modify'I[focus_rules]:
  assumes \<open>focus_is_view l s t\<close>
      and \<open>t' = f t\<close>
    shows \<open>focus_is_view l (focus_modify l f s) t'\<close>
using assms by (simp add: focus_view_modify)

lemma focus_raw_view_update'I[focus_rules]:
  assumes \<open>focus_is_view l s t\<close>
      and \<open>t' = y\<close>
    shows \<open>focus_is_view l (focus_update l y s) t'\<close>
using assms by (simp add: focus_laws_update)

lemma focus_compose_is_viewI[focus_intros]:
  assumes \<open>focus_is_view f0 x y\<close>
      and \<open>focus_is_view f1 y z\<close>
    shows \<open>focus_is_view (f0 \<diamondop> f1) x z\<close>
using assms by transfer (simp add: focus_raw_compose_components)

lemma focus_is_view_modify_partial[focus_intros]:
  assumes \<open>focus_is_view f0 x y'\<close>
      and \<open>f0 = f0'\<close>
      and \<open>y = focus_modify f1 op y'\<close>
    shows \<open>focus_is_view f0 (focus_modify (f0' \<diamondop> f1) op x) y\<close>
using assms by transfer (simp add: focus_raw_compose_components(2) focus_raw_laws_update(1)
  focus_raw_modify_def)

lemma focus_compose_view_dropE[focus_elims]:
  assumes \<open>focus_is_view (f0 \<diamondop> f1) (focus_modify f2 op x) y\<close>
      and \<open>R\<close>
    shows \<open>R\<close>
using assms by simp

lemma focus_is_view_elim[focus_elims2]:
  assumes \<open>focus_is_view l (focus_modify l op x) y\<close>
      and \<open>focus_is_view l x y'\<close>
      and \<open>y = op y' \<Longrightarrow> R\<close>
    shows R
using assms by (metis focus_laws_update(2) focus_modify_def' focus_raw_view_modify'I option.collapse
  option.simps(1))

text\<open>This should be added to \<^verbatim>\<open>focus_intros\<close> after specialization for a particular prism:\<close>
lemma prism_to_focus_modify_update:
  assumes \<open>is_valid_prism p\<close>
      and \<open>prism_project p x = Some y\<close>
    shows \<open>focus_update (prism_to_focus p) y x = prism_embed p y\<close>
      and \<open>focus_modify (prism_to_focus p) f x = prism_embed p (f y)\<close>
using assms by (auto simp add: prism_to_focus_components prism_dom_def)

(*<*)
end
(*>*)
