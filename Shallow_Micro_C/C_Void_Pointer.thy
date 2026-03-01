theory C_Void_Pointer
  imports
    "Lenses_And_Other_Optics.Focused_Types"
    "Lenses_And_Other_Optics.Prism"
    "Shallow_Micro_Rust.Global_Store"
begin

section \<open>Abstract Void Pointer Operations\<close>

text \<open>
  A void pointer in C is an untyped reference --- the raw @{typ \<open>('addr, 'gv) gref\<close>} without
  any focus prism. These operations convert between typed references
  @{typ \<open>('addr, 'gv, 'v) Global_Store.ref\<close>} and raw grefs, corresponding to C's
  @{verbatim \<open>void*\<close>} casts.

  These are pure value-level operations (no monadic effects, no state). They work at the
  abstract level for any @{typ 'gv}.
\<close>

subsection \<open>Cast definitions\<close>

text \<open>Cast a typed pointer to void pointer: strip the focus.\<close>
definition c_cast_to_void :: \<open>('addr, 'gv, 'v) Global_Store.ref \<Rightarrow> ('addr, 'gv) gref\<close> where
  \<open>c_cast_to_void ref \<equiv> unwrap_focused ref\<close>

text \<open>Cast a void pointer to a typed pointer: attach a focus via a prism.\<close>
definition c_cast_from_void :: \<open>('gv, 'v) prism \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> ('addr, 'gv, 'v) Global_Store.ref\<close> where
  \<open>c_cast_from_void p gref \<equiv> make_focused gref (prism_to_focus p)\<close>

subsection \<open>Cast roundtrip lemmas\<close>

lemma cast_to_void_from_void [simp]:
  shows \<open>c_cast_to_void (c_cast_from_void p gref) = gref\<close>
  by (simp add: c_cast_to_void_def c_cast_from_void_def)

lemma cast_from_void_roundtrip:
  shows \<open>c_cast_from_void p (c_cast_to_void (c_cast_from_void p gref)) = c_cast_from_void p gref\<close>
  by simp

lemma unwrap_cast_from_void [simp]:
  shows \<open>unwrap_focused (c_cast_from_void p gref) = gref\<close>
  by (simp add: c_cast_from_void_def)

lemma get_focus_cast_from_void [simp]:
  shows \<open>get_focus (c_cast_from_void p gref) = prism_to_focus p\<close>
  by (simp add: c_cast_from_void_def)

subsection \<open>Adhoc-overloaded prism selector for ML translation\<close>

text \<open>
  The ML translation generates @{text \<open>c_cast_from_void c_void_cast_prism_for gref\<close>} with a
  type annotation on @{text c_void_cast_prism_for} that lets Isabelle's adhoc overloading
  resolve it to the locale's concrete prism parameter. Each verification locale registers
  its prisms via @{text \<open>adhoc_overloading c_void_cast_prism_for \<rightleftharpoons> my_prism\<close>}.
\<close>

consts c_void_cast_prism_for :: \<open>('gv, 'v) prism\<close>

end