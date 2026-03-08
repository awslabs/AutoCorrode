theory C_Void_Pointer_Examples
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
    "Shallow_Micro_C.C_Arithmetic_Rules"
    "Micro_Rust_Std_Lib.StdLib_All"
begin

section \<open>Verification Locale with Void Pointer Support\<close>

text \<open>
  This locale extends the basic reference infrastructure with multiple type prisms
  and void pointer cast support. Each type prism is registered via adhoc overloading
  on @{const c_void_cast_prism_for}, allowing the ML translation to resolve
  @{verbatim "(T*)void_ptr"} casts by type annotation.
\<close>

locale c_void_verification_ctx =
    reference reference_types +
    ref_c_int: reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism +
    ref_c_uint: reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> c_abort \<Rightarrow> 'i prompt \<Rightarrow>
      'o prompt_output \<Rightarrow> unit\<close>
  and c_int_prism :: \<open>('gv, c_int) prism\<close>
  and c_uint_prism :: \<open>('gv, c_uint) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

text \<open>Register prisms for void pointer cast resolution.\<close>
adhoc_overloading c_void_cast_prism_for \<rightleftharpoons> c_int_prism
adhoc_overloading c_void_cast_prism_for \<rightleftharpoons> c_uint_prism

section \<open>Void Pointer Read Example\<close>

text \<open>
  Corresponds to:
  @{verbatim \<open>int read_via_void(void *p) { return *(int *)p; }\<close>}
\<close>

definition c_read_via_void ::
  \<open>('addr, 'gv) gref \<Rightarrow>
   ('s, c_int, c_abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>c_read_via_void p \<equiv> FunctionBody
     (bind (literal (c_cast_from_void c_int_prism p))
       (deep_compose1 call dereference_fun))\<close>

definition c_read_via_void_contract ::
  \<open>('addr, 'gv) gref \<Rightarrow> 'gv \<Rightarrow> c_int \<Rightarrow>
   ('s, c_int, c_abort) function_contract\<close> where
  \<open>c_read_via_void_contract p g v \<equiv>
    let typed_p = c_cast_from_void c_int_prism p;
        pre     = typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>v;
        post    = \<lambda>r. typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>r = v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_via_void_contract

lemma c_read_via_void_spec:
  shows \<open>\<Gamma>; c_read_via_void p \<Turnstile>\<^sub>F c_read_via_void_contract p g v\<close>
by (crush_boot f: c_read_via_void_def contract: c_read_via_void_contract_def)
  (crush_base simp add: c_cast_from_void_def)

section \<open>Void Pointer Write Example\<close>

text \<open>
  Corresponds to:
  @{verbatim \<open>void write_via_void(void *p, unsigned int val) { *(unsigned int *)p = val; }\<close>}
\<close>

definition c_write_via_void ::
  \<open>('addr, 'gv) gref \<Rightarrow> c_uint \<Rightarrow>
   ('s, unit, c_abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>c_write_via_void p v \<equiv> FunctionBody
     (bind (literal (c_cast_from_void c_uint_prism p))
       (\<lambda>up. call (update_fun up v)))\<close>

definition c_write_via_void_contract ::
  \<open>('addr, 'gv) gref \<Rightarrow> 'gv \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow>
   ('s, unit, c_abort) function_contract\<close> where
  \<open>c_write_via_void_contract p g old_v new_v \<equiv>
    let typed_p = c_cast_from_void c_uint_prism p;
        pre     = typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>old_v;
        post    = \<lambda>_. typed_p \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. new_v) \<sqdot> (g\<down>old_v)
     in make_function_contract pre post\<close>
ucincl_auto c_write_via_void_contract

lemma c_write_via_void_spec:
  shows \<open>\<Gamma>; c_write_via_void p val \<Turnstile>\<^sub>F c_write_via_void_contract p g old_v val\<close>
by (crush_boot f: c_write_via_void_def contract: c_write_via_void_contract_def)
  (crush_base simp add: c_cast_from_void_def)

section \<open>End-to-End Translated Void Pointer Example\<close>

text \<open>
  This example demonstrates the full pipeline: C source with @{verbatim \<open>void*\<close>} parameter
  and cast, translated via @{command micro_c_translate}, then verified.

  Corresponds to:
  @{verbatim \<open>int read_via_void_e2e(void *p) { return *(int *)p; }\<close>}
\<close>

micro_c_translate \<open>
  int read_via_void_e2e(void *p) {
    return *(int *)p;
  }
\<close>

definition c_read_via_void_e2e_contract ::
  \<open>('addr, 'gv) gref \<Rightarrow> 'gv \<Rightarrow> c_int \<Rightarrow>
   ('s, c_int, c_abort) function_contract\<close> where
  \<open>c_read_via_void_e2e_contract p g v \<equiv>
    let typed_p = c_cast_from_void c_int_prism p;
        pre     = typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>v;
        post    = \<lambda>r. typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>r = v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_via_void_e2e_contract

lemma c_read_via_void_e2e_spec:
  shows \<open>\<Gamma>; c_read_via_void_e2e p \<Turnstile>\<^sub>F c_read_via_void_e2e_contract p g v\<close>
by (crush_boot f: c_read_via_void_e2e_def contract: c_read_via_void_e2e_contract_def)
  (crush_base simp add: c_cast_from_void_def)

section \<open>Cast Roundtrip Properties\<close>

lemma void_cast_roundtrip_points_to:
    fixes ref :: \<open>('addr, 'gv, c_int) Global_Store.ref\<close>
  assumes \<open>get_focus ref = prism_to_focus c_int_prism\<close>
    shows \<open>c_cast_from_void c_int_prism (c_cast_to_void ref) = ref\<close>
using assms[symmetric] by (simp add: c_cast_from_void_def c_cast_to_void_def focus_simps)

end

end