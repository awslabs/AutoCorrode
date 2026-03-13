theory C_Union_Examples
  imports
    C_Void_Pointer_Examples
    C_Byte_Refinement
begin

context c_void_verification_ctx begin

(* Union Read:
   int read_union_int(union U *p) { return p->i; } *)

micro_c_translate \<open>
  union U {
    int i;
    unsigned int u;
  };

  int read_union_int(union U *p) {
    return p->i;
  }
\<close>

definition c_read_union_int_contract ::
  \<open>('addr, 'gv) gref \<Rightarrow> 'gv \<Rightarrow> c_int \<Rightarrow>
   ('s, c_int, 'abort) function_contract\<close> where
  \<open>c_read_union_int_contract p g v \<equiv>
    let typed_p = c_cast_from_void c_int_prism p;
        pre     = typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>v;
        post    = \<lambda>r. typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>r = v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_union_int_contract

lemma c_read_union_int_spec:
  shows \<open>\<Gamma>; c_read_union_int p \<Turnstile>\<^sub>F c_read_union_int_contract p g v\<close>
by (crush_boot f: c_read_union_int_def contract: c_read_union_int_contract_def)
  (crush_base simp add: c_cast_from_void_def)

(* Union Write:
   void write_union_uint(union U *p, unsigned int val) { p->u = val; } *)

micro_c_translate \<open>
  union U {
    int i;
    unsigned int u;
  };

  void write_union_uint(union U *p, unsigned int val) {
    p->u = val;
  }
\<close>

definition c_write_union_uint_contract ::
  \<open>('addr, 'gv) gref \<Rightarrow> 'gv \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow>
   ('s, unit, 'abort) function_contract\<close> where
  \<open>c_write_union_uint_contract p g old_v new_v \<equiv>
    let typed_p = c_cast_from_void c_uint_prism p;
        pre     = typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>old_v;
        post    = \<lambda>_. typed_p \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. new_v) \<sqdot> (g\<down>old_v)
     in make_function_contract pre post\<close>
ucincl_auto c_write_union_uint_contract

lemma c_write_union_uint_spec:
  shows \<open>\<Gamma>; c_write_union_uint p val \<Turnstile>\<^sub>F c_write_union_uint_contract p g old_v val\<close>
by (crush_boot f: c_write_union_uint_def contract: c_write_union_uint_contract_def)
  (crush_base simp add: c_cast_from_void_def)

(* Union Write then Read:
   int write_read_union(union U *p, int val) {
     p->i = val;
     return p->i;
   } *)

micro_c_translate \<open>
  union U {
    int i;
    unsigned int u;
  };

  int write_read_union(union U *p, int val) {
    p->i = val;
    return p->i;
  }
\<close>

definition c_write_read_union_contract ::
  \<open>('addr, 'gv) gref \<Rightarrow> 'gv \<Rightarrow> c_int \<Rightarrow> c_int \<Rightarrow>
   ('s, c_int, 'abort) function_contract\<close> where
  \<open>c_write_read_union_contract p g old_v new_v \<equiv>
    let typed_p = c_cast_from_void c_int_prism p;
        pre     = typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>old_v;
        post    = \<lambda>r. typed_p \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. new_v) \<sqdot> (g\<down>old_v) \<star> \<langle>r = new_v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_write_read_union_contract

lemma c_write_read_union_spec:
  shows \<open>\<Gamma>; c_write_read_union p val \<Turnstile>\<^sub>F c_write_read_union_contract p g old_v val\<close>
by (crush_boot f: c_write_read_union_def contract: c_write_read_union_contract_def)
  (crush_base simp add: c_cast_from_void_def)

end

section \<open>Type Punning at the Byte Level\<close>

text \<open>
  Type punning — writing through one union field and reading through another — requires
  reasoning about the byte-level encoding. We work in @{locale byte_backed_reference}
  where the global value type is @{typ \<open>byte list\<close>} and use the concrete byte encoding
  prisms @{const c_int_byte_prism} and @{const c_uint_byte_prism}.
\<close>

context byte_backed_reference begin

adhoc_overloading store_update_const \<rightleftharpoons> update_fun
adhoc_overloading c_void_cast_prism_for \<rightleftharpoons> c_int_byte_prism
adhoc_overloading c_void_cast_prism_for \<rightleftharpoons> c_uint_byte_prism

(* Cross-prism extraction: writing as c_int and reading as c_uint yields
   the unsigned reinterpretation of the same bit pattern. *)

lemma byte_prism_type_pun_int_uint:
  shows \<open>prism_project c_uint_byte_prism (prism_embed c_int_byte_prism v) = Some (ucast v)\<close>
using c_uint_byte_prism_valid[unfolded c_uint_byte_prism_def] by (simp add: c_int_byte_prism_def
  c_uint_byte_prism_def prism_compose_def word_sword_iso_prism_def iso_prism_def is_valid_prism_def
  scast_ucast_down_same)

(* unsigned int type_pun(union U *p, int val) {
     p->i = val;
     return p->u;
   }
   Key union use case: writing through one field and reading through another. *)

micro_c_translate gv: \<open>byte list\<close> abort: 'abort \<open>
  union U {
    int i;
    unsigned int u;
  };

  unsigned int type_pun(union U *p, int val) {
    p->i = val;
    return p->u;
  }
\<close>

definition c_type_pun_contract ::
  \<open>('addr, byte list) gref \<Rightarrow> byte list \<Rightarrow> c_int \<Rightarrow> c_int \<Rightarrow>
   ('s, c_uint, 'abort) function_contract\<close> where
  \<open>c_type_pun_contract p g old_v new_v \<equiv>
    let typed_p = c_cast_from_void c_int_byte_prism p;
        pre     = typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>old_v;
        post    = \<lambda>r. typed_p \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. new_v) \<sqdot> (g\<down>old_v) \<star> \<langle>r = ucast new_v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_type_pun_contract

lemma c_int_uint_byte_prism_dom_eq:
  shows \<open>prism_dom c_int_byte_prism = prism_dom c_uint_byte_prism\<close>
by (auto simp: prism_dom_def c_int_byte_prism_def c_uint_byte_prism_def
  prism_compose_def word_sword_iso_prism_def iso_prism_def dom_def bind_eq_Some_conv)

lemma c_type_pun_spec:
  shows \<open>\<Gamma>; c_type_pun p val \<Turnstile>\<^sub>F c_type_pun_contract p g old_v val\<close>
  apply (crush_boot f: c_type_pun_def contract: c_type_pun_contract_def)
  apply (crush_base simp add: c_cast_from_void_def byte_prism_type_pun_int_uint)
  apply (simp_all add: prism_to_focus_modify_update byte_prism_type_pun_int_uint
     byte_prism_roundtrip_c_int is_valid_ref_for_def prism_to_focus_dom
     c_int_uint_byte_prism_dom_eq)
  done

end

end
