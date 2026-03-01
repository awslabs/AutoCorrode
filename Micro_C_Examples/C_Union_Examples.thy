theory C_Union_Examples
  imports
    C_Void_Pointer_Examples
    C_Byte_Refinement
begin

context c_void_verification_ctx begin

section ‹Union Read›

text ‹
  @{verbatim ‹int read_union_int(union U *p) { return p->i; }›}
›

micro_c_translate ‹
  union U {
    int i;
    unsigned int u;
  };

  int read_union_int(union U *p) {
    return p->i;
  }
›

definition c_read_union_int_contract ::
  ‹('addr, 'gv) gref ⇒ 'gv ⇒ c_int ⇒
   ('s, c_int, 'abort) function_contract› where
  ‹c_read_union_int_contract p g v ≡
    let typed_p = c_cast_from_void c_int_prism p;
        pre     = typed_p ↦⟨⊤⟩ g↓v;
        post    = λr. typed_p ↦⟨⊤⟩ g↓v ⋆ ⟨r = v⟩
     in make_function_contract pre post›
ucincl_auto c_read_union_int_contract

lemma c_read_union_int_spec:
  shows ‹Γ; c_read_union_int p ⊨⇩F c_read_union_int_contract p g v›
by (crush_boot f: c_read_union_int_def contract: c_read_union_int_contract_def)
  (crush_base simp add: c_cast_from_void_def)

section ‹Union Write›

text ‹
  @{verbatim ‹void write_union_uint(union U *p, unsigned int val) { p->u = val; }›}
›

micro_c_translate ‹
  union U {
    int i;
    unsigned int u;
  };

  void write_union_uint(union U *p, unsigned int val) {
    p->u = val;
  }
›

definition c_write_union_uint_contract ::
  ‹('addr, 'gv) gref ⇒ 'gv ⇒ c_uint ⇒ c_uint ⇒
   ('s, unit, 'abort) function_contract› where
  ‹c_write_union_uint_contract p g old_v new_v ≡
    let typed_p = c_cast_from_void c_uint_prism p;
        pre     = typed_p ↦⟨⊤⟩ g↓old_v;
        post    = λ_. typed_p ↦⟨⊤⟩ (λ_. new_v) · (g↓old_v)
     in make_function_contract pre post›
ucincl_auto c_write_union_uint_contract

lemma c_write_union_uint_spec:
  shows ‹Γ; c_write_union_uint p val ⊨⇩F c_write_union_uint_contract p g old_v val›
by (crush_boot f: c_write_union_uint_def contract: c_write_union_uint_contract_def)
  (crush_base simp add: c_cast_from_void_def)

section ‹Union Write then Read›

text ‹
  @{verbatim ‹
    int write_read_union(union U *p, int val) {
      p->i = val;
      return p->i;
    }
  ›}
›

micro_c_translate ‹
  union U {
    int i;
    unsigned int u;
  };

  int write_read_union(union U *p, int val) {
    p->i = val;
    return p->i;
  }
›

definition c_write_read_union_contract ::
  ‹('addr, 'gv) gref ⇒ 'gv ⇒ c_int ⇒ c_int ⇒
   ('s, c_int, 'abort) function_contract› where
  ‹c_write_read_union_contract p g old_v new_v ≡
    let typed_p = c_cast_from_void c_int_prism p;
        pre     = typed_p ↦⟨⊤⟩ g↓old_v;
        post    = λr. typed_p ↦⟨⊤⟩ (λ_. new_v) · (g↓old_v) ⋆ ⟨r = new_v⟩
     in make_function_contract pre post›
ucincl_auto c_write_read_union_contract

lemma c_write_read_union_spec:
  shows ‹Γ; c_write_read_union p val ⊨⇩F c_write_read_union_contract p g old_v val›
by (crush_boot f: c_write_read_union_def contract: c_write_read_union_contract_def)
  (crush_base simp add: c_cast_from_void_def)

end

section ‹Type Punning at the Byte Level›

text ‹
  Type punning — writing through one union field and reading through another — requires
  reasoning about the byte-level encoding. We work in @{locale byte_backed_reference}
  where the global value type is @{typ ‹byte list›} and use the concrete byte encoding
  prisms @{const c_int_byte_prism} and @{const c_uint_byte_prism}.
›

context byte_backed_reference begin

adhoc_overloading store_update_const ⇌ update_fun
adhoc_overloading c_void_cast_prism_for ⇌ c_int_byte_prism
adhoc_overloading c_void_cast_prism_for ⇌ c_uint_byte_prism

text ‹Cross-prism extraction: writing as @{type c_int} and reading as @{type c_uint}
  yields the unsigned reinterpretation of the same bit pattern.›

lemma byte_prism_type_pun_int_uint:
  shows ‹prism_project c_uint_byte_prism (prism_embed c_int_byte_prism v) = Some (ucast v)›
using c_uint_byte_prism_valid[unfolded c_uint_byte_prism_def] by (simp add: c_int_byte_prism_def
  c_uint_byte_prism_def prism_compose_def word_sword_iso_prism_def iso_prism_def is_valid_prism_def
  scast_ucast_down_same)

text ‹
  @{verbatim ‹
    unsigned int type_pun(union U *p, int val) {
      p->i = val;
      return p->u;
    }
  ›}
  This is the key union use case: writing through one field and reading through another.
›

micro_c_translate ‹
  union U {
    int i;
    unsigned int u;
  };

  unsigned int type_pun(union U *p, int val) {
    p->i = val;
    return p->u;
  }
›

definition c_type_pun_contract ::
  ‹('addr, byte list) gref ⇒ byte list ⇒ c_int ⇒ c_int ⇒
   ('s, c_uint, 'abort) function_contract› where
  ‹c_type_pun_contract p g old_v new_v ≡
    let typed_p = c_cast_from_void c_int_byte_prism p;
        pre     = typed_p ↦⟨⊤⟩ g↓old_v;
        post    = λr. typed_p ↦⟨⊤⟩ (λ_. new_v) · (g↓old_v) ⋆ ⟨r = ucast new_v⟩
     in make_function_contract pre post›
ucincl_auto c_type_pun_contract

lemma c_int_uint_byte_prism_dom_eq:
  shows ‹prism_dom c_int_byte_prism = prism_dom c_uint_byte_prism›
by (auto simp: prism_dom_def c_int_byte_prism_def c_uint_byte_prism_def
  prism_compose_def word_sword_iso_prism_def iso_prism_def dom_def bind_eq_Some_conv)

lemma c_type_pun_spec:
  shows ‹Γ; c_type_pun p val ⊨⇩F c_type_pun_contract p g old_v val›
  apply (crush_boot f: c_type_pun_def contract: c_type_pun_contract_def)
  apply (crush_base simp add: c_cast_from_void_def byte_prism_type_pun_int_uint)
  apply (simp_all add: prism_to_focus_modify_update byte_prism_type_pun_int_uint
     byte_prism_roundtrip_c_int is_valid_ref_for_def prism_to_focus_dom
     c_int_uint_byte_prism_dom_eq)
  done

end

end

