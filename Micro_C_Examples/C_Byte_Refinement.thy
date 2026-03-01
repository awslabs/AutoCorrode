theory C_Byte_Refinement
  imports
    C_Void_Pointer_Examples
begin

section \<open>Byte-Level Refinement for C Operations\<close>

text \<open>
  This theory establishes the byte-level refinement: the abstract void pointer
  operations from @{theory Shallow_Micro_C.C_Void_Pointer} can be instantiated
  with @{typ \<open>byte list\<close>} as the global value type, using concrete byte
  encoding prisms.

  We define a @{text byte_backed_reference} locale that specializes the
  @{locale reference} locale to @{text \<open>'gv = byte list\<close>}. Inside this locale,
  the byte encoding prisms can be used directly to focus on typed C values
  within raw byte arrays.

  The key instantiation is physical memory, where @{text reference_sublocale}
  establishes the @{locale reference} axioms for byte-backed memory regions.
  Physical memory does not support allocation, so this refinement covers
  pointer-parameter-only functions (no local variables).
\<close>

subsection \<open>Byte Encoding Prisms (inline from C\_Byte\_Encoding)\<close>

text \<open>
  We define the signed/unsigned iso prism and compose it with the existing
  word-to-byte-list prisms to get C-type byte encoding prisms.
  These are the same definitions as in @{text C_Byte_Encoding} but inlined
  here to avoid a dependency on a theory whose processing may be slow.
\<close>

definition word_sword_iso_prism :: \<open>('l::len word, 'l sword) prism\<close> where
  \<open>word_sword_iso_prism \<equiv> iso_prism scast scast\<close>

lemma word_sword_iso_prism_valid:
  shows \<open>is_valid_prism word_sword_iso_prism\<close>
  by (auto intro!: iso_prism_valid simp: word_sword_iso_prism_def)

definition c_uint_byte_prism :: \<open>(byte list, c_uint) prism\<close> where
  \<open>c_uint_byte_prism \<equiv> word32_byte_list_prism_le\<close>

definition c_int_byte_prism :: \<open>(byte list, c_int) prism\<close> where
  \<open>c_int_byte_prism \<equiv> prism_compose word32_byte_list_prism_le word_sword_iso_prism\<close>

lemma c_uint_byte_prism_valid [simp]:
  shows \<open>is_valid_prism c_uint_byte_prism\<close>
  by (simp add: c_uint_byte_prism_def word_byte_array_prism_validity)

lemma c_int_byte_prism_valid [simp]:
  shows \<open>is_valid_prism c_int_byte_prism\<close>
  by (auto simp: c_int_byte_prism_def
           intro!: prism_compose_valid word_byte_array_prism_validity word_sword_iso_prism_valid)

lemma c_uint_byte_embed_length:
  shows \<open>length (prism_embed c_uint_byte_prism v) = 4\<close>
  by (simp add: c_uint_byte_prism_def word32_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word32_byte_array_iso_prism_le_def
                iso_prism_def)

lemma c_int_byte_embed_length:
  shows \<open>length (prism_embed c_int_byte_prism v) = 4\<close>
  by (simp add: c_int_byte_prism_def word32_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word32_byte_array_iso_prism_le_def
                iso_prism_def word_sword_iso_prism_def)

subsection \<open>Byte-Backed Reference Locale\<close>

locale byte_backed_reference =
  reference reference_types update_raw_fun dereference_raw_fun
    reference_raw_fun points_to_raw' gref_can_store new_gref_can_store can_alloc_reference
  for reference_types ::
    \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> byte list \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and update_raw_fun and dereference_raw_fun and reference_raw_fun
  and points_to_raw' and gref_can_store and new_gref_can_store and can_alloc_reference
begin

text \<open>
  Inside this locale, the global value type is @{typ \<open>byte list\<close>}, so the
  byte encoding prisms can focus on typed C values within raw byte arrays.
  The @{term dereference_fun} and @{term update_fun} operations (inherited
  from @{locale reference}) work through prism-based focusing to read/write
  typed C values as byte sequences.
\<close>

subsection \<open>Byte-Level Read via Void Pointer\<close>

text \<open>
  Corresponds to: @{verbatim \<open>int read_via_void(void *p) { return *(int *)p; }\<close>}

  The void pointer @{term p} is a raw reference to a byte array. Casting to
  @{typ c_int} via @{const c_cast_from_void} with @{const c_int_byte_prism}
  creates a focused reference. Dereferencing reads the bytes and decodes them
  via the prism's 4-byte little-endian interpretation.
\<close>

definition c_read_bytes_via_void ::
  \<open>('addr, byte list) gref \<Rightarrow>
   ('s, c_int, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>c_read_bytes_via_void p \<equiv> FunctionBody
     (bind (literal (c_cast_from_void c_int_byte_prism p))
       (deep_compose1 call dereference_fun))\<close>

definition c_read_bytes_via_void_contract ::
  \<open>('addr, byte list) gref \<Rightarrow> byte list \<Rightarrow> c_int \<Rightarrow>
   ('s, c_int, 'abort) function_contract\<close> where
  \<open>c_read_bytes_via_void_contract p g v \<equiv>
    let typed_p = c_cast_from_void c_int_byte_prism p;
        pre = typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>v;
        post = \<lambda>r. typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>r = v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_read_bytes_via_void_contract

lemma c_read_bytes_via_void_spec:
  shows \<open>\<Gamma>; c_read_bytes_via_void p \<Turnstile>\<^sub>F c_read_bytes_via_void_contract p g v\<close>
  by (crush_boot f: c_read_bytes_via_void_def contract: c_read_bytes_via_void_contract_def)
     (crush_base simp add: c_cast_from_void_def)

subsection \<open>Byte-Level Write via Void Pointer\<close>

text \<open>
  Corresponds to: @{verbatim \<open>void write_via_void(void *p, unsigned int val) { *(unsigned int *)p = val; }\<close>}

  The prism @{const c_uint_byte_prism} encodes a @{typ c_uint} value as 4 bytes
  (little-endian). Writing through the void pointer encodes the value and stores
  the resulting bytes.
\<close>

definition c_write_bytes_via_void ::
  \<open>('addr, byte list) gref \<Rightarrow> c_uint \<Rightarrow>
   ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>c_write_bytes_via_void p v \<equiv> FunctionBody
     (bind (literal (c_cast_from_void c_uint_byte_prism p))
       (\<lambda>up. call (update_fun up v)))\<close>

definition c_write_bytes_via_void_contract ::
  \<open>('addr, byte list) gref \<Rightarrow> byte list \<Rightarrow> c_uint \<Rightarrow> c_uint \<Rightarrow>
   ('s, unit, 'abort) function_contract\<close> where
  \<open>c_write_bytes_via_void_contract p g old_v new_v \<equiv>
    let typed_p = c_cast_from_void c_uint_byte_prism p;
        pre = typed_p \<mapsto>\<langle>\<top>\<rangle> g\<down>old_v;
        post = \<lambda>_. typed_p \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. new_v) \<sqdot> (g\<down>old_v)
     in make_function_contract pre post\<close>
ucincl_auto c_write_bytes_via_void_contract

lemma c_write_bytes_via_void_spec:
  shows \<open>\<Gamma>; c_write_bytes_via_void p val \<Turnstile>\<^sub>F c_write_bytes_via_void_contract p g old_v val\<close>
  by (crush_boot f: c_write_bytes_via_void_def contract: c_write_bytes_via_void_contract_def)
     (crush_base simp add: c_cast_from_void_def)

subsection \<open>Sizeof-Encoding Consistency\<close>

text \<open>
  The byte encoding prisms produce byte lists whose length matches C sizeof values.
\<close>

lemma byte_refinement_sizeof_consistency:
  shows \<open>c_sizeof TYPE(c_uint) = length (prism_embed c_uint_byte_prism v1)\<close>
    and \<open>c_sizeof TYPE(c_int)  = length (prism_embed c_int_byte_prism v2)\<close>
  by (simp_all add: c_uint_byte_embed_length c_int_byte_embed_length)

subsection \<open>Prism Encode-Decode Roundtrip\<close>

text \<open>
  Writing a typed value via a byte prism and reading it back yields the
  original value. This is the core soundness property of the byte refinement.
\<close>

lemma byte_prism_roundtrip_c_int:
  shows \<open>prism_project c_int_byte_prism (prism_embed c_int_byte_prism v) = Some v\<close>
  using c_int_byte_prism_valid
  by (simp add: is_valid_prism_def)

lemma byte_prism_roundtrip_c_uint:
  shows \<open>prism_project c_uint_byte_prism (prism_embed c_uint_byte_prism v) = Some v\<close>
  using c_uint_byte_prism_valid
  by (simp add: is_valid_prism_def)

subsection \<open>Relationship to Abstract Void Pointer Proofs\<close>

text \<open>
  The abstract proofs in @{locale c_void_verification_ctx} work for any valid
  @{locale reference} instance and any valid prisms. The byte-level refinement
  instantiates:
  \begin{itemize}
  \item @{text \<open>'gv\<close>} = @{typ \<open>byte list\<close>}
  \item @{term c_int_prism} = @{const c_int_byte_prism}
  \item @{term c_uint_prism} = @{const c_uint_byte_prism}
  \end{itemize}

  The concrete @{const c_read_bytes_via_void} and @{const c_write_bytes_via_void}
  defined above have the same proof structure as the abstract versions in
  @{locale c_void_verification_ctx}, confirming that the abstract proofs transfer
  to byte-backed memory.

  For a full instantiation with physical memory, the @{text reference_sublocale}
  lemma in @{text Raw_Physical_Memory_References} establishes that physical memory
  (with @{text \<open>'gv = byte list\<close>}) satisfies the @{locale reference} axioms.
  Combined with the prism validity lemmas above (@{thm c_int_byte_prism_valid}
  and @{thm c_uint_byte_prism_valid}), all conditions for the byte refinement
  are met.
\<close>

end

end
