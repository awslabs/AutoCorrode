theory Byte_Reinterpret_Examples
  imports
    "Micro_Rust_Std_Lib.StdLib_All"
    "Shallow_Micro_C.C_Byte_Encoding"
    "Shallow_Micro_C.C_Void_Pointer"
begin

section \<open>Byte Reinterpretation in Micro Rust\<close>

text \<open>
  This theory demonstrates byte-level type reinterpretation in Micro Rust,
  the analogue of C void pointer casts. In Rust, this corresponds to
  @{verbatim \<open>unsafe { *(buf.as_ptr() as *const T) }\<close>} --- reading a typed
  value from a raw byte buffer via pointer cast.

  The key insight: @{const c_cast_from_void} and @{const c_cast_to_void}
  are pure value-level operations that work for any @{locale reference}
  instance. They are equally valid in Rust as in C.
\<close>

subsection \<open>Verification Locale\<close>

text \<open>
  A verification context with typed prisms for @{typ \<open>64 word\<close>} and
  @{typ \<open>32 word\<close>}. The prisms control how raw global values @{typ 'gv}
  are interpreted as typed values.
\<close>

locale byte_reinterpret_ctx =
    reference reference_types +
    ref_word64: reference_allocatable reference_types _ _ _ _ _ _ _ word64_prism +
    ref_word32: reference_allocatable reference_types _ _ _ _ _ _ _ word32_prism
  for
    reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  and word64_prism :: \<open>('gv, 64 word) prism\<close>
  and word32_prism :: \<open>('gv, 32 word) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_word64.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_word32.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun
adhoc_overloading raw_ptr_cast_prism \<rightleftharpoons> word64_prism
adhoc_overloading raw_ptr_cast_prism \<rightleftharpoons> word32_prism

subsection \<open>Read via Reinterpret Cast\<close>

text \<open>
  Read a @{typ \<open>32 word\<close>} value from a raw (untyped) reference by
  reinterpreting the global value through @{term word32_prism}.

  Rust analogue:
  @{verbatim \<open>unsafe { *(buf.as_ptr() as *const u32) }\<close>}
\<close>

definition read_reinterpret ::
  \<open>('addr, 'gv) gref \<Rightarrow>
   ('s, 32 word, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>read_reinterpret buf \<equiv> FunctionBody \<lbrakk>
    *(buf as *const u32)
  \<rbrakk>\<close>

definition read_reinterpret_contract ::
  \<open>('addr, 'gv) gref \<Rightarrow> 'gv \<Rightarrow> 32 word \<Rightarrow>
   ('s, 32 word, 'abort) function_contract\<close> where
  \<open>read_reinterpret_contract buf g v \<equiv>
    let typed_buf = c_cast_from_void word32_prism buf;
        pre  = typed_buf \<mapsto>\<langle>\<top>\<rangle> g\<down>v;
        post = \<lambda>r. typed_buf \<mapsto>\<langle>\<top>\<rangle> g\<down>v \<star> \<langle>r = v\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto read_reinterpret_contract

lemma read_reinterpret_spec:
  shows \<open>\<Gamma>; read_reinterpret buf \<Turnstile>\<^sub>F read_reinterpret_contract buf g v\<close>
  by (crush_boot f: read_reinterpret_def contract: read_reinterpret_contract_def)
     (crush_base simp add: raw_ptr_cast_def c_cast_from_void_def)

subsection \<open>Write via Reinterpret Cast\<close>

text \<open>
  Write a @{typ \<open>64 word\<close>} value to a raw reference by reinterpreting
  through @{term word64_prism}.

  Rust analogue:
  @{verbatim \<open>unsafe { *(buf.as_mut_ptr() as *mut u64) = val; }\<close>}
\<close>

definition write_reinterpret ::
  \<open>('addr, 'gv) gref \<Rightarrow> 64 word \<Rightarrow>
   ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>write_reinterpret buf v \<equiv> FunctionBody \<lbrakk>
    let typed_buf = buf as *mut u64;
    typed_buf = v
  \<rbrakk>\<close>

definition write_reinterpret_contract ::
  \<open>('addr, 'gv) gref \<Rightarrow> 'gv \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow>
   ('s, unit, 'abort) function_contract\<close> where
  \<open>write_reinterpret_contract buf g old_v new_v \<equiv>
    let typed_buf = c_cast_from_void word64_prism buf;
        pre  = typed_buf \<mapsto>\<langle>\<top>\<rangle> g\<down>old_v;
        post = \<lambda>_. typed_buf \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. new_v) \<sqdot> (g\<down>old_v)
     in make_function_contract pre post\<close>
ucincl_auto write_reinterpret_contract

lemma write_reinterpret_spec:
  shows \<open>\<Gamma>; write_reinterpret buf val \<Turnstile>\<^sub>F write_reinterpret_contract buf g old_v val\<close>
  by (crush_boot f: write_reinterpret_def contract: write_reinterpret_contract_def)
     (crush_base simp add: raw_ptr_cast_def c_cast_from_void_def)

subsection \<open>Swap via Raw Buffers\<close>

text \<open>
  Swap two @{typ \<open>32 word\<close>} values held in raw (untyped) references,
  using @{verbatim \<open>as *mut u32\<close>} casts.

  Rust analogue:
  @{verbatim \<open>unsafe {
    let tmp = *(a.as_ptr() as *const u32);
    *(a.as_mut_ptr() as *mut u32) = *(b.as_ptr() as *const u32);
    *(b.as_mut_ptr() as *mut u32) = tmp;
  }\<close>}
\<close>

definition swap_raw ::
  \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow>
   ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>swap_raw a b \<equiv> FunctionBody \<lbrakk>
    unsafe {
      let tmp = *(a as *mut u32);
      *(a as *mut u32) = *(b as *mut u32);
      *(b as *mut u32) = tmp
    }
  \<rbrakk>\<close>

definition swap_raw_contract ::
  \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow>
   'gv \<Rightarrow> 'gv \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow>
   ('s, 'a, 'b) function_contract\<close> where
  \<open>swap_raw_contract a b ga gb va vb \<equiv>
    let ra   = c_cast_from_void word32_prism a;
        rb   = c_cast_from_void word32_prism b;
        pre  = ra \<mapsto>\<langle>\<top>\<rangle> ga\<down>va \<star>
               rb \<mapsto>\<langle>\<top>\<rangle> gb\<down>vb;
        post = \<lambda>_. ra \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. vb) \<sqdot> (ga\<down>va) \<star>
               rb \<mapsto>\<langle>\<top>\<rangle> (\<lambda>_. va) \<sqdot> (gb\<down>vb)
     in make_function_contract pre post\<close>
ucincl_auto swap_raw_contract

lemma swap_raw_spec:
  shows \<open>\<Gamma>; swap_raw a b \<Turnstile>\<^sub>F swap_raw_contract a b ga gb va vb\<close>
by (crush_boot f: swap_raw_def contract: swap_raw_contract_def)
   (crush_base simp add: raw_ptr_cast_def c_cast_from_void_def)

end

end

