theory C_Struct_Examples
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
    "Shallow_Micro_C.C_Arithmetic_Rules"
    "Micro_Rust_Std_Lib.StdLib_All"
begin

micro_c_translate \<open>
  struct point {
    int x;
    int y;
  };
\<close>

thm c_point.record_simps

section \<open>C struct verification\<close>

text \<open>
  This theory demonstrates verification of C code operating on structs.
  The function @{text swap_coords} swaps the x and y fields of a
  point struct via a pointer.
\<close>

locale c_struct_verification_ctx =
    reference reference_types +
    ref_c_int: reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism +
    ref_c_point: reference_allocatable reference_types _ _ _ _ _ _ _ c_point_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow>
        'o prompt_output \<Rightarrow> unit\<close>
  and c_int_prism :: \<open>('gv, c_int) prism\<close>
  and c_point_prism :: \<open>('gv, c_point) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_point.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

micro_c_translate \<open>
  struct point {
    int x;
    int y;
  };

  void swap_coords(struct point *p) {
    int t = p->x;
    p->x = p->y;
    p->y = t;
  }
\<close>

thm c_swap_coords_def

text \<open>
  The contract for swap\_coords: given a reference to a c\_point with value
  @{text pval}, after execution the x and y fields are swapped.
\<close>
definition c_swap_coords_contract :: \<open>('addr, 'gv, c_point) Global_Store.ref \<Rightarrow> 'gv \<Rightarrow> c_point \<Rightarrow>
      ('s, 'a, 'b) function_contract\<close> where
  \<open>c_swap_coords_contract pref pg pval \<equiv>
    let pre  = can_alloc_reference \<star>
               pref \<mapsto>\<langle>\<top>\<rangle> pg\<down>pval;
        post = \<lambda>_. can_alloc_reference \<star>
               pref \<mapsto>\<langle>\<top>\<rangle>
                 (\<lambda>_. update_c_point_y (\<lambda>_. c_point_x pval)
                         (update_c_point_x (\<lambda>_. c_point_y pval) pval)) \<sqdot> (pg\<down>pval)
     in make_function_contract pre post\<close>
ucincl_auto c_swap_coords_contract

lemma c_swap_coords_spec:
  shows \<open>\<Gamma>; c_swap_coords pref \<Turnstile>\<^sub>F c_swap_coords_contract pref pg pval\<close>
by (crush_boot f: c_swap_coords_def contract: c_swap_coords_contract_def) crush_base

end

end
