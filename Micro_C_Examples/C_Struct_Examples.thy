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
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> c_abort \<Rightarrow> 'i prompt \<Rightarrow>
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

lemma c_point_x_focus_view [simp]:
  shows \<open>focus_view (Abs_focus (make_focus_raw (\<lambda>s. Some (c_point_x s)) (\<lambda>y. update_c_point_x (\<lambda>_. y)))) pval = Some (c_point_x pval)\<close>
proof -
  have valid_via_modify: \<open>is_valid_focus (make_focus_raw_via_view_modify (\<lambda>s. Some (c_point_x s)) update_c_point_x)\<close>
  proof (rule is_valid_focus_via_modifyI')
    show \<open>is_valid_view_modify (\<lambda>s. Some (c_point_x s)) update_c_point_x\<close>
      unfolding is_valid_view_modify_def
    proof (intro conjI allI impI)
      fix f s
      show \<open>Some (c_point_x (update_c_point_x f s)) = map_option f (Some (c_point_x s))\<close>
        by (cases s) simp
    next
      fix f s
      assume eq: \<open>map_option f (Some (c_point_x s)) = Some (c_point_x s)\<close>
      then have fx: \<open>f (c_point_x s) = c_point_x s\<close>
        by simp
      show \<open>update_c_point_x f s = s\<close>
      proof (cases s)
        case (make_c_point x1 x2)
        from fx make_c_point have \<open>f x1 = x1\<close>
          by simp
        then show ?thesis
          using make_c_point by (simp add: c_point.record_simps c_point.expand)
      qed
    next
      fix f g s
      show \<open>update_c_point_x f (update_c_point_x g s) = update_c_point_x (\<lambda>x. f (g x)) s\<close>
        by (cases s) simp
    qed
  qed
  then have valid: \<open>is_valid_focus (make_focus_raw (\<lambda>s. Some (c_point_x s)) (\<lambda>y. update_c_point_x (\<lambda>_. y)))\<close>
    by (simp add: make_focus_raw_via_view_modify_def)
  then show ?thesis
    by (auto simp add: eq_onp_same_args focus_view.abs_eq Abs_focus_inverse)
qed

lemma c_point_y_focus_view [simp]:
  shows \<open>focus_view (Abs_focus (make_focus_raw (\<lambda>s. Some (c_point_y s)) (\<lambda>y. update_c_point_y (\<lambda>_. y)))) pval = Some (c_point_y pval)\<close>
proof -
  have valid_via_modify: \<open>is_valid_focus (make_focus_raw_via_view_modify (\<lambda>s. Some (c_point_y s)) update_c_point_y)\<close>
  proof (rule is_valid_focus_via_modifyI')
    show \<open>is_valid_view_modify (\<lambda>s. Some (c_point_y s)) update_c_point_y\<close>
      unfolding is_valid_view_modify_def
    proof (intro conjI allI impI)
      fix f s
      show \<open>Some (c_point_y (update_c_point_y f s)) = map_option f (Some (c_point_y s))\<close>
        by (cases s) simp
    next
      fix f s
      assume eq: \<open>map_option f (Some (c_point_y s)) = Some (c_point_y s)\<close>
      then have fy: \<open>f (c_point_y s) = c_point_y s\<close>
        by simp
      show \<open>update_c_point_y f s = s\<close>
      proof (cases s)
        case (make_c_point x1 x2)
        from fy make_c_point have \<open>f x2 = x2\<close>
          by simp
        then show ?thesis
          using make_c_point by (simp add: c_point.record_simps c_point.expand)
      qed
    next
      fix f g s
      show \<open>update_c_point_y f (update_c_point_y g s) = update_c_point_y (\<lambda>x. f (g x)) s\<close>
        by (cases s) simp
    qed
  qed
  then have valid: \<open>is_valid_focus (make_focus_raw (\<lambda>s. Some (c_point_y s)) (\<lambda>y. update_c_point_y (\<lambda>_. y)))\<close>
    by (simp add: make_focus_raw_via_view_modify_def)
  then show ?thesis
    by (auto simp add: eq_onp_same_args focus_view.abs_eq Abs_focus_inverse)
qed

lemma c_point_x_lens_focus_view [simp]:
  shows \<open>focus_view (Abs_focus (lens_to_focus_raw (make_lens_via_view_modify c_point_x update_c_point_x))) pval = Some (c_point_x pval)\<close>
proof -
  have valid_vm: \<open>is_valid_lens_view_modify c_point_x update_c_point_x\<close>
    unfolding is_valid_lens_view_modify_def
  proof (intro conjI allI impI)
    fix f s
    show \<open>c_point_x (update_c_point_x f s) = f (c_point_x s)\<close>
      by (cases s) simp
  next
    fix f s
    assume eq: \<open>f (c_point_x s) = c_point_x s\<close>
    show \<open>update_c_point_x f s = s\<close>
    proof (cases s)
      case (make_c_point x1 x2)
      from eq make_c_point have \<open>f x1 = x1\<close>
        by simp
      then show ?thesis
        using make_c_point by (simp add: c_point.record_simps c_point.expand)
    qed
  next
    fix f g s
    show \<open>update_c_point_x f (update_c_point_x g s) = update_c_point_x (\<lambda>x. f (g x)) s\<close>
      by (cases s) simp
  qed
  have valid: \<open>is_valid_lens (make_lens_via_view_modify c_point_x update_c_point_x)\<close>
    by (rule is_valid_lens_via_modifyI'[OF valid_vm])
  from lens_to_focus_raw_components'[OF valid] show ?thesis
    by (simp add: make_lens_via_view_modify_components)
qed

lemma c_point_y_lens_focus_view [simp]:
  shows \<open>focus_view (Abs_focus (lens_to_focus_raw (make_lens_via_view_modify c_point_y update_c_point_y))) pval = Some (c_point_y pval)\<close>
proof -
  have valid_vm: \<open>is_valid_lens_view_modify c_point_y update_c_point_y\<close>
    unfolding is_valid_lens_view_modify_def
  proof (intro conjI allI impI)
    fix f s
    show \<open>c_point_y (update_c_point_y f s) = f (c_point_y s)\<close>
      by (cases s) simp
  next
    fix f s
    assume eq: \<open>f (c_point_y s) = c_point_y s\<close>
    show \<open>update_c_point_y f s = s\<close>
    proof (cases s)
      case (make_c_point x1 x2)
      from eq make_c_point have \<open>f x2 = x2\<close>
        by simp
      then show ?thesis
        using make_c_point by (simp add: c_point.record_simps c_point.expand)
    qed
  next
    fix f g s
    show \<open>update_c_point_y f (update_c_point_y g s) = update_c_point_y (\<lambda>x. f (g x)) s\<close>
      by (cases s) simp
  qed
  have valid: \<open>is_valid_lens (make_lens_via_view_modify c_point_y update_c_point_y)\<close>
    by (rule is_valid_lens_via_modifyI'[OF valid_vm])
  from lens_to_focus_raw_components'[OF valid] show ?thesis
    by (simp add: make_lens_via_view_modify_components)
qed

lemma c_swap_coords_spec:
  shows \<open>\<Gamma>; c_swap_coords pref \<Turnstile>\<^sub>F c_swap_coords_contract pref pg pval\<close>
by (crush_boot f: c_swap_coords_def contract: c_swap_coords_contract_def)
  (crush_base simp add: c_point.record_simps)

end

end
