theory C_Abort_Rules
  imports
    C_Abort
    "Shallow_Separation_Logic.Weakest_Precondition"
begin

section \<open>WP Rules for C Abort Reasons\<close>

lemma wp_c_abort [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> (c_abort reason) \<psi> \<rho> \<theta> = \<theta> (CustomAbort reason) \<star> UNIV\<close>
  by (simp add: c_abort_def wp_abort)

lemma wp_c_abortI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> (CustomAbort reason) \<star> UNIV\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_abort reason) \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: wp_c_abort)

lemma wp_c_null_pointer_dereference [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> c_null_pointer_dereference \<psi> \<rho> \<theta> =
           \<theta> (CustomAbort NullPointerDereference) \<star> UNIV\<close>
  by (simp add: c_null_pointer_dereference_def wp_c_abort)

lemma wp_c_buffer_overflow [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> c_buffer_overflow \<psi> \<rho> \<theta> =
           \<theta> (CustomAbort BufferOverflow) \<star> UNIV\<close>
  by (simp add: c_buffer_overflow_def wp_c_abort)

lemma wp_c_signed_overflow [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> c_signed_overflow \<psi> \<rho> \<theta> =
           \<theta> (CustomAbort SignedOverflow) \<star> UNIV\<close>
  by (simp add: c_signed_overflow_def wp_c_abort)

lemma wp_c_division_by_zero [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> c_division_by_zero \<psi> \<rho> \<theta> =
           \<theta> (CustomAbort DivisionByZero) \<star> UNIV\<close>
  by (simp add: c_division_by_zero_def wp_c_abort)

lemma wp_c_use_after_free [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> c_use_after_free \<psi> \<rho> \<theta> =
           \<theta> (CustomAbort UseAfterFree) \<star> UNIV\<close>
  by (simp add: c_use_after_free_def wp_c_abort)

lemma wp_c_shift_out_of_range [micro_rust_wp_simps]:
  shows \<open>\<W>\<P> \<Gamma> c_shift_out_of_range \<psi> \<rho> \<theta> =
           \<theta> (CustomAbort ShiftOutOfRange) \<star> UNIV\<close>
  by (simp add: c_shift_out_of_range_def wp_c_abort)

lemma wp_c_null_pointer_dereferenceI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> (CustomAbort NullPointerDereference) \<star> UNIV\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> c_null_pointer_dereference \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: wp_c_null_pointer_dereference)

lemma wp_c_buffer_overflowI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> (CustomAbort BufferOverflow) \<star> UNIV\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> c_buffer_overflow \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: wp_c_buffer_overflow)

lemma wp_c_signed_overflowI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> (CustomAbort SignedOverflow) \<star> UNIV\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> c_signed_overflow \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: wp_c_signed_overflow)

lemma wp_c_division_by_zeroI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> (CustomAbort DivisionByZero) \<star> UNIV\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> c_division_by_zero \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: wp_c_division_by_zero)

lemma wp_c_use_after_freeI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> (CustomAbort UseAfterFree) \<star> UNIV\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> c_use_after_free \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: wp_c_use_after_free)

lemma wp_c_shift_out_of_rangeI [micro_rust_wp_intros]:
  assumes \<open>\<phi> \<longlongrightarrow> \<theta> (CustomAbort ShiftOutOfRange) \<star> UNIV\<close>
  shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> c_shift_out_of_range \<psi> \<rho> \<theta>\<close>
  using assms by (simp add: wp_c_shift_out_of_range)

end
