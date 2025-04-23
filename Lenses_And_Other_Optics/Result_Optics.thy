(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Result_Optics
  imports Focus Misc.Result
begin

lift_definition result_ok_focus :: \<open>(('v, 'e) result, 'v) focus\<close>
  is \<open>make_focus_raw_via_view_modify (\<lambda>r. case r of Err _ \<Rightarrow> None | Ok x \<Rightarrow> Some x) over_result\<close>
  by (intro is_valid_focusI, auto simp add: make_focus_raw_via_view_modify_def
    over_result_def focus_update_def split: result.splits)

lift_definition result_err_focus :: \<open>(('v, 'e) result, 'e) focus\<close> is
  \<open>make_focus_raw_via_view_modify (\<lambda>r. case r of Err e \<Rightarrow> Some e | Ok _ \<Rightarrow> None) over_err\<close>
  by (intro is_valid_focusI, auto simp add: make_focus_raw_via_view_modify_def
    over_err_def focus_update_def split: result.splits)

end