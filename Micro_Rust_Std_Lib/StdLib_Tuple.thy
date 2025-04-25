(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Tuple
  imports Crush.Crush
begin
(*>*)

definition list_zip :: \<open>'a list \<Rightarrow> 'b list \<Rightarrow> ('s, ('a \<times> 'b \<times> tnil) list, 'abort, 'i prompt, 'o prompt_output) function_body\<close> where
  \<open>list_zip \<equiv> lift_fun2 (map2 (\<lambda>x y. (x, y, TNil)))\<close>

(*<*)
end
(*>*)