(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Tuple
  imports
    Core_Expression
begin
(*>*)

datatype tnil = TNil

abbreviation(input) tuple_base_pair :: \<open>('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                        ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                        ('s, 'arg0 \<times> 'arg1 \<times> tnil, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_base_pair \<equiv> bindlift2 (\<lambda>x y. (x, y, TNil))\<close>

abbreviation(input) tuple_cons :: \<open>('s, 'arg0, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                   ('s, 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                   ('s, 'arg0 \<times> 'arg1, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_cons \<equiv> bindlift2 (\<lambda>x y. (x, y))\<close>

abbreviation(input) tuple_index_0 :: \<open>('s, 'arg0 \<times> 'arg1, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg0, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_0 \<equiv> bindlift1 fst\<close>

abbreviation(input) tuple_index_1 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg1, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_1 \<equiv> bindlift1 (fst \<circ> snd)\<close>

abbreviation(input) tuple_index_2 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg2, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_2 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_3 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg3, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_3 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_4 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg4, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_4 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_5 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg5, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_5 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_6 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg6, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_6 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_7 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7 \<times> 'arg8, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg7, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_7 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_8 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7 \<times> 'arg8 \<times> 'arg9, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg8, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_8 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_9 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7 \<times> 'arg8 \<times> 'arg9 \<times> 'arg10, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                      ('s, 'arg9, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_9 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_10 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7 \<times> 'arg8 \<times> 'arg9 \<times> 'arg10 \<times> 'arg11, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                       ('s, 'arg10, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_10 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_11 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7 \<times> 'arg8 \<times> 'arg9 \<times> 'arg10 \<times> 'arg11 \<times> 'arg12, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                       ('s, 'arg11, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_11 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_12 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7 \<times> 'arg8 \<times> 'arg9 \<times> 'arg10 \<times> 'arg11 \<times> 'arg12 \<times> 'arg13, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                       ('s, 'arg12, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_12 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_13 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7 \<times> 'arg8 \<times> 'arg9 \<times> 'arg10 \<times> 'arg11 \<times> 'arg12 \<times> 'arg13 \<times> 'arg14, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                       ('s, 'arg13, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_13 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_14 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7 \<times> 'arg8 \<times> 'arg9 \<times> 'arg10 \<times> 'arg11 \<times> 'arg12 \<times> 'arg13 \<times> 'arg14 \<times> 'arg15, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                       ('s, 'arg14, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_14 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

abbreviation(input) tuple_index_15 :: \<open>('s, 'arg0 \<times> 'arg1 \<times> 'arg2 \<times> 'arg3 \<times> 'arg4 \<times> 'arg5 \<times> 'arg6 \<times> 'arg7 \<times> 'arg8 \<times> 'arg9 \<times> 'arg10 \<times> 'arg11 \<times> 'arg12 \<times> 'arg13 \<times> 'arg14 \<times> 'arg15 \<times> 'arg16, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
                                       ('s, 'arg15, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>tuple_index_15 \<equiv> bindlift1 (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd)\<close>

(*<*)
end
(*>*)
