(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory MLKEM_Parameters
  imports
    Misc.Array
    "HOL-Library.Word"
begin

text\<open>
  MLKEM (Module Lattice-based Key Encapsulation Mechanism, FIPS 203) parameters.
  This theory defines the core constants, types, zeta table, and well-formedness
  predicates used throughout the MLKEM development.
\<close>

section\<open>Constants\<close>

definition mlkem_q :: \<open>nat\<close> where
  \<open>mlkem_q \<equiv> 3329\<close>

definition mlkem_q_word :: \<open>16 word\<close> where
  \<open>mlkem_q_word \<equiv> 3329\<close>

definition mlkem_n :: \<open>nat\<close> where
  \<open>mlkem_n \<equiv> 256\<close>

definition mlkem_zeta :: \<open>nat\<close> where
  \<open>mlkem_zeta \<equiv> 17\<close>

section\<open>Types\<close>

type_synonym mlkem_poly = \<open>(16 word, 256) array\<close>

section\<open>Zeta table\<close>

text\<open>128 entries: powers of 17 mod 3329 in bit-reversed order per FIPS 203.\<close>
definition zetas_table :: \<open>(16 word, 128) array\<close> where
  \<open>zetas_table \<equiv> array_of_list
    [1, 1729, 2580, 3289, 2642, 630, 1897, 848,
     1062, 1919, 193, 797, 2786, 3260, 569, 1746,
     296, 2447, 1339, 1476, 3046, 56, 2240, 1333,
     1426, 2094, 535, 2882, 2393, 2879, 1974, 821,
     289, 331, 3253, 1756, 1197, 2304, 2277, 2055,
     650, 1977, 2513, 632, 2865, 33, 1320, 1915,
     2319, 1435, 807, 452, 1438, 2868, 1534, 2402,
     2647, 2617, 1481, 648, 2474, 3110, 1227, 910,
     17, 2761, 583, 2649, 1637, 723, 2288, 1100,
     1409, 2662, 3281, 233, 756, 2156, 3015, 3050,
     1703, 1651, 2789, 1789, 1847, 952, 1461, 2687,
     939, 2308, 2437, 2388, 733, 2337, 268, 641,
     1584, 2298, 2037, 3220, 375, 2549, 2090, 1645,
     1063, 319, 2773, 757, 2099, 561, 2466, 2594,
     2804, 1092, 403, 1026, 1143, 2150, 2775, 886,
     1722, 1212, 1874, 1029, 2110, 2935, 885, 2154]\<close>

section\<open>Well-formedness\<close>

definition poly_wf :: \<open>mlkem_poly \<Rightarrow> bool\<close> where
  \<open>poly_wf p \<equiv> \<forall>i < mlkem_n. unat (array_nth p i) < mlkem_q\<close>

section\<open>Basic lemmas\<close>

lemma mlkem_q_pos:
  shows \<open>0 < mlkem_q\<close>
by (simp add: mlkem_q_def)

lemma mlkem_q_nonzero_word:
  shows \<open>mlkem_q_word \<noteq> 0\<close>
by (simp add: mlkem_q_word_def)

lemma mlkem_q_bound16:
  shows \<open>mlkem_q < 2 ^ 16\<close>
by (simp add: mlkem_q_def)

lemma mlkem_q_bound32:
  shows \<open>mlkem_q < 2 ^ 32\<close>
by (simp add: mlkem_q_def)

lemma mlkem_q_word_unat:
  shows \<open>unat mlkem_q_word = mlkem_q\<close>
by (simp add: mlkem_q_word_def mlkem_q_def)

lemma poly_wf_nth:
  assumes \<open>poly_wf p\<close>
      and \<open>i < mlkem_n\<close>
    shows \<open>unat (array_nth p i) < mlkem_q\<close>
using assms by (simp add: poly_wf_def)

lemma zetas_table_wf:
  assumes \<open>i < 128\<close>
    shows \<open>unat (array_nth zetas_table i) < mlkem_q\<close>
proof -
  have \<open>list_all (\<lambda>j. unat (array_nth zetas_table j) < mlkem_q) [0..<128]\<close>
    by eval
  thus ?thesis
    using assms by (auto simp: list_all_iff)
qed

end
