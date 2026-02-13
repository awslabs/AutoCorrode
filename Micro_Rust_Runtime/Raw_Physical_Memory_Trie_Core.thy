(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Raw_Physical_Memory_Trie_Core
  imports Main
    Crush.Crush
    "HOL-Library.Datatype_Records"
    Shallow_Separation_Logic.Apartness
    Shallow_Separation_Logic.Separation_Algebra
    Shallow_Separation_Logic.Assertion_Language
    Shallow_Separation_Logic.Tree_Shares
    Shallow_Separation_Logic.Shareable_Value
    Word_Lib.Word_Lib_Sumo
    Misc.WordAdditional

begin
(*>*)

section\<open>Breaking memory regions into naturally-aligned blocks\<close>

lemma word_ctz_is_aligned:
  shows \<open>is_aligned l (word_ctz l)\<close>
proof -
  have \<open>\<And>n. n < word_ctz l \<Longrightarrow> \<not>(l!!n)\<close>
    by (clarsimp simp add: word_ctz_unfold', blast)
  then show ?thesis
    using is_aligned_nth by auto
qed

lemma word_ctz_is_aligned':
  assumes \<open>is_aligned l n\<close> \<open>n \<le> size l\<close> shows \<open>n \<le> word_ctz l\<close>
  using assms
  unfolding is_aligned_nth word_ctz_unfold' le_def
  by (metis Min.insert Min.singleton Min_in finite_bit_word mem_Collect_eq min_def word_size)

lemma word_log2_pow2_le:
  assumes \<open>l > 0\<close>
  shows \<open>2^word_log2 l \<le> l\<close>
proof -
  have \<open>word_log2 l = Max { n . l !! n}\<close>
    using assms word_log2_unfold[of l] by clarsimp
  moreover have \<open>l !! Max { n . l !! n}\<close>
    using assms word_exists_nth[of l]
    by (metis bit_word_log2 word_gt_0 word_log2_unfold)
  ultimately show ?thesis
    using assms bang_is_le[of l] by clarsimp
qed


definition next_aligned_block_size :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> nat\<close> where
  \<open>next_aligned_block_size adr l \<equiv> min (word_ctz adr) (word_log2 l)\<close>

lemma next_aligned_block_size_le:
  fixes l :: \<open>64 word\<close>
  assumes \<open>l > 0\<close>
  shows \<open>2^next_aligned_block_size adr l \<le> l\<close>
proof -
  have \<open>next_aligned_block_size adr l \<le> word_log2 l\<close>
    by (simp add: next_aligned_block_size_def)
  then show ?thesis
    using word_log2_pow2_le[OF assms] unfolding next_aligned_block_size_def
    by (metis (no_types, opaque_lifting) order_trans two_power_increasing word_log2_max word_size)
qed

lemma next_aligned_block_size_gt0:
  fixes l :: \<open>64 word\<close>
  assumes \<open>l > 0\<close>
  shows \<open>2^next_aligned_block_size adr l > (0::64 word)\<close>
  using assms unfolding next_aligned_block_size_def
  by (metis min.strict_coboundedI2 p2_gt_0 word_log2_max wsst_TYs(3))

lemma next_aligned_block_size_shrink:
  fixes l :: \<open>64 word\<close>
  assumes \<open>l > 0\<close>
  shows \<open>(l - 2 ^ next_aligned_block_size adr l) < l\<close>
  using next_aligned_block_size_gt0 assms next_aligned_block_size_le word_diff_less by blast

lemma next_aligned_block_is_aligned:
  \<open>is_aligned adr (next_aligned_block_size adr l)\<close>
  unfolding next_aligned_block_size_def
  using word_ctz_is_aligned is_aligned_weaken min.cobounded1
  by blast

lemma next_aligned_block_bound:
  shows \<open>next_aligned_block_size adr l < size adr\<close>
  using word_log2_max[of l]
  unfolding next_aligned_block_size_def size_word_def by simp

lemma next_aligned_block_size_largest:
  assumes \<open>is_aligned adr n\<close> and \<open>2^n \<le> l\<close> and \<open>n < size adr\<close> and \<open>0 < l\<close>
  shows \<open>n \<le> next_aligned_block_size adr l\<close>
proof -
  have \<open>n \<le> word_ctz adr\<close>
    using assms word_ctz_is_aligned'[of adr n] by auto
  moreover obtain i where \<open>n \<le> i \<and> l!!i\<close>
    using assms less_2p_is_upper_bits_unset[of l n]
    unfolding size_word_def by auto
  moreover from this have \<open>n \<le> word_log2 l\<close>
    using le_trans word_log2_maximum by blast
  ultimately show ?thesis
    unfolding next_aligned_block_size_def by auto
qed

text\<open>Given an address and a length, compute a sequence of naturally-aligned blocks
that partition the region. This is intended to be the shortest sequence of blocks
covering the region (this is not currently proved).\<close>
function range_to_aligned_blocks :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> (64 word \<times> nat) list\<close> where
  \<open>range_to_aligned_blocks adr l =
   (if l > 0 then
      let n = next_aligned_block_size adr l in
      (adr, n) # range_to_aligned_blocks (adr + 2^n) (l - 2^n)
    else [])\<close>
  by pat_completeness auto
termination
  apply (relation \<open>measure (unat \<circ> snd)\<close>, force)
  by (simp add: unat_mono next_aligned_block_size_shrink comp_def)

declare range_to_aligned_blocks.simps[simp del]


lemma range_to_aligned_blocks_induct:
  assumes \<open>\<And>addr l. l = 0 \<Longrightarrow> P addr l []\<close>
  and \<open>\<And>addr l xs . 0 < l \<Longrightarrow>
        xs = range_to_aligned_blocks (addr+2^next_aligned_block_size addr l) (l-2^next_aligned_block_size addr l) \<Longrightarrow>
        P (addr+2^next_aligned_block_size addr l) (l-2^next_aligned_block_size addr l) xs \<Longrightarrow>
        P addr l ((addr, next_aligned_block_size addr l)#xs)\<close>
  shows \<open>P adr l (range_to_aligned_blocks adr l)\<close>
proof (induction adr l rule: range_to_aligned_blocks.induct)
  case (1 adr l)
  then show ?case
    by (metis assms range_to_aligned_blocks.simps word_gt_0)
qed

lemma range_to_aligned_blocks_aligned:
  shows \<open>(a,n) \<in> set (range_to_aligned_blocks adr l) \<Longrightarrow> is_aligned a n\<close>
by (induction adr l rule: range_to_aligned_blocks_induct)
   (auto simp add: Let_def next_aligned_block_is_aligned)

lemma range_to_aligned_blocks_page_range:
  assumes \<open>0 < l\<close> and \<open>adr \<le> adr + (l - 1)\<close>
  shows \<open>{ adr .. (adr + l - 1) } =
         \<Union>( (\<lambda>an. page_range_word (fst an) (snd an)) ` set (range_to_aligned_blocks adr l))\<close>
using assms
proof (induction adr l rule: range_to_aligned_blocks_induct)
  case (1 addr l)
  then show ?case by clarsimp
next
  case (2 addr l xs)
  { \<comment> \<open>In this case, we need to make another recursive call\<close>
    assume \<open>0 < l - 2 ^ next_aligned_block_size addr l\<close>
    moreover from 2 this have \<open>addr \<le> addr + (2 ^ next_aligned_block_size addr l - 1)\<close>
      using is_aligned_no_overflow' next_aligned_block_is_aligned by blast
    moreover from 2 have \<open>addr + 2 ^ next_aligned_block_size addr l - 1 \<le> addr + l - 1\<close>
      by (metis (no_types, opaque_lifting) add_diff_eq lt1_neq0 next_aligned_block_size_le
           next_aligned_block_size_shrink nle_le verit_minus_simplify(2) word_le_minus_cancel
           word_le_not_less word_plus_mono_right)
    moreover from calculation have \<open> {addr..addr + l - 1} =
      { addr .. addr + 2 ^ next_aligned_block_size addr l - 1 }
      \<union> {addr + 2 ^ next_aligned_block_size addr l..addr + l - 1}\<close>
      using word_atLeastLessThan_Suc_atLeastAtMost_union
              [where m = \<open>addr + 2 ^ next_aligned_block_size addr l - 1\<close>]
      by (simp add: add_diff_eq less_1_simp word_gt_0 word_le_less_eq)
    moreover have \<open>{addr..addr + 2 ^ next_aligned_block_size addr l - 1} =
                 page_range_word addr (next_aligned_block_size addr l)\<close>
      unfolding page_range_word_def by simp
    moreover from 2 calculation
    have \<open>addr + 2 ^ next_aligned_block_size addr l \<le> addr + (l - 1)\<close>
      by (metis (no_types, lifting) add_cancel_right_right group_cancel.sub1 less_1_simp order_less_le zadd_diff_inverse)
    ultimately have ?case
      using 2 by (clarsimp  simp add: Let_def)
  } moreover
  { assume \<open>2 ^ next_aligned_block_size addr l = l\<close>
    then have ?case
    using 2 by (clarsimp simp add: page_range_word_def range_to_aligned_blocks.simps)
  }
  ultimately show ?case
    by (meson 2 less_diff_gt0 next_aligned_block_size_le word_le_less_eq)
qed


lemma range_to_aligned_blocks_bounds:
  assumes \<open>range_to_aligned_blocks adr l ! i = (x,n)\<close>
  and \<open>i < length (range_to_aligned_blocks adr l)\<close>
  and \<open>0 < l\<close>
  and \<open>adr \<le> adr + (l-1)\<close>
  and \<open>adr < 2^N\<close>
  and \<open>adr+(l-1) < 2^N\<close>
  shows \<open>adr \<le> x \<and> x \<le> adr + (l-1) \<and> x < 2^N \<and> n \<le> N\<close>
using assms proof (induction adr l arbitrary: i rule: range_to_aligned_blocks_induct)
  case (1 addr l)
  then show ?case by clarsimp
next
  case (2 addr l xs)
  moreover from this have \<open>l \<le> 2^N\<close>
    by (metis add_diff_cancel_left' word_less_imp_diff_less word_minus_one_le_leq)
  moreover from calculation have \<open>2^next_aligned_block_size x l \<le> (2^N :: 64 word)\<close>
    using next_aligned_block_size_le order_trans by blast
  moreover from calculation have \<open>next_aligned_block_size x l \<le> N\<close>
    by (metis next_aligned_block_size_shrink not_le order.refl p2_gt_0 power_le_mono verit_minus_simplify(2) word_coorder.not_eq_extremum)
  moreover {
    note calculation
    moreover assume \<open>i > 0\<close>
    moreover from calculation have \<open>0 < l - 2 ^ next_aligned_block_size addr l\<close>
      by clarsimp (metis list.size(3) not_less_eq range_to_aligned_blocks.elims)
    moreover from calculation
    have \<open>addr + 2 ^ next_aligned_block_size addr l
        \<le> addr + 2 ^ next_aligned_block_size addr l + (l - 2 ^ next_aligned_block_size addr l - 1)\<close>
      by (metis (no_types, lifting) add_diff_eq eq_iff_diff_eq_0 le_m1_iff_lt next_aligned_block_size_le nless_le word_plus_mono_right zadd_diff_inverse)
    moreover from calculation have
      \<open>addr \<le> addr + 2 ^ next_aligned_block_size addr l\<close>
      by (metis arith_extra_simps(5) next_aligned_block_size_le word_le_minus_one_leq word_less_add_right word_plus_mono_right2)
    ultimately have ?case
      by (fastforce simp add: nth_Cons' split: if_splits)
  }
  ultimately show ?case
    by (clarsimp simp add: nth_Cons' split: if_splits)
qed

definition \<open>PMEM_TRIE_ADDRESS_WIDTH \<equiv> 48::nat\<close>
definition \<open>PMEM_TRIE_ADDRESS_LIMIT \<equiv> 2^PMEM_TRIE_ADDRESS_WIDTH\<close>
lemmas pmem_trie_bounds = PMEM_TRIE_ADDRESS_WIDTH_def PMEM_TRIE_ADDRESS_LIMIT_def

definition bits_range :: \<open>64 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 64 word set\<close> where
  \<open>bits_range addr h block_h \<equiv> { x. \<forall>n. block_h \<le> n \<longrightarrow> n < h \<longrightarrow> addr!!n = x!!n }\<close>

lemma bits_range_Suc [simp]:
  shows \<open>x \<in> bits_range addr (Suc h) block_h = (h < block_h \<or> (x \<in> bits_range addr h block_h \<and> x!!h = addr!!h))\<close>
  unfolding bits_range_def using nat_less_le by fastforce

lemma bits_range_split:
  assumes \<open>h \<ge> block_h\<close>
  shows \<open>bits_range addr (Suc h) block_h =
          (if addr!!h then
             { x. x \<in> bits_range addr h block_h \<and> x!!h }
           else
             { x. x \<in> bits_range addr h block_h \<and> \<not>(x!!h) })\<close>
  using assms unfolding bits_range_def by (auto simp add: nat_le_Suc_less_imp nless_le)

lemma block_range0[simp] : \<open>block_range pa 0 = { pa }\<close>
  unfolding block_range_def by fastforce

lemma block_range_includes:
  shows \<open>addr \<in> block_range addr h\<close>
  unfolding block_range_def by auto

lemma block_range_to_bits_core:
  notes PMEM_TRIE_ADDRESS_LIMIT_def[simp]
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
      and \<open>block_h \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
    shows \<open>x \<in> block_range pa block_h \<Longrightarrow> x \<in> bits_range pa PMEM_TRIE_ADDRESS_WIDTH block_h\<close>
      and \<open>x < PMEM_TRIE_ADDRESS_LIMIT \<Longrightarrow> x \<in> bits_range pa PMEM_TRIE_ADDRESS_WIDTH block_h
                           \<Longrightarrow> x \<in> block_range pa block_h\<close>
  using assms
   apply (simp_all add: block_range_def bits_range_def)
   apply (metis neg_mask_test_bit test_bit_conj_lt word_and_nth)
  apply (word_eqI, auto)
  done

lemma block_range_to_bits:
  notes PMEM_TRIE_ADDRESS_LIMIT_def[simp]
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close>
      and \<open>x < PMEM_TRIE_ADDRESS_LIMIT\<close>
      and \<open>block_h \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
    shows \<open>x \<in> block_range pa block_h \<longleftrightarrow> x \<in> bits_range pa PMEM_TRIE_ADDRESS_WIDTH block_h\<close>
  using assms block_range_to_bits_core by auto

lemma finite_block_range: shows \<open>finite (block_range pa n)\<close>
  by (rule finite_word)

lemma bits_range_inh:
  assumes \<open>h < 64\<close>
  shows \<open>(addr AND mask h) \<in> bits_range addr h block_h \<and> (addr AND mask h) < 2 ^ h\<close>
proof (intro and_mask_less_size conjI)
  show \<open>addr && mask h \<in> bits_range addr h block_h\<close>
    by (simp add: bits_range_def bit_take_bit_iff flip: take_bit_eq_mask)
next
  show \<open>h < size addr\<close>
    using assms by (simp add: size_word_def)
qed

lemma block_range_split:
  assumes \<open>is_aligned pa (Suc n)\<close>
  shows \<open>block_range pa (Suc n) = block_range pa n \<union> block_range (pa + (2^n)) n\<close>
proof -
  have H: \<open>word_align_down pa n || 2 ^ n = word_align_down x n\<close>
    if \<open>word_align_down pa (Suc n) = word_align_down x (Suc n)\<close>
      and \<open>pa !! n \<noteq> x !! n\<close> for x :: \<open>64 word\<close>
  proof -
    have \<open>x !! n\<close>
      by (metis assms that is_aligned_neg_mask_eq' word_ao_nth)
    with assms that show ?thesis
     by - (word_eqI, fastforce)
  qed
  have B: \<open>\<And>x. \<lbrakk>word_align_down pa (Suc n) = word_align_down x (Suc n);
                word_align_down pa n || 2 ^ n \<noteq> word_align_down x n\<rbrakk>
         \<Longrightarrow> word_align_down pa n = word_align_down x n\<close>
    by (metis H assms Suc_mask_eq_mask is_aligned_nth lessI subtract_mask(1))
  have C: \<open>\<And>x. word_align_down pa n = word_align_down x n
                \<Longrightarrow> word_align_down pa (Suc n) = word_align_down x (Suc n)\<close>
    by (metis (no_types, lifting) add_diff_cancel_right' mask_Suc_exp neg_mask_add_mask word_bw_lcs(2))
  have D: \<open>\<And>x. word_align_down pa n || 2 ^ n = word_align_down x n
                \<Longrightarrow> word_align_down pa (Suc n) = word_align_down x (Suc n)\<close>
    by word_eqI force
  show ?thesis
    using assms by (force simp: block_range_def word_align_down_plus_pow2 intro: B C D)
qed

lemma block_range_split_disjoint:
  assumes pa: \<open>is_aligned pa (Suc n)\<close> and \<open>n < 64\<close>
  shows \<open>block_range pa n \<inter> block_range (pa + 2 ^ n) n = {}\<close>
  unfolding block_range_def word_align_down_plus_pow2 disjoint_iff
proof clarify
  fix x :: \<open>64 word\<close>
  assume eq: \<open>word_align_down pa n = word_align_down x n\<close>
             \<open>word_align_down (pa + 2 ^ n) n = word_align_down x n\<close>
  then have \<open>(word_align_down x n || 2 ^ n) !! n\<close>
    by (simp add: assms(2) bit_exp_iff word_or_nth)
  moreover have \<open>\<not>(word_align_down x n !! n)\<close>
    by (metis pa bit_and_iff eq(1) is_aligned_nth lessI)
  ultimately show False
    using pa eq word_align_down_plus_pow2 by force
qed

type_synonym 'tag physical_byte_state = \<open>('tag \<times> 8 word) shareable_value\<close>
abbreviation Unmapped :: \<open>'tag physical_byte_state\<close> where \<open>Unmapped \<equiv> No_Value\<close>
abbreviation Tagged :: \<open>nonempty_share \<Rightarrow> 'tag \<Rightarrow> 8 word \<Rightarrow> 'tag physical_byte_state\<close> where
   \<open>Tagged sh tag val \<equiv> Shared_Value sh (tag, val)\<close>

lemma tagged_disjoint_lemma:
  assumes \<open>Tagged sh tag b \<sharp> x\<close>
  shows \<open>x = Unmapped \<or> (\<exists>sh'. Rep_nonempty_share sh \<sharp> Rep_nonempty_share sh' \<and> x = Tagged sh' tag b)\<close>
  using assms by (cases x; simp)

corollary tagged_disjoint_lemma':
  assumes \<open>Tagged \<top> tag b \<sharp> x\<close>
  shows \<open>x = Unmapped\<close>
  by (metis assms shareable_value_disjoint_top(1))

lemma tagged_top_disjoint_lemma:
  assumes \<open>Tagged \<top> tagA bA \<sharp> y\<close>
  shows \<open>Tagged \<top> tagB bB \<sharp> y\<close>
  by (metis assms shareable_value_disjoint_top(1))

type_synonym 'tag physical_byte_class = \<open>'tag shareable_value\<close>

definition state_to_class :: \<open>'tag physical_byte_state \<Rightarrow> 'tag physical_byte_class\<close> where
  \<open>state_to_class \<equiv> map_shareable_value fst\<close>

lemma
  shows [simp]: \<open>state_to_class Unmapped = No_Value\<close>
  and   [simp]: \<open>state_to_class (Tagged sh tag x) = Shared_Value sh tag\<close>
  by (auto simp add: state_to_class_def map_shareable_value_def)

definition map_tag :: \<open>('tag \<Rightarrow> 'tag) \<Rightarrow> 'tag physical_byte_state \<Rightarrow> 'tag physical_byte_state\<close>
  where \<open>map_tag f \<equiv> map_shareable_value (apfst f)\<close>

abbreviation tag_byte_state :: \<open>'tag \<Rightarrow> 'tag physical_byte_state \<Rightarrow> 'tag physical_byte_state\<close>
  where \<open>tag_byte_state tag \<equiv> map_tag (\<lambda>_. tag)\<close>

lemma
  shows [simp]: \<open>map_tag f (Tagged sh tag x) = Tagged sh (f tag) x\<close>
    and [simp]: \<open>map_tag f Unmapped = Unmapped\<close>
  by (simp add: map_tag_def map_shareable_value_def)+

abbreviation writeable_byte_state :: \<open>'tag physical_byte_state \<Rightarrow> bool\<close> where
  \<open>writeable_byte_state b \<equiv>
    case b of
      Shared_Value sh _ \<Rightarrow> sh = \<top>
    | No_Value \<Rightarrow> False\<close>

definition set_byte_state :: \<open>'tag physical_byte_state \<Rightarrow> 8 word \<Rightarrow> 'tag physical_byte_state\<close> where
  \<open>set_byte_state b x \<equiv> map_shareable_value (apsnd (\<lambda>_. x)) b\<close>

lemma writeable_byte_state_disjoint:
  assumes \<open>writeable_byte_state x\<close> and \<open>x\<sharp>y\<close>
  shows \<open>y = Unmapped\<close>
  using assms by (cases x; simp add: shareable_value_disjoint_top(2))

section\<open>Trie-based representation for naturally-aligned blocks of memory.\<close>

text\<open>This theory provides an efficiently executable interpretation of the
\<^verbatim>\<open>physical_memory\<close> locale.\<close>

text\<open>\<^verbatim>\<open>memory_contents\<close> is a big-endian binary trie representing
the contents of a block of physical memory of size \<^verbatim>\<open>2^h\<close>, for a height
value of \<^verbatim>\<open>h\<close>. \<^verbatim>\<open>MC_byte b\<close> represents a uniform block of \<^verbatim>\<open>2^h\<close> copies of b.
\<^verbatim>\<open>MC_node n0 n1\<close> represents a block split in two, where values for
addresses with the high bit equal to zero are found in \<^verbatim>\<open>n0\<close> and
address with high bit equal to one are found in \<^verbatim>\<open>n1\<close>. Both \<^verbatim>\<open>n0\<close>
and \<^verbatim>\<open>n1\<close> then have height \<^verbatim>\<open>h-1\<close>. Note the height of the trie is not
stored, but is implicit; it is directly provided via the operations
called on the trie.\<close>
datatype memory_contents
  = MC_node memory_contents memory_contents
  | MC_byte \<open>8 word\<close>

fun mc_left :: \<open>memory_contents \<Rightarrow> memory_contents\<close> where
  \<open>mc_left (MC_node n0 n1) = n0\<close> |
  \<open>mc_left (MC_byte b) = MC_byte b\<close>

fun mc_right :: \<open>memory_contents \<Rightarrow> memory_contents\<close> where
  \<open>mc_right (MC_node n0 n1) = n1\<close> |
  \<open>mc_right (MC_byte b) = MC_byte b\<close>

fun mc_height :: \<open>memory_contents \<Rightarrow> nat\<close> where
  \<open>mc_height (MC_byte _) = 0\<close> |
  \<open>mc_height (MC_node n0 n1) = 1 + (max (mc_height n0) (mc_height n1))\<close>

fun lookup_memory_contents :: \<open>memory_contents \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 8 word\<close> where
  \<open>lookup_memory_contents (MC_byte b) _ _ = b\<close> |
  \<open>lookup_memory_contents (MC_node _ _) 0 addr = undefined\<close> |
  \<open>lookup_memory_contents (MC_node zero_n one_n) (Suc h) addr =
    (if bit addr h then
      lookup_memory_contents one_n h addr
     else
      lookup_memory_contents zero_n h addr)\<close>

fun mc_node :: \<open>memory_contents \<Rightarrow> memory_contents \<Rightarrow> memory_contents\<close> where
  \<open>mc_node (MC_byte b0) (MC_byte b1) = (if b0 = b1 then MC_byte b0 else MC_node (MC_byte b0) (MC_byte b1))\<close> |
  \<open>mc_node n0 n1 = MC_node n0 n1\<close>

lemma lookup_memory_contents_mc_node:
  assumes \<open>h > mc_height n0\<close> \<open>h > mc_height n1\<close>
  shows \<open>lookup_memory_contents (mc_node n0 n1) h addr = lookup_memory_contents (MC_node n0 n1) h addr\<close>
  using assms
proof (induction n0 n1 rule: mc_node.induct)
  case 1
  then show ?case by (cases h; simp)
qed auto

fun canonicalize_memory_contents :: \<open>memory_contents \<Rightarrow> memory_contents\<close> where
  \<open>canonicalize_memory_contents (MC_node n1 n2) =
     mc_node (canonicalize_memory_contents n1) (canonicalize_memory_contents n2)\<close> |
  \<open>canonicalize_memory_contents (MC_byte b) = MC_byte b\<close>

fun write_memory_contents :: \<open>memory_contents \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow> memory_contents\<close> where
  \<open>write_memory_contents _ 0 _ b = MC_byte b\<close> |
  \<open>write_memory_contents m (Suc h) addr b =
    (if bit addr h then
       mc_node (mc_left m) (write_memory_contents (mc_right m) h addr b)
     else
       mc_node (write_memory_contents (mc_left m) h addr b) (mc_right m))\<close>

fun memset_memory_block ::
  \<open>memory_contents \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 8 word \<Rightarrow> memory_contents\<close> where

  \<open>memset_memory_block m h addr block_h b =
   (if h > block_h then
      (if bit addr (h-1) then
         mc_node (mc_left m) (memset_memory_block (mc_right m) (h-1) addr block_h b)
       else
         mc_node (memset_memory_block (mc_left m) (h-1) addr block_h b) (mc_right m))
    else
      MC_byte b)\<close>

declare memset_memory_block.simps [simp del]

definition memory_contents_canonical :: \<open>memory_contents \<Rightarrow> bool\<close> where
  \<open>memory_contents_canonical mc \<equiv> canonicalize_memory_contents mc = mc\<close>

lemma mc_node_canonical:
  assumes \<open>memory_contents_canonical n0\<close>
  and \<open>memory_contents_canonical n1\<close>
  shows \<open>memory_contents_canonical (mc_node n0 n1)\<close>
  using assms unfolding memory_contents_canonical_def
  by (induction n0 n1 rule: mc_node.induct, auto)

lemma mc_node_commute:
  shows \<open>canonicalize_memory_contents (mc_node n0 n1) =
           mc_node (canonicalize_memory_contents n0) (canonicalize_memory_contents n1)\<close>
  by (induction n0 n1 rule: mc_node.induct, auto)

lemma mc_canonicalize_correct:
  shows \<open>memory_contents_canonical (canonicalize_memory_contents mc)\<close>
  using mc_node_canonical unfolding memory_contents_canonical_def
  by (induction mc rule: canonicalize_memory_contents.induct, auto)

lemma mc_node_eqE:
  assumes \<open>mc_node n0 n1 = MC_node n0' n1'\<close>
    and \<open>n0 = n0' \<Longrightarrow> n1 = n1' \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (induction n0 n1 rule: mc_node.induct, auto split: if_splits)

lemma lookup_memory_contents_eq:
  assumes \<open>\<forall>n. n < h \<longrightarrow> addr!!n = addr'!!n\<close>
  shows \<open>lookup_memory_contents x h addr = lookup_memory_contents x h addr'\<close>
using assms by (induction x h addr arbitrary: addr' rule: lookup_memory_contents.induct; clarsimp)

lemma memory_contents_node_constant_aux:
  fixes x y h b
  assumes \<open>\<And>addr. lookup_memory_contents (MC_node x y) (Suc h) addr = b\<close> and \<open>h < 64\<close>
  shows \<open>\<And>addr. lookup_memory_contents x h addr = b\<close>
  and \<open>\<And>addr. lookup_memory_contents y h addr = b\<close>
proof -
  fix addr :: \<open>64 word\<close>
  obtain addr' where \<open>addr' = set_bit addr h False\<close> by simp
  moreover from this have \<open>lookup_memory_contents x h addr' = b\<close>
    using assms by clarsimp (metis test_bit_set)
  ultimately show \<open>lookup_memory_contents x h addr = b\<close>
    using lookup_memory_contents_eq
    by (metis (no_types, lifting) nat_less_le test_bit_set_gen)
next
  fix addr :: \<open>64 word\<close>
  obtain addr' where \<open>addr' = set_bit addr h True\<close> by simp
  moreover from this have \<open>lookup_memory_contents y h addr' = b\<close>
    using assms(1)[of addr'] assms(2)
    by (clarsimp simp add: test_bit_set_gen size_word_def)
  ultimately show \<open>lookup_memory_contents y h addr = b\<close>
    using lookup_memory_contents_eq
    by (metis (no_types, lifting) not_less_iff_gr_or_eq test_bit_set_gen)
qed

lemma memory_contents_node_constant:
  assumes \<open>memory_contents_canonical mc\<close>
  and \<open>\<forall>addr. lookup_memory_contents mc h addr = b\<close>
  and \<open>mc_height mc \<le> h\<close>
  and \<open>h \<le> 64\<close>
  shows \<open>mc = MC_byte b\<close>
using assms proof (induction mc arbitrary: h)
  case (MC_node mc1 mc2)
  moreover from this have
    \<open>\<forall>addr. lookup_memory_contents mc1 (h-1) addr = b\<close>
    \<open>\<forall>addr. lookup_memory_contents mc2 (h-1) addr = b\<close>
    using memory_contents_node_constant_aux[of mc1 mc2 \<open>h-1\<close> b] by auto
  moreover from calculation have \<open>mc1 = MC_byte b \<and> mc2 = MC_byte b\<close>
    by (clarsimp simp add: memory_contents_canonical_def elim!: mc_node_eqE)
  then show ?case
    using MC_node(3-4) by (clarsimp simp add: memory_contents_canonical_def)
next
  case (MC_byte x)
  then show ?case by simp
qed

lemma canonical_MC_nodeE [elim]:
  assumes \<open>memory_contents_canonical (MC_node x y)\<close>
  obtains \<open>memory_contents_canonical x\<close> \<open>memory_contents_canonical y\<close> \<open>mc_node x y = MC_node x y\<close>
  using assms mc_node_eqE unfolding memory_contents_canonical_def by fastforce

lemma lookup_memory_contents_node_eqE:
  assumes H: \<open>\<And>addr. lookup_memory_contents (MC_node a b) (Suc h) addr = lookup_memory_contents (MC_node x y) (Suc h) addr\<close>
  and \<open>h < 64\<close>
obtains \<open>\<forall>addr. lookup_memory_contents a h addr = lookup_memory_contents x h addr\<close>
        \<open>\<forall>addr. lookup_memory_contents b h addr = lookup_memory_contents y h addr\<close>
proof -
  have \<open>lookup_memory_contents a h addr = lookup_memory_contents x h addr\<close> for addr :: \<open>64 word\<close>
    using H[of \<open>set_bit addr h False\<close>] lookup_memory_contents_eq [of h addr \<open>set_bit addr h False\<close>]
    by (simp add: test_bit_set_gen)
  moreover
  have \<open>lookup_memory_contents b h addr = lookup_memory_contents y h addr\<close> for addr :: \<open>64 word\<close>
    using H[of \<open>set_bit addr h True\<close>] lookup_memory_contents_eq [of h addr \<open>set_bit addr h True\<close>] \<open>h < 64\<close>
    by (simp add: test_bit_set_gen size_word_def)
  ultimately show thesis
    using that by blast
qed

lemma memory_contents_unique:
  assumes \<open>memory_contents_canonical mc1\<close>
   and \<open>memory_contents_canonical mc2\<close>
   and \<open>mc_height mc1 \<le> h\<close>
   and \<open>mc_height mc2 \<le> h\<close>
   and \<open>h \<le> 64\<close>
   and \<open>\<forall>addr. lookup_memory_contents mc1 h addr = lookup_memory_contents mc2 h addr\<close>
   shows \<open>mc1 = mc2\<close>
  using assms
proof (induction mc1 arbitrary: h mc2)
  case node: (MC_node mc11 mc12)
  show ?case
  proof (cases mc2)
    case (MC_node x y)
    then show ?thesis
      using node lookup_memory_contents_node_eqE[of mc11 mc12 \<open>h-1\<close> x y]
      by (cases h; fastforce)
  next
    case (MC_byte b)
    then show ?thesis using node.prems memory_contents_node_constant
      by (metis lookup_memory_contents.simps(1))
  qed
next
  case (MC_byte x)
  then show ?case
    by (metis lookup_memory_contents.simps(1) memory_contents_node_constant)
qed

lemma memset_memory_block_canonical [intro]:
  assumes \<open>memory_contents_canonical mc\<close>
  shows \<open>memory_contents_canonical (memset_memory_block mc h addr block_h b)\<close>
  using assms
proof (induction mc h addr block_h b rule: memset_memory_block.induct)
  case (1 m h addr block_h b)
  then
  show ?case
    unfolding memset_memory_block.simps[of m]
    apply (simp add: memory_contents_canonical_def mc_node_commute)
    apply (case_tac m; clarsimp elim!: mc_node_eqE)
    done
qed

lemma mc_node_height_le:
  shows \<open>mc_height (mc_node x y) \<le> mc_height (MC_node x y)\<close>
  by (induction x y rule: mc_node.induct; simp)

lemma mc_height_mc_nodeI [intro]:
  assumes \<open>mc_height (MC_node x y) \<le> h\<close>
  shows \<open>mc_height (mc_node x y) \<le> h\<close>
  by (meson assms le_trans mc_node_height_le)

lemma mc_node_left_right [simp]:
  assumes \<open>memory_contents_canonical x\<close>
  shows \<open>mc_node (mc_left x) (mc_right x) = x\<close>
proof (cases x)
  case (MC_node x11 x12)
  then show ?thesis
    unfolding memory_contents_canonical_def using assms by auto
qed auto

lemma mc_left_height:
  assumes \<open>mc_height x \<le> Suc h\<close>
  shows \<open>mc_height (mc_left x) \<le> h\<close>
  using assms by (cases x; clarsimp)

lemma mc_right_height:
  assumes \<open>mc_height x \<le> Suc h\<close>
  shows \<open>mc_height (mc_right x) \<le> h\<close>
  using assms by (cases x; clarsimp)

lemma memset_memory_block_height_le [intro]:
  assumes \<open>mc_height mc \<le> h\<close>
  shows \<open>mc_height (memset_memory_block mc h addr block_h b) \<le> h\<close>
using assms proof (induction mc h addr block_h b rule: memset_memory_block.induct)
  case (1 m h addr block_h b)
  then show ?case
    unfolding memset_memory_block.simps[of m]
    by (cases m; force intro!: order.trans[OF mc_node_height_le])
qed

lemma memset_memory_block_height_lt:
  assumes \<open>mc_height mc < h\<close>
  shows \<open>mc_height (memset_memory_block mc (h-1) addr block_h b) < h\<close>
  using assms memset_memory_block_height_le[where h=\<open>h-1\<close>]
  by (simp add: nat_le_Suc_less)

lemma canonical_mc_left [intro]:
  assumes \<open>memory_contents_canonical x\<close>
  shows \<open>memory_contents_canonical (mc_left x)\<close>
  using assms unfolding memory_contents_canonical_def
  by (cases x; auto elim: mc_node_eqE)

lemma canonical_mc_right [intro]:
  assumes \<open>memory_contents_canonical x\<close>
  shows \<open>memory_contents_canonical (mc_right x)\<close>
  using assms unfolding memory_contents_canonical_def
  by (cases x; auto elim: mc_node_eqE)

lemma mc_left_node [simp]:
  shows \<open>mc_left (mc_node x y) = x\<close>
  by (induction x y rule: mc_node.induct, auto)

lemma mc_right_node [simp]:
  shows \<open>mc_right (mc_node x y) = y\<close>
  by (induction x y rule: mc_node.induct, auto)

lemma mc_left_right_ext:
  assumes \<open>mc_left x = mc_left y\<close>
  and \<open>mc_right x = mc_right y\<close>
  and \<open>memory_contents_canonical x\<close>
  and \<open>memory_contents_canonical y\<close>
  shows \<open>x = y\<close>
using assms proof (induction x arbitrary: y)
  case (MC_node x1 x2)
  then show ?case
  by (cases y; simp add: memory_contents_canonical_def)
next                                                        
  case (MC_byte x)
  then show ?case
  by (cases y; auto simp add: memory_contents_canonical_def)
qed

lemma memory_contents_memset_lookup:
  assumes \<open>mc_height mc \<le> h\<close>
   and \<open>\<forall>n\<ge>block_h. n < h \<longrightarrow> (addr !! n = addr' !! n)\<close>
   shows \<open>lookup_memory_contents (memset_memory_block mc h addr block_h b) h addr' = b\<close>
using assms
proof (induction mc h addr block_h b rule: memset_memory_block.induct)
  case (1 m h addr block_h b)
  then show ?case
    using memset_memory_block_height_lt
    apply (auto simp add: memset_memory_block.simps [of m] lookup_memory_contents_mc_node; 
           subst lookup_memory_contents_mc_node; cases m)
    apply (auto split: nat_diff_split)
    done
qed

lemma memory_contents_memset_lookup_diff:
  assumes \<open>mc_height mc \<le> h\<close>
   and \<open>\<exists>n. n\<ge>block_h \<and> n < h \<and> addr !! n \<noteq> addr' !! n\<close>
   shows \<open>lookup_memory_contents (memset_memory_block mc h addr block_h b) h addr' = lookup_memory_contents mc h addr'\<close>
using assms
proof (induction mc h addr block_h b rule: memset_memory_block.induct)
  case (1 m h addr block_h b)
  then show ?case
    apply (auto simp: memset_memory_block.simps [of m])
    using memset_memory_block_height_lt
       apply (subst lookup_memory_contents_mc_node; cases m;
              auto simp: less_Suc_eq memset_memory_block_height_lt split: nat_diff_split_asm)+
    done
qed

section\<open>Trie-based representation of physical memory\<close>

datatype memory_fault
  = Unmapped_Address
  | Insufficient_Permissions
  | Translation_Fault

datatype 'tag memory_tree
  = MT_unmapped
  | MT_tagged \<open>nonempty_share\<close> 'tag \<open>memory_contents\<close>
  | MT_node \<open>'tag memory_tree\<close> \<open>'tag memory_tree\<close>

fun mt_height :: \<open>'tag memory_tree \<Rightarrow> nat\<close> where
  \<open>mt_height MT_unmapped = 0\<close> |
  \<open>mt_height (MT_tagged _ _ mc) = mc_height mc\<close> |
  \<open>mt_height (MT_node n0 n1) = 1 + max (mt_height n0) (mt_height n1)\<close>

fun lookup_memory_tree :: \<open>'tag memory_tree \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 'tag physical_byte_state\<close> where
  \<open>lookup_memory_tree MT_unmapped _ _ = Unmapped\<close> |
  \<open>lookup_memory_tree (MT_tagged sh tag mc) h addr = Tagged sh tag (lookup_memory_contents mc h addr)\<close> |
  \<open>lookup_memory_tree (MT_node n0 n1) 0 addr = Unmapped\<close> |
  \<open>lookup_memory_tree (MT_node n0 n1) (Suc h) addr =
     (if bit addr h then
       lookup_memory_tree n1 h addr
     else
       lookup_memory_tree n0 h addr)\<close>

subsection\<open>Canonical memory trees\<close>

fun mt_node :: \<open>'tag memory_tree \<Rightarrow> 'tag memory_tree \<Rightarrow> 'tag memory_tree\<close> where
  \<open>mt_node MT_unmapped MT_unmapped = MT_unmapped\<close> |
  \<open>mt_node (MT_tagged sh1 tag1 mc1) (MT_tagged sh2 tag2 mc2) =
     (if sh1 = sh2 \<and> tag1 = tag2 then MT_tagged sh1 tag1 (mc_node mc1 mc2) else MT_node (MT_tagged sh1 tag1 mc1) (MT_tagged sh2 tag2 mc2))\<close> |
  \<open>mt_node n0 n1 = MT_node n0 n1\<close>

fun canonicalize_memory_tree :: \<open>'tag memory_tree \<Rightarrow> 'tag memory_tree\<close> where
  \<open>canonicalize_memory_tree MT_unmapped = MT_unmapped\<close> |
  \<open>canonicalize_memory_tree (MT_tagged sh tag mc) = MT_tagged sh tag (canonicalize_memory_contents mc)\<close> |
  \<open>canonicalize_memory_tree (MT_node n0 n1) =
      mt_node (canonicalize_memory_tree n0) (canonicalize_memory_tree n1)\<close>

definition memory_tree_is_canonical :: \<open>'tag memory_tree \<Rightarrow> bool\<close> where
  \<open>memory_tree_is_canonical pm \<equiv> canonicalize_memory_tree pm = pm\<close>

lemma mt_node_eqE:
  assumes \<open>mt_node n0 n1 = MT_node n0' n1'\<close>
    and \<open>n0 = n0' \<Longrightarrow> n1 = n1' \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (induction n0 n1 rule: mt_node.induct, auto split: if_splits)

lemma canonical_mt_nodeE [elim]:
  assumes \<open>memory_tree_is_canonical (MT_node x y)\<close>
  obtains \<open>memory_tree_is_canonical x\<close> \<open>memory_tree_is_canonical y\<close> \<open>mt_node x y = MT_node x y\<close>
  using assms mt_node_eqE unfolding memory_tree_is_canonical_def
  by fastforce

lemma canonical_mt_node_iff:
  \<open>memory_tree_is_canonical (MT_node x y) \<longleftrightarrow> memory_tree_is_canonical x \<and> memory_tree_is_canonical y \<and> mt_node x y = MT_node x y\<close>
  by (metis canonical_mt_nodeE canonicalize_memory_tree.simps(3) memory_tree_is_canonical_def)

lemma mt_node_height_le:
  shows \<open>mt_height (mt_node n0 n1) \<le> mt_height (MT_node n0 n1)\<close>
  by (induction n0 n1 rule: mt_node.induct) (use mc_node_height_le in auto)

lemma mt_height_mt_nodeI [intro]:
  assumes \<open>mt_height (MT_node x y) \<le> h\<close>
  shows \<open>mt_height (mt_node x y) \<le> h\<close>
  by (meson assms le_trans mt_node_height_le)

lemma canonical_tagged [simp]:
  shows \<open>memory_tree_is_canonical (MT_tagged sh tag x) = memory_contents_canonical x\<close>
  unfolding memory_tree_is_canonical_def memory_contents_canonical_def by auto

lemma canonical_mt_nodeI [intro]:
  assumes \<open>memory_tree_is_canonical x\<close>
  and \<open>memory_tree_is_canonical y\<close>
  and \<open>mt_node x y = MT_node x y\<close>
  shows \<open>memory_tree_is_canonical (MT_node x y)\<close>
  using assms unfolding memory_tree_is_canonical_def by auto

lemma mt_node_unmappedE:
  assumes \<open>mt_node x y = MT_unmapped\<close>
  and \<open>x = MT_unmapped \<Longrightarrow> y = MT_unmapped \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (induction x y rule: mt_node.induct, auto split: if_splits)

lemma mt_node_unmapped_iff [iff]:
   \<open>mt_node x y = MT_unmapped \<longleftrightarrow> x = MT_unmapped \<and> y = MT_unmapped\<close>
  using mt_node.simps(1) mt_node_unmappedE by blast

lemma mt_node_taggedE:
  assumes \<open>mt_node x y = MT_tagged sh tag m\<close>
  and \<open>\<And>mx my. x = MT_tagged sh tag mx \<Longrightarrow> y = MT_tagged sh tag my \<Longrightarrow> m = mc_node mx my \<Longrightarrow> R\<close>
  shows \<open>R\<close>
  using assms by (induction x y rule: mt_node.induct, auto split: if_splits)

lemma mt_node_tagged_iff [iff]:
  \<open>mt_node x y = MT_tagged sh tag m \<longleftrightarrow> (\<exists>mx my. x = MT_tagged sh tag mx \<and> y = MT_tagged sh tag my \<and> m = mc_node mx my)\<close>
  by (meson mt_node.simps(2) mt_node_taggedE)

lemma mt_node_canonical:
  assumes \<open>memory_tree_is_canonical n0\<close>
  and \<open>memory_tree_is_canonical n1\<close>
  shows \<open>memory_tree_is_canonical (mt_node n0 n1)\<close>
  using assms mc_node_canonical
  unfolding memory_tree_is_canonical_def
  by (induction n0 n1 rule: mt_node.induct)
     (auto simp add: mc_node_canonical mc_node_commute)

lemma mt_canonicalize_correct:
  shows \<open>memory_tree_is_canonical (canonicalize_memory_tree mt)\<close>
  using mt_node_canonical mc_canonicalize_correct
  unfolding memory_tree_is_canonical_def memory_contents_canonical_def
  by (induction mt rule: canonicalize_memory_tree.induct) auto

lemma mt_node_commute:
  shows \<open>canonicalize_memory_tree (mt_node n0 n1) =
           mt_node (canonicalize_memory_tree n0) (canonicalize_memory_tree n1)\<close>
  by (induction n0 n1 rule: mt_node.induct, auto simp add: mc_node_commute)

lemma lookup_memory_tree_eq:
  assumes \<open>\<And>n. n < h \<Longrightarrow> addr!!n = addr'!!n\<close>
  shows \<open>lookup_memory_tree x h addr = lookup_memory_tree x h addr'\<close>
using assms by
  (induction x h addr arbitrary: addr' rule: lookup_memory_tree.induct;
   clarsimp simp add: lookup_memory_contents_eq)

lemma lookup_memory_tree_bound_eq:
  assumes \<open>\<And>addr. addr < 2^h \<Longrightarrow> lookup_memory_tree x h addr = lookup_memory_tree y h addr\<close>
   and \<open>h < 64\<close>
  shows \<open>lookup_memory_tree x h addr = lookup_memory_tree y h addr\<close>
proof -
  fix addr :: \<open>64 word\<close>
  obtain addr' where \<open>addr' = addr AND mask h\<close> by simp
  moreover have \<open>(mask h :: 64 word) < 2^h\<close>
    using assms by (simp add: mask_lt_2pn)
  moreover from calculation have \<open>addr' < 2^h\<close>
    using word_and_less' by clarsimp
  moreover from calculation have \<open>\<And>n. n < h \<Longrightarrow> addr!!n = addr'!!n\<close>
    by clarsimp (metis bit_take_bit_iff take_bit_eq_mask)
  ultimately show \<open>lookup_memory_tree x h addr = lookup_memory_tree y h addr\<close>
    using assms lookup_memory_tree_eq by (metis (no_types, lifting))
qed

lemma lookup_memory_tree_mt_node:
  assumes \<open>h > mt_height n0\<close> \<open>h > mt_height n1\<close>
  shows \<open>lookup_memory_tree (mt_node n0 n1) h addr = lookup_memory_tree (MT_node n0 n1) h addr\<close>
  using assms lookup_memory_contents_mc_node
  by (induction n0 n1 rule: mt_node.induct; cases h; simp)

lemma memory_tree_node_constant_aux:
  fixes x y h b
  assumes \<open>\<And>addr. state_to_class (lookup_memory_tree (MT_node x y) (Suc h) addr) = cl\<close>
    and \<open>h < 64\<close>
  shows \<open>\<And>addr. state_to_class (lookup_memory_tree x h addr) = cl\<close>
  and \<open>\<And>addr. state_to_class (lookup_memory_tree y h addr) = cl\<close>
proof -
  fix addr :: \<open>64 word\<close>
  obtain addr' where \<open>addr' = set_bit addr h False\<close> by simp
  moreover from this have \<open>state_to_class (lookup_memory_tree x h addr') = cl\<close>
    using assms by (metis bit_set_bit_iff_2n lookup_memory_tree.simps(4))
  ultimately show \<open>state_to_class (lookup_memory_tree x h addr) = cl\<close>
    using lookup_memory_tree_eq
    by (metis (no_types, lifting) nless_le test_bit_set_gen)
next
  fix addr :: \<open>64 word\<close>
  obtain addr' where \<open>addr' = set_bit addr h True\<close> by simp
  moreover from this have \<open>state_to_class (lookup_memory_tree y h addr') = cl\<close>
    using assms(1)[of addr'] \<open>h < 64\<close>
    by (clarsimp simp add: test_bit_set_gen size_word_def)
  ultimately show \<open>state_to_class (lookup_memory_tree y h addr) = cl\<close>
    using lookup_memory_tree_eq
    by (metis (no_types, lifting) not_less_iff_gr_or_eq test_bit_set_gen)
qed

lemma memory_tree_constant_class:
  assumes \<open>memory_tree_is_canonical mt\<close>
  and \<open>\<forall>addr. state_to_class (lookup_memory_tree mt h addr) = cl\<close>
  and \<open>mt_height mt \<le> h\<close>
  and \<open>h \<le> 64\<close>
  shows \<open>(\<exists>sh tag mc. mt = MT_tagged sh tag mc) \<or> mt = MT_unmapped\<close>
using assms proof (induction mt arbitrary: h)
  case (MT_node n0 n1)
  note IH = this
  moreover from IH have
    \<open>\<forall>addr. state_to_class (lookup_memory_tree n0 (h-1) addr) = cl\<close>
    using memory_tree_node_constant_aux[of n0 n1 \<open>h-1\<close> cl] by simp
  moreover from this have lookup_n0: \<open>state_to_class (lookup_memory_tree n0 (h-1) 0) = cl\<close>
    by simp
  moreover from calculation have
    \<open>\<forall>addr. state_to_class (lookup_memory_tree n1 (h-1) addr) = cl\<close>
    using memory_tree_node_constant_aux[of n0 n1 \<open>h-1\<close> cl] by simp
  moreover from this have lookup_n1: \<open>state_to_class (lookup_memory_tree n1 (h-1) 0) = cl\<close>
    by simp
  moreover from IH have \<open>mt_height n0 \<le> h - 1\<close> and \<open>mt_height n1 \<le> h - 1\<close>
    by simp+
  moreover from calculation have split0: \<open>(\<exists>sh tag mc. n0 = MT_tagged sh tag mc) \<or> n0 = MT_unmapped\<close>
    and split1: \<open>(\<exists>sh tag mc. n1 = MT_tagged sh tag mc) \<or> n1 = MT_unmapped\<close>
    by auto
  from split0 split1 IH lookup_n0 lookup_n1 show ?case
    by (force simp add: map_shareable_value_def)
qed auto

lemma lookup_memory_tree_node_eqE:
  assumes H: \<open>\<And>addr. lookup_memory_tree (MT_node a b) (Suc h) addr = lookup_memory_tree (MT_node x y) (Suc h) addr\<close>
  and \<open>h < 64\<close>
  obtains \<open>\<forall>addr. lookup_memory_tree a h addr = lookup_memory_tree x h addr\<close>
          \<open>\<forall>addr. lookup_memory_tree b h addr = lookup_memory_tree y h addr\<close>
proof -
  have \<open>lookup_memory_tree a h addr = lookup_memory_tree x h addr\<close> for addr :: \<open>64 word\<close>
    using H[of \<open>set_bit addr h False\<close>] lookup_memory_tree_eq [of h addr \<open>set_bit addr h False\<close>, where ?'a='a]
    by (simp add: test_bit_set_gen)
  moreover
  have \<open>lookup_memory_tree b h addr = lookup_memory_tree y h addr\<close> for addr :: \<open>64 word\<close>
    using H[of \<open>set_bit addr h True\<close>] lookup_memory_tree_eq [of h addr \<open>set_bit addr h True\<close>, where ?'a='a] \<open>h < 64\<close>
    by (simp add: test_bit_set_gen size_word_def)
  ultimately show thesis
    using that by blast
qed

theorem memory_tree_unique:
  assumes \<open>memory_tree_is_canonical mt1\<close>
   and \<open>memory_tree_is_canonical mt2\<close>
   and \<open>mt_height mt1 \<le> h\<close>
   and \<open>mt_height mt2 \<le> h\<close>
   and \<open>h \<le> 64\<close>
   and \<open>\<And>addr. lookup_memory_tree mt1 h addr = lookup_memory_tree mt2 h addr\<close>
   shows \<open>mt1 = mt2\<close>
using assms proof (induction mt1 arbitrary: h mt2)
  case MT_unmapped
  then show ?case
  using memory_tree_constant_class[of mt2 h No_Value] by auto
next
  case (MT_tagged sh tag x)
  moreover from this and assms have \<open>\<forall>addr. lookup_memory_tree mt2 h addr = Shared_Value sh (tag, lookup_memory_contents x h addr)\<close>
    by auto
  moreover from this have H: \<open>\<forall>addr. state_to_class (lookup_memory_tree mt2 h addr) = Shared_Value sh tag\<close>
    by auto
  moreover from this obtain tag y where \<open>mt2 = MT_tagged sh tag y\<close>
    using memory_tree_constant_class[of mt2 h \<open>Shared_Value sh tag\<close>, OF \<open>memory_tree_is_canonical mt2\<close> H \<open>mt_height mt2 \<le> h\<close> \<open>h \<le> 64\<close>]
    by auto
  ultimately show ?case
    using memory_contents_unique by (clarsimp simp add: memory_tree_is_canonical_def memory_contents_canonical_def)
next
  case (MT_node n0 n1)
  then have *: \<open>MT_node n0 n1 = mt2\<close> if \<open>mt2 = MT_node x y\<close> and \<open>h = Suc h'\<close> for  x y h'
    using that apply (clarsimp elim!: canonical_mt_nodeE)
    by (rule lookup_memory_tree_node_eqE[of n0 n1 h' x y]; simp)
  show ?case
  proof (cases mt2)
    case MT_unmapped
    then show ?thesis
    using MT_node memory_tree_constant_class[of \<open>MT_node n0 n1\<close> h No_Value]
    by auto
  next
    case (MT_tagged sh tag y)
    then show ?thesis 
    using MT_node memory_tree_constant_class[of \<open>MT_node n0 n1\<close> h \<open>Shared_Value sh tag\<close>]
    by auto
  next
    case (MT_node x y)
    with * MT_node.prems(4) Suc_le_D show ?thesis
      by force
  qed
qed

subsection\<open>Claiming a physical page of memory\<close>

\<comment>\<open>Given raw memory contents and a 2-power address range, builds a memory tree
which has a given tag within the range, and another tag outside of the range.\<close>
fun tag_memory_contents ::
  \<open>memory_contents \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> nonempty_share \<Rightarrow> 'tag \<Rightarrow> 'tag \<Rightarrow> 'tag memory_tree\<close> where
  \<open>tag_memory_contents mc h addr block_h sh tag_in tag_out =
    (if h > block_h then
      (if bit addr (h-1) then
         MT_node (MT_tagged sh tag_out (mc_left mc))
                 (tag_memory_contents (mc_right mc) (h-1) addr block_h sh tag_in tag_out)
       else
         MT_node (tag_memory_contents (mc_left mc) (h-1) addr block_h sh tag_in tag_out)
                 (MT_tagged sh tag_out (mc_right mc)))
    else
      MT_tagged sh tag_in mc)\<close>

lemma tag_memory_contents_height_le:
  notes tag_memory_contents.simps[simp del]
  assumes \<open>mc_height mc \<le> h\<close>
  shows \<open>mt_height (tag_memory_contents mc h addr block_h sh tag_in tag_out) \<le> h\<close>
using assms proof (induction mc h addr block_h sh tag_in tag_out rule: tag_memory_contents.induct)
  case (1 mc h addr block_h)
  then show ?case
    by (subst tag_memory_contents.simps; cases mc; force split: if_splits)
qed

lemma tag_memory_contents_height_lt:
  notes tag_memory_contents.simps[simp del]
  assumes \<open>mc_height mc < h\<close>
  shows \<open>mt_height (tag_memory_contents mc (h-1) addr block_h sh tag_in tag_out) < h\<close>
  by (metis One_nat_def assms nat_le_Suc_less not_less0 not_less_iff_gr_or_eq tag_memory_contents_height_le)

lemma tag_memory_contents_mt_node:
  assumes \<open>tag_in \<noteq> tag_out\<close>
  shows \<open>mt_node (MT_tagged sh' tag_out mc') (tag_memory_contents mc h addr block_h sh tag_in tag_out) =
         MT_node (MT_tagged sh' tag_out mc') (tag_memory_contents mc h addr block_h sh tag_in tag_out)\<close>
    and \<open>mt_node (tag_memory_contents mc h addr block_h sh tag_in tag_out) (MT_tagged sh' tag_out mc')  =
         MT_node (tag_memory_contents mc h addr block_h sh tag_in tag_out) (MT_tagged sh' tag_out mc')\<close>
  using assms by (cases \<open>tag_memory_contents mc h addr block_h sh tag_in tag_out\<close>, auto split: if_splits)

lemma tag_memory_contents_canonical:
  notes tag_memory_contents.simps[simp del]
  assumes \<open>tag_in \<noteq> tag_out\<close>
  assumes \<open>memory_contents_canonical mc\<close>
  shows \<open>memory_tree_is_canonical (tag_memory_contents mc h addr block_h sh tag_in tag_out)\<close>
using assms proof (induction mc h addr block_h sh tag_in tag_out rule: tag_memory_contents.induct)
  case (1 mc h addr block_h tag_in tag_out)
  then show ?case
    unfolding tag_memory_contents.simps [of mc]
    by (simp add: canonical_mc_left canonical_mc_right canonical_mt_nodeI tag_memory_contents_mt_node) 
qed

lemma tag_memory_contents_result:
  notes tag_memory_contents.simps[simp del]
  shows
  \<open>lookup_memory_tree (tag_memory_contents mc h addr block_h sh tag_in tag_out) h x =
    (if x \<in> bits_range addr h block_h then Tagged sh tag_in (lookup_memory_contents mc h x) else Tagged sh tag_out (lookup_memory_contents mc h x))\<close>
proof (induction h arbitrary: mc)
  case 0
  then show ?case
    by (subst tag_memory_contents.simps, auto simp add: bits_range_def)
next
  case (Suc h)
  then show ?case
    unfolding tag_memory_contents.simps [of mc]
    by (cases mc; simp add: bits_range_split)
qed

fun memory_tree_tag_page ::
  \<open>'tag memory_tree \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 'tag \<Rightarrow> memory_fault + 'tag memory_tree\<close> where
  \<open>memory_tree_tag_page MT_unmapped h addr block_h tag_new = Inl Unmapped_Address\<close> |
  \<open>memory_tree_tag_page (MT_tagged sh tag_old mc) h addr block_h tag_new =
    (if Rep_nonempty_share sh = \<top> \<and> tag_new \<noteq> tag_old then
       Inr (tag_memory_contents mc h addr block_h sh tag_new tag_old)
     else
       \<comment>\<open>TODO: Why do we error here, rather than just making it a no-op?\<close>
       Inl Insufficient_Permissions)\<close> |
  \<open>memory_tree_tag_page (MT_node n0 n1) h addr block_h tag_new =
    (if h > block_h then
       (if bit addr (h-1) then
         (case memory_tree_tag_page n1 (h-1) addr block_h tag_new of
            Inl e \<Rightarrow> Inl e
          | Inr n1' \<Rightarrow> Inr (mt_node n0 n1'))
        else
         (case memory_tree_tag_page n0 (h-1) addr block_h tag_new of
            Inl e \<Rightarrow> Inl e
          | Inr n0' \<Rightarrow> Inr (mt_node n0' n1)))
     else
       (case memory_tree_tag_page n0 (h-1) addr block_h tag_new of
          Inr n0' \<Rightarrow>
            (case memory_tree_tag_page n1 (h-1) addr block_h tag_new of
              Inr n1' \<Rightarrow> Inr (mt_node n0' n1')
            | Inl e \<Rightarrow> Inl e)
        | Inl e \<Rightarrow> Inl e))\<close>

lemma memory_tree_tag_page_height_le:
  notes tag_memory_contents.simps[simp del]
  assumes \<open>mt_height mt \<le> h\<close>
  and \<open>memory_tree_tag_page mt h addr block_h tag = Inr mt'\<close>
  shows \<open>mt_height mt' \<le> h\<close>
  using assms
proof (induction mt h addr block_h tag arbitrary: mt' rule: memory_tree_tag_page.induct)
  case (1 h addr block_h tag_new)
  then show ?case by clarsimp
next
  case (2 sh tag_old mc h addr block_h tag_new)
  then show ?case by (cases \<open>tag_new = tag_old\<close>;
    cases \<open>Rep_nonempty_share sh = \<top>\<close>; clarsimp simp add: tag_memory_contents_height_le)
next
  case (3 n0 n1 h addr block_h tag_new)
  show ?case
  \<comment> \<open>This is all very fiddly. Bringing in all the induction hyps makes simp go crazy.\<close>
  using "3.prems"
  apply (elim memory_tree_tag_page.elims; simp split: if_splits sum.splits)
  apply (rule order.trans[OF mt_node_height_le]; use "3.IH" in fastforce)+
  done
qed

lemma memory_tree_tag_page_height_lt:
  notes tag_memory_contents.simps[simp del]
  assumes \<open>mt_height mt < h\<close>
  and \<open>memory_tree_tag_page mt (h-1) addr block_h tag = Inr mt'\<close>
shows \<open>mt_height mt' < h\<close>
  using assms memory_tree_tag_page_height_le
  by (metis One_nat_def less_nat_zero_code nat_le_Suc_less nat_neq_iff)

lemma memory_tree_tag_page_canonical:
  notes tag_memory_contents.simps[simp del]
  assumes \<open>memory_tree_is_canonical mt\<close>
  and \<open>memory_tree_tag_page mt h addr block_h tag = Inr mt'\<close>
  shows \<open>memory_tree_is_canonical mt'\<close>
using assms proof (induction mt h addr block_h tag arbitrary: mt' rule: memory_tree_tag_page.induct)
  case (2 sh tag_old mc h addr block_h tag_new)
  then obtain \<open>Rep_nonempty_share sh = \<top>\<close> \<open>tag_old \<noteq> tag_new\<close>
    by (metis Inl_Inr_False memory_tree_tag_page.simps(2))
  with 2 show ?case
    by (auto simp add: tag_memory_contents_canonical)
next
  case (3 n0 n1 h addr block_h tag_new)
  show ?case
  using "3.prems"   \<comment> \<open>Again we don't need or want the induction hyps yet.\<close>
  apply (auto elim!: mt_node_eqE
              simp add: mt_node_commute memory_tree_is_canonical_def
              split: if_splits sum.splits)
  using "3.IH" unfolding memory_tree_is_canonical_def by simp_all
qed auto

definition is_owned_with_other_tag :: \<open>'tag \<Rightarrow> 'tag physical_byte_class \<Rightarrow> bool\<close> where
  \<open>is_owned_with_other_tag tag c \<equiv>
     case c of
        No_Value \<Rightarrow> False
      | Shared_Value sh tag' \<Rightarrow> Rep_nonempty_share sh = \<top> \<and> tag \<noteq> tag'\<close>

lemma is_owned_with_other_tagE:
  assumes \<open>is_owned_with_other_tag tag c\<close>
  and \<open>\<And>tag'. tag \<noteq> tag' \<Longrightarrow> c = Shared_Value \<top> tag' \<Longrightarrow> R\<close>
shows R
  using assms by (auto simp add: nonempty_share_top_eq is_owned_with_other_tag_def split!: shareable_value.splits)

lemma memory_tree_tag_page_succeeds1:
  assumes \<open>\<forall>x \<in> bits_range addr h block_h. x<2^h \<longrightarrow> is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mt h x))\<close>
  and \<open>h < 64\<close> and \<open>mt_height mt \<le> h\<close> and \<open>memory_tree_is_canonical mt\<close>
  shows \<open>\<exists>mt'. memory_tree_tag_page mt h addr block_h tag = Inr mt'\<close>
using assms proof (induction mt arbitrary: h addr)
  case MT_unmapped
  then have \<open>\<not> is_owned_with_other_tag tag No_Value\<close>
    by (meson bits_range_inh is_owned_with_other_tagE shareable_value.simps(3))
    with MT_unmapped show ?case
  using Suc bits_range_inh[of \<open>Suc h\<close> addr] bits_range_inh
  by (force elim!: is_owned_with_other_tagE)
next
  case MT_tagged
  then show ?case
    by clarsimp
      (metis bits_range_inh is_owned_with_other_tagE shareable_value.inject  top_nonempty_share.rep_eq)
next
  case (MT_node mt1 mt2)
  let ?h' = \<open>h - 1\<close>
  let ?mt = \<open>MT_node mt1 mt2\<close>
  have  can1: \<open>memory_tree_is_canonical mt1\<close>
    and can2: \<open>memory_tree_is_canonical mt2\<close>
    using MT_node.prems(4) by blast+
  moreover from MT_node(5) have
    h_suc: \<open>h = Suc ?h'\<close> by simp
  moreover from \<open>h < 64\<close> have h1: \<open>?h' < 64\<close>
    by simp
  { assume b1: \<open>addr !! ?h' = False \<or> h \<le> block_h\<close>
    { fix x assume \<open>x \<in> bits_range addr ?h' block_h\<close> and \<open>x < 2^?h'\<close>
      moreover from \<open>x < 2^?h'\<close> have \<open>x !! ?h' = False\<close>
        using bang_is_le leD by blast
      moreover from this and \<open>x \<in> bits_range addr ?h' block_h\<close> and b1 have \<open>x \<in> bits_range addr h block_h\<close>
        by (metis Suc_le_eq bits_range_Suc h_suc)
      moreover from this have \<open>lookup_memory_tree mt1 ?h' x = lookup_memory_tree ?mt h x\<close>
        by (metis calculation(3) h_suc lookup_memory_tree.simps(4))
      moreover have \<open>x < 2^h\<close>
        by (metis MT_node.prems(2) Suc_mask_eq_mask bits_range_inh
            calculation(2) calculation(3) h_suc less_mask_eq)
      ultimately have \<open>is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mt1 ?h' x))\<close>
        using MT_node.prems(1) by force
    }
    moreover have \<open>mt_height mt1 \<le> ?h'\<close>
      by (metis MT_node.prems(3) h_suc max.bounded_iff mt_height.simps(3)
        not_less_eq_eq plus_1_eq_Suc)
    ultimately have \<open>\<exists>mt1'. memory_tree_tag_page mt1 ?h' addr block_h tag = Inr mt1'\<close>
      using MT_node.IH(1) can1 h1 by blast
  }
  moreover {
    assume b1: \<open>addr !! ?h' = True \<or> h \<le> block_h\<close>
    { fix x assume \<open>x \<in> bits_range addr ?h' block_h\<close> and \<open>x < 2^?h'\<close>
      note X = this
      let ?x' = \<open>set_bit x ?h' True\<close>
      note X
      moreover have \<open>?x' !! ?h' = True\<close>
        by (metis bit_set_bit_iff_2n calculation(2) dual_order.strict_implies_not_eq word_gt_a_gt_0)
      moreover from this and \<open>x \<in> bits_range addr ?h' block_h\<close> and b1 have \<open>?x' \<in> bits_range addr h block_h\<close>
        by (subst h_suc; clarsimp simp add: bits_range_def test_bit_set_gen)
      moreover have \<open>lookup_memory_tree mt2 ?h' x = lookup_memory_tree mt2 ?h' ?x'\<close>
        using \<open>h < 64\<close> by (intro lookup_memory_tree_eq; auto simp add: bit_simps )
      moreover from this have \<open>lookup_memory_tree mt2 ?h' ?x' = lookup_memory_tree ?mt h ?x'\<close>
        by (metis calculation(3) h_suc lookup_memory_tree.simps(4))
      moreover have \<open>?x' < 2^h\<close>
        by (metis (no_types, lifting) MT_node.prems(2) bits_range_inh calculation(2)
          h_suc less_2p_is_upper_bits_unset less_Suc_eq linorder_not_less test_bit_set_gen)
      ultimately have \<open>is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mt2 ?h' x))\<close>
        using MT_node.prems(1) by auto
    }
    moreover have \<open>mt_height mt2 \<le> ?h'\<close>
      by (metis MT_node.prems(3) h_suc max.bounded_iff mt_height.simps(3)
        not_less_eq_eq plus_1_eq_Suc)
    ultimately have \<open>\<exists>m2'. memory_tree_tag_page mt2 ?h' addr block_h tag = Inr m2'\<close>
      using MT_node.IH(2) can2 h1 by blast
  }
  ultimately show ?case
    by auto
qed

lemma memory_tree_tag_page_fails:
  notes tag_memory_contents.simps[simp del]
  assumes \<open>memory_tree_tag_page mt h addr block_h tag = Inl e\<close>
  and \<open>h < 64\<close> and \<open>mt_height mt \<le> h\<close> and \<open>memory_tree_is_canonical mt\<close>
shows \<open>\<exists>x \<in> bits_range addr h block_h. x<2^h \<and> \<not> is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mt h x))\<close>
  using assms memory_tree_tag_page_succeeds1 by force

lemma sum_if_cases: \<open>\<And>P x y y'. (if P then Inr y else Inl x) = Inr y' \<longleftrightarrow> (P \<and> (y = y'))\<close>
  by auto

lemma memory_tree_tag_page_result:
  notes tag_memory_contents.simps[simp del]
  assumes \<open>memory_tree_tag_page mt h addr block_h tag = Inr mt'\<close>
  and \<open>mt_height mt \<le> h\<close>
  shows \<open>lookup_memory_tree mt' h x =
           (if x \<in> bits_range addr h block_h then tag_byte_state tag (lookup_memory_tree mt h x) else lookup_memory_tree mt h x)\<close>
using assms
proof (induction mt h addr block_h tag arbitrary: mt' rule: memory_tree_tag_page.induct)
  case (1 h addr block_h tag)
  then show ?case by clarsimp
next
  case (2 mc h addr block_h tag)
  then show ?case
    by (force simp add: sum_if_cases tag_memory_contents_result split: if_splits)
next
  case (3 n0 n1 h addr block_h tag)
  then show ?case
    apply (auto split: if_splits sum.splits nat_diff_split_asm; use memory_tree_tag_page_height_le in \<open>subst lookup_memory_tree_mt_node\<close>)
     apply (fastforce simp: bits_range_def)+
    done
qed


lemma memory_tree_tag_page_succeeds2:
  assumes
    \<open>h < 64\<close>
    \<open>memory_tree_is_canonical mt\<close>
    \<open>x \<in> bits_range addr h block_h\<close>
    \<open>x < 2 ^ h\<close>
    \<open>\<not> is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mt h x))\<close>
    \<open>mt_height mt \<le> h\<close>
  shows
    \<open>\<exists>e. memory_tree_tag_page mt h addr block_h tag = Inl e\<close>
  using assms proof (induction mt arbitrary: h x)
  case MT_unmapped
  then show ?case by clarsimp
next
  case MT_tagged
  then show ?case
    using nonempty_share_top_eq by (simp add: is_owned_with_other_tag_def)
next
  case (MT_node mt1 mt2)
  let ?h' = \<open>h-1\<close>
  let ?mt = \<open>MT_node mt1 mt2\<close>
  have mt1h: \<open>mt_height mt1 \<le> ?h'\<close>
    by (metis MT_node.prems(6) One_nat_def Suc_le_lessD max.bounded_iff mt_height.simps(3)
        nat_le_Suc_less_imp plus_1_eq_Suc)
  have mt2h: \<open>mt_height mt2 \<le> ?h'\<close>
    by (metis MT_node.prems(6) One_nat_def Suc_le_lessD max.bounded_iff mt_height.simps(3)
        nat_le_Suc_less_imp plus_1_eq_Suc)
  have mt1c: \<open>memory_tree_is_canonical mt1\<close>
    and mt2c:\<open>memory_tree_is_canonical mt2\<close>
    using MT_node.prems(2) by blast+
  moreover have h_suc: \<open>h = Suc ?h'\<close> \<open>h>0\<close>
    using MT_node.prems(6) by auto
  have hl: \<open>?h' < 64\<close>
    using MT_node.prems(1) less_imp_diff_less by presburger
  have A: \<open>\<exists>e. memory_tree_tag_page mt1 ?h' addr block_h tag = Inl e\<close>
    if \<open>x !! ?h' = False\<close>
  proof -
    from \<open>x \<in> bits_range addr h block_h\<close> h_suc have
      \<open>lookup_memory_tree ?mt h x = lookup_memory_tree mt1 ?h' x\<close>
      by (metis lookup_memory_tree.simps(4) that)
    moreover have \<open>x < 2^?h'\<close>
      using \<open>?h' < 64\<close> \<open>x !! ?h' = False\<close> h_suc
      by (metis MT_node.prems(4) Suc_mask_eq_mask bits_range_inh less_mask_eq)
    moreover from \<open>x \<in> bits_range addr h block_h\<close> have \<open>x \<in> bits_range addr ?h' block_h\<close>
      by (clarsimp simp add: bits_range_def)
    ultimately show ?thesis
      using  MT_node.prems(5) by (intro MT_node(1)[OF hl mt1c _ _ _ mt1h, where x=x]; clarsimp)
  qed
  have B: \<open>\<exists>e. memory_tree_tag_page mt2 ?h' addr block_h tag = Inl e\<close>
    if \<open>x !! ?h' = True\<close>
  proof -
    let ?x' = \<open>set_bit x ?h' False\<close>
    note \<open>x !! ?h' = True\<close>
    moreover from this have \<open>lookup_memory_tree ?mt h x = lookup_memory_tree mt2 ?h' x\<close>
      by (subst h_suc; clarsimp)
    moreover have \<open>lookup_memory_tree mt2 ?h' x = lookup_memory_tree mt2 ?h' ?x'\<close>
      by (intro lookup_memory_tree_eq) (simp add: bit_set_bit_word_iff)
    moreover have \<open>?x' < 2^?h'\<close>
      using \<open>?h' < 64\<close> \<open>x < 2 ^ h\<close>
      by (simp add: less_2p_is_upper_bits_unset test_bit_set_gen)
    moreover from \<open>x \<in> bits_range addr h block_h\<close> have \<open>?x' \<in> bits_range addr ?h' block_h\<close>
      using \<open>h < 64\<close> by (clarsimp simp add: bits_range_def bit_simps)
    moreover from calculation have \<open>\<not> (is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mt2 ?h' ?x')))\<close>
      using MT_node.prems(5) by argo
    ultimately show ?thesis
      thm MT_node(2)[OF hl mt2c _ _ _ mt2h]
      using  MT_node.prems(5) by (intro MT_node(2)[OF hl mt2c _ _ _ mt2h, where x=\<open>?x'\<close>]; clarsimp)
  qed
  {
    assume \<open>block_h < h\<close>
    with \<open>x \<in> bits_range addr h block_h\<close> have \<open>x !! ?h' = addr !! ?h'\<close>
      by (clarsimp simp add: bits_range_def)
    with \<open>block_h < h\<close> have ?case
      using A B by (cases \<open>addr !! ?h'\<close>) auto
  }
  moreover {
    assume \<open>h \<le> block_h\<close>
    with A B have ?case
      by (cases \<open>x !! ?h'\<close>) (auto split!: sum.splits)
  }
  ultimately show ?case
    by simp
qed

lemma memory_tree_tag_page_succeeds:
  assumes
    \<open>h < 64\<close>
    \<open>memory_tree_is_canonical mt\<close>
    \<open>mt_height mt \<le> h\<close>
  shows
    \<open>(\<forall>x \<in> bits_range addr h block_h. x < 2 ^ h \<longrightarrow>
        is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mt h x)))
      \<longleftrightarrow> (\<exists>mt'. memory_tree_tag_page mt h addr block_h tag = Inr mt')\<close>
  using assms memory_tree_tag_page_succeeds1 memory_tree_tag_page_succeeds2 by fastforce

lemma memory_tree_tag_page_prestate:
  assumes \<open>memory_tree_tag_page mt h addr block_h tag = Inr mt'\<close>
  and \<open>mt_height mt \<le> h\<close>
  and \<open>memory_tree_is_canonical mt\<close>
  and \<open>x \<in> bits_range addr h block_h\<close>
  and \<open>h < 64\<close>
  and \<open>x < 2^h\<close>
  shows \<open>is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mt h x))\<close>
  using memory_tree_tag_page_succeeds2 by (metis Inl_Inr_False assms)

subsection\<open>Memset a block of physical memory\<close>

text\<open>This operation sets an entire aligned block of \<^verbatim>\<open>2^h\<close> bytes
to contain a specific value. In the degenerate case, where \<^verbatim>\<open>h=0\<close>, this
writes a single byte.\<close>

fun memset_memory_tree_block ::
  \<open>'tag memory_tree \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 8 word \<Rightarrow> memory_fault + 'tag memory_tree\<close> where
  \<open>memset_memory_tree_block MT_unmapped h addr block_h b = Inl Unmapped_Address \<close> |
  \<open>memset_memory_tree_block (MT_tagged sh tag mc) h addr block_h b =
    (if Rep_nonempty_share sh = \<top> then
       Inr (MT_tagged sh tag (memset_memory_block mc h addr block_h b))
     else
       Inl Insufficient_Permissions)\<close> |
  \<open>memset_memory_tree_block (MT_node n0 n1) h addr block_h b =
    (if h > block_h then
      (if bit addr (h-1) then
        (case memset_memory_tree_block n1 (h-1) addr block_h b of
           Inr n1' \<Rightarrow> Inr (mt_node n0 n1')
         | Inl e \<Rightarrow> Inl e)
       else
        (case memset_memory_tree_block n0 (h-1) addr block_h b of
           Inr n0' \<Rightarrow> Inr (mt_node n0' n1)
         | Inl e \<Rightarrow> Inl e))
     else
       (case memset_memory_tree_block n0 (h-1) addr block_h b of
          Inr n0' \<Rightarrow>
            (case memset_memory_tree_block n1 (h-1) addr block_h b of
              Inr n1' \<Rightarrow> Inr (mt_node n0' n1')
            | Inl e \<Rightarrow> Inl e)
        | Inl e \<Rightarrow> Inl e))\<close>

lemma memset_memory_tree_block_canonical:
  assumes \<open>memory_tree_is_canonical mt\<close>
    and \<open>memset_memory_tree_block mt h addr block_h b = Inr mt'\<close>
  shows \<open>memory_tree_is_canonical mt'\<close>
  using assms proof (induction mt h addr block_h b arbitrary: mt' rule: memset_memory_tree_block.induct)
  case (1 h addr block_h b)
  then show ?case by clarsimp
next
  case (2 mc h addr block_h b)
  then show ?case
    by (metis memset_memory_block_canonical canonical_tagged memset_memory_tree_block.simps(2) sum_if_cases)
next
  case (3 n0 n1 h addr block_h b)
  show ?case
    using "3.prems"  
    apply (auto elim!: mt_node_eqE simp add: mt_node_commute memory_tree_is_canonical_def split: if_splits sum.splits)
    using "3.IH" unfolding memory_tree_is_canonical_def by simp_all
qed

definition memory_tree_write ::
  \<open>'tag memory_tree \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow> memory_fault + 'tag memory_tree\<close> where
  \<open>memory_tree_write mt addr b \<equiv>
     memset_memory_tree_block mt PMEM_TRIE_ADDRESS_WIDTH addr 0 b\<close>

lemma memset_memory_tree_block_height_le:
  assumes \<open>mt_height mt \<le> h\<close>
  and \<open>memset_memory_tree_block mt h addr block_h b = Inr mt'\<close>
  shows \<open>mt_height mt' \<le> h\<close>
using assms proof (induction mt h addr block_h b arbitrary: mt' rule: memset_memory_tree_block.induct)
  case (1 h addr block_h b)
  then show ?case by clarsimp
next
  case (2 mc h addr block_h b)
  then show ?case
    by (metis Inl_Inr_False Inr_inject memset_memory_block_height_le 
        memset_memory_tree_block.simps(2) mt_height.simps(2))
next
  case (3 n0 n1 h addr block_h b)
  show ?case
  \<comment> \<open>This is all very fiddly. Bringing in all the induction hyps makes simp go crazy.\<close>
  using "3.prems"
  apply (elim memset_memory_tree_block.elims; simp split: if_splits sum.splits)
  apply (rule order.trans[OF mt_node_height_le]; use "3.IH" in fastforce)+
  done
qed

lemma memset_memory_tree_block_height_lt:
  assumes \<open>mt_height mt < h\<close>
  and \<open>memset_memory_tree_block mt (h-1) addr block_h b = Inr mt'\<close>
  shows \<open>mt_height mt' < h\<close>
  using assms memset_memory_tree_block_height_le
  by (metis less_nat_zero_code nat_le_Suc_less nat_neq_iff numeral_nat(7))

lemma memory_tree_memset_block_lookup:
  assumes \<open>memset_memory_tree_block mt h addr block_h b = Inr mt'\<close>
  and \<open>mt_height mt \<le> h\<close>
  and \<open>\<forall>n. block_h \<le> n \<longrightarrow> n < h \<longrightarrow> addr!!n = addr'!!n\<close>
  shows \<open>case lookup_memory_tree mt' h addr' of
           Shared_Value sh (tag, x) \<Rightarrow> \<top> \<le> Rep_nonempty_share sh \<and> x = b
         | No_Value \<Rightarrow> False\<close>
using assms
proof (induction mt h addr block_h b arbitrary: mt' rule: memset_memory_tree_block.induct)
  case (1 h addr block_h b)
  then show ?case by clarsimp
next
  case (2 mc h addr block_h b)
  then show ?case
    by (auto simp add: sum_if_cases memory_contents_memset_lookup)
next
  case (3 n0 n1 h addr block_h b)
  then show ?case
    apply (auto split: if_splits sum.splits)
      apply (subst lookup_memory_tree_mt_node;
        auto simp: le_neq_implies_less less_Suc_eq memset_memory_tree_block_height_le split: nat_diff_split_asm)+
    done
qed

lemma memory_tree_memset_block_lookup_diff:
  assumes \<open>memset_memory_tree_block mt h addr block_h b = Inr mt'\<close>
  and \<open>mt_height mt \<le> h\<close>
  and \<open>\<exists>n. block_h \<le> n \<and> n < h \<and> addr!!n \<noteq> addr'!!n\<close>
  shows \<open>lookup_memory_tree mt' h addr' = lookup_memory_tree mt h addr'\<close>
using assms
proof (induction mt h addr block_h b arbitrary: mt' rule: memset_memory_tree_block.induct)
  case (1 h addr block_h b)
  then show ?case by clarsimp
next
  case (2 mc h addr block_h b)
  then show ?case
    by (clarsimp intro!: memory_contents_memset_lookup_diff simp add: sum_if_cases, force)
next
  case (3 n0 n1 h addr block_h b)
  show ?case
    using "3.prems"
    apply (auto split: if_splits sum.splits nat_diff_split_asm; subst lookup_memory_tree_mt_node)
    using "3.IH"  apply (auto simp: less_Suc_eq_le memset_memory_tree_block_height_le)
    using order_le_less apply blast+
  done
qed

lemma memory_tree_memset_block_lookup_class:
  assumes \<open>memset_memory_tree_block mt h addr block_h b = Inr mt'\<close>
  and \<open>mt_height mt \<le> h\<close>
  shows \<open>state_to_class (lookup_memory_tree mt' h addr') = state_to_class (lookup_memory_tree mt h addr')\<close>
using assms
proof (induction mt h addr block_h b arbitrary: mt' rule: memset_memory_tree_block.induct)
  case (1 h addr block_h b)
  then show ?case by clarsimp
next
  case (2 mc h addr block_h b)
  then show ?case by (clarsimp simp add: sum_if_cases)
next
  case (3 n0 n1 h addr block_h b)
  show ?case
    using "3.prems"
    apply (auto split: if_splits sum.splits nat_diff_split_asm; subst lookup_memory_tree_mt_node)
    using "3.IH" by (auto simp: less_Suc_eq_le memset_memory_tree_block_height_le)
qed

lemma memory_tree_memset_block_succeeds1:
  assumes
    \<open>h < 64\<close>
    \<open>memory_tree_is_canonical mt\<close>
    \<open>\<forall>x \<in> bits_range addr h block_h. x < 2 ^ h \<longrightarrow> writeable_byte_state (lookup_memory_tree mt h x)\<close>
    \<open>mt_height mt \<le> h\<close>
  shows
    \<open>\<exists>mt'. memset_memory_tree_block mt h addr block_h b = Inr mt'\<close>
using assms proof(induction mt arbitrary: h addr)
  case MT_unmapped
  then show ?case
    using bits_range_inh by (clarsimp, blast)
next
  case (MT_tagged x1 x2 x3)
  then show ?case
    using bits_range_inh nonempty_share_top_eq by (clarsimp, blast)
next
  case (MT_node mt1 mt2)
  let ?h' = \<open>h - 1\<close>
  let ?mt = \<open>MT_node mt1 mt2\<close>
  from \<open>memory_tree_is_canonical mt\<close> have
    can1: \<open>memory_tree_is_canonical mt1\<close>
    and can2: \<open>memory_tree_is_canonical mt2\<close>
    using MT_node.prems(2) by blast+
  moreover from MT_node(6) have
    h_suc: \<open>h = Suc ?h'\<close> by simp
  moreover from \<open>h < 64\<close> have h1: \<open>?h' < 64\<close>
    by simp
  note IHl = MT_node(1)[of \<open>?h'\<close>, OF h1 can1]
   and IHr = MT_node(2)[of \<open>?h'\<close>, OF h1 can2]
   and mapped = MT_node(5)
  have \<open>\<exists>mt1'. memset_memory_tree_block mt1 ?h' addr block_h b = Inr mt1'\<close>
    if b1: \<open>addr !! ?h' = False \<or> h \<le> block_h\<close>
  proof -
    have \<open>writeable_byte_state (lookup_memory_tree mt1 ?h' x)\<close>
      if \<open>x \<in> bits_range addr ?h' block_h\<close> and \<open>x < 2^?h'\<close> for x
    proof -
      from \<open>x < 2^?h'\<close> have \<open>x !! ?h' = False\<close>
        using bang_is_le leD by blast
      moreover from this and \<open>x \<in> bits_range addr ?h' block_h\<close> and b1 have \<open>x \<in> bits_range addr h block_h\<close>
        by (auto split: nat_diff_split_asm)
      moreover from this have \<open>lookup_memory_tree mt1 ?h' x = lookup_memory_tree ?mt h x\<close>
        by (metis \<open>x !! (h - 1) = False\<close> h_suc lookup_memory_tree.simps(4))
      moreover have \<open>x < 2^h\<close>
        using that MT_node.prems by (simp add: order_less_le_trans two_power_increasing)
      ultimately show ?thesis
        by (metis mapped)
    qed
    moreover have \<open>mt_height mt1 \<le> ?h'\<close>
      using MT_node.prems by fastforce
    ultimately show ?thesis
      using IHl by blast
  qed
  moreover 
  have \<open>\<exists>mt2'. memset_memory_tree_block mt2 ?h' addr block_h b = Inr mt2'\<close>
    if b1: \<open>addr !! ?h' = True \<or> h \<le> block_h\<close>
  proof -
    have \<open>writeable_byte_state (lookup_memory_tree mt2 ?h' x)\<close>
      if \<open>x \<in> bits_range addr ?h' block_h\<close> and \<open>x < 2^?h'\<close> for x
    proof -
      let ?x' = \<open>set_bit x ?h' True\<close>
      have T: \<open>?x' !! ?h' = True\<close>
        using that by (metis bit_set_bit_iff_2n order_less_irrefl word_gt_a_gt_0)
      from this and that and b1 have \<open>?x' \<in> bits_range addr h block_h\<close>
        by (fastforce simp: test_bit_set_gen bits_range_def split: nat_diff_split_asm)
      moreover have \<open>lookup_memory_tree mt2 ?h' x = lookup_memory_tree mt2 ?h' ?x'\<close>
        using \<open>h < 64\<close> by (intro lookup_memory_tree_eq; auto simp add: bit_simps )
      moreover from this have \<open>lookup_memory_tree mt2 ?h' ?x' = lookup_memory_tree ?mt h ?x'\<close>
        by (metis T h_suc lookup_memory_tree.simps(4))
      moreover have \<open>?x' < 2^h\<close>
        using that
        by (metis (no_types, lifting) MT_node.prems(1) bits_range_inh h_suc
            less_2p_is_upper_bits_unset less_Suc_eq not_less test_bit_set_gen)
      ultimately have \<open>writeable_byte_state (lookup_memory_tree mt2 ?h' ?x')\<close>
        by (metis mapped)
      with \<open>lookup_memory_tree mt2 ?h' x = lookup_memory_tree mt2 ?h' ?x'\<close> 
      show ?thesis by simp
    qed
    moreover have \<open>mt_height mt2 \<le> ?h'\<close>
      using MT_node.prems by force
    ultimately show ?thesis
      using IHr by blast
  qed
  ultimately show ?case
    by (auto split!: if_splits)
qed

lemma memory_tree_memset_block_succeeds2:
  assumes
    \<open>h < 64\<close>
    \<open>memory_tree_is_canonical mt\<close>
    \<open>x \<in> bits_range addr h block_h\<close>
    \<open>x < 2 ^ h\<close>
    \<open>\<not> writeable_byte_state (lookup_memory_tree mt h x)\<close>
    \<open>mt_height mt \<le> h\<close>
  shows
    \<open>\<exists>e. memset_memory_tree_block mt h addr block_h b = Inl e\<close>
using assms proof (induction mt arbitrary: h x)
  case MT_unmapped
  then show ?case by clarsimp
next
  case (MT_tagged x1 x2 x3)
  then show ?case 
    using nonempty_share_top_eq by force
next
  case (MT_node mt1 mt2)
  let ?h' = \<open>h-1\<close>
  let ?mt = \<open>MT_node mt1 mt2\<close>
  have mt1h: \<open>mt_height mt1 \<le> ?h'\<close>
    by (metis MT_node.prems(6) One_nat_def Suc_le_lessD max.bounded_iff mt_height.simps(3)
      nat_le_Suc_less_imp plus_1_eq_Suc)
  have mt2h: \<open>mt_height mt2 \<le> ?h'\<close>
    by (metis MT_node.prems(6) One_nat_def Suc_le_lessD max.bounded_iff mt_height.simps(3)
      nat_le_Suc_less_imp plus_1_eq_Suc)
  have mt1c: \<open>memory_tree_is_canonical mt1\<close>
   and mt2c:\<open>memory_tree_is_canonical mt2\<close>
    using MT_node.prems(2) by blast+
  have h_suc: \<open>h = Suc ?h'\<close> \<open>h>0\<close>
    using MT_node.prems(6) by auto
  have hl: \<open>?h' < 64\<close>
    using MT_node.prems(1) less_imp_diff_less by presburger
  have A: \<open>\<exists>e. memset_memory_tree_block mt1 ?h' addr block_h b = Inl e\<close>
    if \<open>x !! ?h' = False\<close>
  proof -
    from \<open>x \<in> bits_range addr h block_h\<close> h_suc have
      \<open>lookup_memory_tree ?mt h x = lookup_memory_tree mt1 ?h' x\<close>
      by (metis \<open>x !! (h - 1) = False\<close> lookup_memory_tree.simps(4))
    moreover have \<open>x < 2^?h'\<close>
      using \<open>?h' < 64\<close> \<open>x !! ?h' = False\<close> MT_node.prems(4)
      by (metis Suc_mask_eq_mask bits_range_inh h_suc(1) less_mask_eq)
    moreover from \<open>x \<in> bits_range addr h block_h\<close> have \<open>x \<in> bits_range addr ?h' block_h\<close>
      by (clarsimp simp add: bits_range_def)
    ultimately show ?thesis
      using  MT_node.prems(5) by (intro MT_node(1)[OF hl mt1c _ _ _ mt1h, where x=x]; clarsimp)
  qed
  have B: \<open>\<exists>e. memset_memory_tree_block mt2 ?h' addr block_h b = Inl e\<close>
    if \<open>x !! ?h' = True\<close>
  proof -
    let ?x' = \<open>set_bit x ?h' False\<close>
    note \<open>x !! ?h' = True\<close>
    moreover from this have \<open>lookup_memory_tree ?mt h x = lookup_memory_tree mt2 ?h' x\<close>
      by (subst h_suc; clarsimp)
    moreover have \<open>lookup_memory_tree mt2 ?h' x = lookup_memory_tree mt2 ?h' ?x'\<close>
      by (intro lookup_memory_tree_eq) (simp add: test_bit_set_gen)
    moreover have \<open>?x' < 2^?h'\<close>
      using \<open>?h' < 64\<close> MT_node.prems(4)
      by (simp add: less_2p_is_upper_bits_unset test_bit_set_gen)
    moreover from \<open>x \<in> bits_range addr h block_h\<close> have \<open>?x' \<in> bits_range addr ?h' block_h\<close>
      using \<open>h < 64\<close> by (clarsimp simp add: bits_range_def bit_simps)
    moreover from calculation have \<open>\<not> (writeable_byte_state (lookup_memory_tree mt2 ?h' ?x'))\<close>
      using MT_node.prems(5) by argo
    ultimately show ?thesis
      using MT_node(2)[OF hl mt2c _ _ _ mt2h] by blast
  qed
  show ?case
  proof (cases \<open>block_h < h\<close>)
    case True
    with \<open>x \<in> bits_range addr h block_h\<close> have \<open>x !! ?h' = addr !! ?h'\<close>
      by (clarsimp simp add: bits_range_def)
    with True A B show ?thesis
      by fastforce
  next
    case False
    with A B \<open>h>0\<close> show ?thesis  
      by (cases \<open>x !! ?h'\<close>; clarsimp split!: sum.splits)
  qed
qed

lemma memory_tree_memset_block_succeeds:
  assumes
    \<open>h < 64\<close>
    \<open>memory_tree_is_canonical mt\<close>
    \<open>mt_height mt \<le> h\<close>
  shows
    \<open>(\<forall>x \<in> bits_range addr h block_h. x < 2 ^ h \<longrightarrow> writeable_byte_state (lookup_memory_tree mt h x))
      \<longleftrightarrow> (\<exists>mt'. memset_memory_tree_block mt h addr block_h b = Inr mt')\<close>
  by (metis assms memory_tree_memset_block_succeeds1 memory_tree_memset_block_succeeds2 Inl_Inr_False)

(* TODO Remove? *)
lemma memory_tree_memset_block_fails:
  assumes
    \<open>h < 64\<close>
    \<open>memset_memory_tree_block mt h addr block_h b = Inl e\<close>
    \<open>memory_tree_is_canonical mt\<close>
    \<open>mt_height mt \<le> h\<close>
  shows
    \<open>\<exists>x\<in>bits_range addr h block_h.
       x < 2 ^ h \<and> \<not> writeable_byte_state (lookup_memory_tree mt h x)\<close>
  using assms proof (induction h arbitrary: mt addr)
  case (0 mt addr)
  then show ?case
    by (metis Inr_Inl_False memory_tree_memset_block_succeeds1)
next
  case (Suc h)
  show ?case
  proof (cases mt)
    case MT_unmapped
    then show ?thesis
      using assms Suc bits_range_inh[of \<open>Suc h\<close> addr] by force
  next
    case (MT_tagged sh tag mc)
    from this and Suc show ?thesis
      by (metis Inl_Inr_False memory_tree_memset_block_succeeds)
  next
    case (MT_node n0 n1)
    then consider \<open>memset_memory_tree_block n0 h addr block_h b = Inl e\<close> \<open>\<not>addr!!h \<or> block_h > h\<close>
      | \<open>memset_memory_tree_block n1 h addr block_h b = Inl e\<close> \<open>addr!!h \<or> block_h > h\<close>
      using Suc by (auto split: if_splits sum.splits)
    with Suc MT_node show ?thesis
      by (metis memory_tree_memset_block_succeeds1 sum.simps(4))
  qed
qed

subsection\<open>The separation algebra on physical memory\<close>

fun memory_tree_plus :: \<open>'tag memory_tree \<Rightarrow> 'tag memory_tree \<Rightarrow> 'tag memory_tree\<close> where
  \<open>memory_tree_plus MT_unmapped x = x\<close> |
  \<open>memory_tree_plus (MT_tagged sh tag x) MT_unmapped = MT_tagged sh tag x\<close> |
  \<open>memory_tree_plus (MT_tagged sh tag x) (MT_tagged sh2 _ _) = MT_tagged (sh+sh2) tag x\<close> |
  \<open>memory_tree_plus (MT_tagged sh tag x) (MT_node a b) =
    mt_node (memory_tree_plus (MT_tagged sh tag (mc_left x)) a)
            (memory_tree_plus (MT_tagged sh tag (mc_right x)) b)\<close> |

  \<open>memory_tree_plus (MT_node a b) MT_unmapped = MT_node a b\<close> |
  \<open>memory_tree_plus (MT_node a b) (MT_tagged sh tag x) =
    mt_node (memory_tree_plus a (MT_tagged sh tag (mc_left x)))
            (memory_tree_plus b (MT_tagged sh tag (mc_right x)))\<close> |
  \<open>memory_tree_plus (MT_node a b) (MT_node x y) =
    mt_node (memory_tree_plus a x) (memory_tree_plus b y)\<close>


fun memory_tree_disjoint :: \<open>'tag memory_tree \<Rightarrow> 'tag memory_tree \<Rightarrow> bool\<close> where
  \<open>memory_tree_disjoint MT_unmapped _ = True\<close> |
  \<open>memory_tree_disjoint _ MT_unmapped = True\<close> |
  \<open>memory_tree_disjoint (MT_tagged sh1 tag x) (MT_tagged sh2 tag2 y) =
    (Rep_nonempty_share sh1\<sharp>Rep_nonempty_share sh2 \<and> x = y \<and> tag = tag2)\<close> |
  \<open>memory_tree_disjoint (MT_tagged sh tag x) (MT_node a b) =
    (memory_tree_disjoint (MT_tagged sh tag (mc_left x)) a \<and>
     memory_tree_disjoint (MT_tagged sh tag (mc_right x)) b)\<close> |
  \<open>memory_tree_disjoint (MT_node x y) (MT_tagged sh tag a) =
    (memory_tree_disjoint x (MT_tagged sh tag (mc_left a)) \<and>
     memory_tree_disjoint y (MT_tagged sh tag (mc_right a)))\<close> |
  \<open>memory_tree_disjoint (MT_node x y) (MT_node a b) =
    (memory_tree_disjoint x a \<and> memory_tree_disjoint y b)\<close>


fun_cases memory_tree_disjoint_NodeE: \<open>memory_tree_disjoint x (MT_node a b)\<close>
fun_cases memory_tree_disjoint_TaggedE: \<open>memory_tree_disjoint (MT_tagged sh tag m) x\<close>
fun_cases memory_tree_disjoint_NodeE2: \<open>memory_tree_disjoint (MT_node a b) x\<close>
fun_cases memory_tree_disjoint_TaggedE2: \<open>memory_tree_disjoint x (MT_tagged sh tag m)\<close>

lemma memory_tree_disjoint_sym:
  assumes \<open>memory_tree_disjoint x y\<close>
  shows \<open>memory_tree_disjoint y x\<close>
  using assms by (induction y x rule: memory_tree_disjoint.induct; simp)

lemma memory_tree_disjoint_zero [simp]:
  shows \<open>memory_tree_disjoint x MT_unmapped\<close>
  by (cases x; simp)

lemma memory_tree_zero_unique:
  assumes \<open>memory_tree_disjoint x x\<close>
   and \<open>memory_tree_is_canonical x\<close>
  shows \<open>x = MT_unmapped\<close>
  using assms
proof (induction x)
  case (MT_tagged x1 x2 x3)
  then show ?case
    using Rep_nonempty_share less_imp_not_eq2 zero_share_def by auto
qed auto

lemma memory_tree_plus_ident2 [simp]:
  shows \<open>memory_tree_plus x MT_unmapped = x\<close>
  by (cases x; simp)

lemma memory_tree_plus_comm:
  assumes \<open>memory_tree_disjoint x y\<close>
  shows \<open>memory_tree_plus x y = memory_tree_plus y x\<close>
  using assms
proof (induction x y rule: memory_tree_disjoint.induct)
  case (3 sh1 tag x sh2 tag2 y)
  then show ?case
    by (metis Rep_nonempty_share_inject memory_tree_disjoint.simps(4) memory_tree_plus.simps(3) plus_nonempty_share.rep_eq plus_share_def sepalg_comm)
qed auto

lemma memory_tree_disjoint_mt_node [intro]:
  assumes \<open>memory_tree_disjoint x (MT_node a b)\<close>
   and \<open>memory_tree_is_canonical x\<close>
  shows \<open>memory_tree_disjoint x (mt_node a b)\<close>
using assms proof (induction x)
  case MT_unmapped
  then show ?case by clarsimp
next
  case (MT_tagged sh tag m)
  then show ?case
  by (induction a b rule: mt_node.induct; clarsimp simp add: mc_node_left_right)
next
  case (MT_node x1 x2)
  then show ?case
  by (induction a b rule: mt_node.induct)
     (auto simp add: mc_node_left_right elim!: canonical_mt_nodeE)
qed

lemma memory_tree_plus_height_le:
  assumes \<open>mt_height x \<le> h\<close>
  and \<open>mt_height y \<le> h\<close>
  shows \<open>mt_height (memory_tree_plus x y) \<le> h\<close>
using assms proof (induction h arbitrary: x y)
  case 0
  then show ?case
  by (cases x; cases y; clarsimp)
next
  case (Suc h)
  then show ?case
  by (cases x; cases y,
      auto intro!: mt_height_mt_nodeI
           simp add: mc_left_height mc_right_height)
qed

lemma memory_tree_plus_canonical:
  assumes \<open>memory_tree_is_canonical x\<close>
  and \<open>memory_tree_is_canonical y\<close>
  shows \<open>memory_tree_is_canonical (memory_tree_plus x y)\<close>
  using assms
  by (induction x y rule: memory_tree_plus.induct,
      auto elim!: canonical_mt_nodeE
           intro!: canonical_mt_nodeI mt_node_canonical)

lemma memory_tree_disjoint_mt_node2 [intro]:
  assumes \<open>memory_tree_disjoint (MT_node a b) x\<close>
   and \<open>memory_tree_is_canonical x\<close>
  shows \<open>memory_tree_disjoint (mt_node a b) x\<close>
  using assms memory_tree_disjoint_sym memory_tree_disjoint_mt_node by blast

lemma memory_tree_plus_tagged_node:
  assumes \<open>memory_tree_disjoint (MT_tagged sh tag x) (MT_node a b)\<close>
   and \<open>memory_contents_canonical x\<close>
  shows
  \<open>memory_tree_plus (MT_tagged sh tag x) (mt_node a b) =
   mt_node (memory_tree_plus (MT_tagged sh tag (mc_left x)) a)
           (memory_tree_plus (MT_tagged sh tag (mc_right x)) b)\<close>
  using assms by (induction a b rule: mt_node.induct, auto simp add: mc_node_left_right)

lemma memory_tree_plus_node_tagged:
  assumes \<open>memory_tree_disjoint (MT_node a b) (MT_tagged sh tag x)\<close>
   and \<open>memory_contents_canonical x\<close>
  shows
  \<open>memory_tree_plus (mt_node a b) (MT_tagged sh tag x) =
   mt_node (memory_tree_plus a (MT_tagged sh tag (mc_left x)))
           (memory_tree_plus b (MT_tagged sh tag (mc_right x)))\<close>
  using assms by (induction a b rule: mt_node.induct, auto simp add: mc_node_left_right)

lemma memory_tree_disjoint_tagged_plus:
  assumes \<open>memory_tree_is_canonical x\<close>
  and \<open>memory_tree_disjoint x (MT_tagged sh1 tag mc)\<close>
  and \<open>memory_tree_disjoint x (MT_tagged sh2 tag mc)\<close>
  shows \<open>memory_tree_disjoint x (MT_tagged (sh1 + sh2) tag mc)\<close>
using assms proof (induction x arbitrary: mc)
  case MT_unmapped
  then show ?case by clarsimp
next
  case (MT_tagged x1 x2a)
  then show ?case
  by (clarsimp simp add: disjoint_share_def inf_aci(1) inf_sup_distrib1 plus_nonempty_share.rep_eq)
next
  case (MT_node x1 x2)
  then show ?case by auto
qed

lemma mt_plus_disjoint1:
  assumes \<open>memory_tree_disjoint x a\<close>
  and \<open>memory_tree_disjoint x b\<close>
  and \<open>memory_tree_disjoint a b\<close>
  and \<open>memory_tree_is_canonical x\<close>
  shows \<open>memory_tree_disjoint x (memory_tree_plus a b)\<close>
using assms proof (induction x arbitrary: a b)
  case MT_unmapped
  then show ?case by clarsimp
next
  case (MT_tagged sh tag m)
  then show ?case
  proof (induction a b arbitrary: m rule: memory_tree_plus.induct)
    case (3 sh1 tag1 x sh2 uu uv)
    then show ?case
      by (metis memory_tree_disjoint.simps(4) memory_tree_disjoint_tagged_plus memory_tree_plus.simps(3))
  qed (auto simp: canonical_mc_left canonical_mc_right memory_tree_disjoint_mt_node)
next
  case (MT_node x1 x2)
  then show ?case
  by (induction a b rule: memory_tree_plus.induct,
      auto simp add:  memory_tree_disjoint_tagged_plus elim!: canonical_mt_nodeE)
qed

lemma mt_plus_disjoint2:
  assumes \<open>memory_tree_disjoint a x\<close>
  and \<open>memory_tree_disjoint b x\<close>
  and \<open>memory_tree_disjoint a b\<close>
  and \<open>memory_tree_is_canonical x\<close>
  shows \<open>memory_tree_disjoint (memory_tree_plus a b) x\<close>
  using assms mt_plus_disjoint1 memory_tree_disjoint_sym memory_tree_plus_comm by blast

lemma memory_tree_plus_Node_node:
  assumes \<open>mt_node x y = MT_node x y\<close> and \<open>memory_tree_disjoint x a\<close> and \<open>memory_tree_disjoint y b\<close>
  shows \<open>memory_tree_plus (MT_node x y) (mt_node a b) = mt_node (memory_tree_plus x a) (memory_tree_plus y b)\<close>
  using assms by (induction a b rule: mt_node.induct, auto)

lemma memory_tree_plus_node_Node:
  assumes \<open>mt_node a b = MT_node a b\<close> and \<open>memory_tree_disjoint x a\<close> and \<open>memory_tree_disjoint y b\<close>
  shows \<open>memory_tree_plus (mt_node x y) (MT_node a b) = mt_node (memory_tree_plus x a) (memory_tree_plus y b)\<close>
  using assms by (induction x y rule: mt_node.induct, auto)

lemma memory_tree_plus_assoc:
  assumes \<open>memory_tree_disjoint x y\<close> and \<open>memory_tree_disjoint y z\<close> and \<open>memory_tree_disjoint x z\<close>
   and \<open>memory_tree_is_canonical x\<close> and \<open>memory_tree_is_canonical y\<close> and \<open>memory_tree_is_canonical z\<close>
  shows \<open>memory_tree_plus x (memory_tree_plus y z) = memory_tree_plus (memory_tree_plus x y) z\<close>
using assms proof (induction y arbitrary: x z)
  case MT_unmapped
  then show ?case
    by force
next
  case (MT_tagged sh tag mc)
  then show ?case
    by (induction x z arbitrary: mc rule: memory_tree_disjoint.induct,
        auto simp add: add.assoc memory_tree_plus_tagged_node memory_tree_plus_node_tagged
                canonical_mc_left canonical_mc_right mt_plus_disjoint1 mt_plus_disjoint2
                memory_tree_plus_Node_node memory_tree_plus_node_Node canonical_mt_node_iff)
next
  case (MT_node a b)
  then show ?case
    by (induction x z rule: memory_tree_disjoint.induct,
        auto simp add: add.assoc memory_tree_plus_tagged_node memory_tree_plus_node_tagged
                canonical_mc_left canonical_mc_right mt_plus_disjoint1 mt_plus_disjoint2
                memory_tree_plus_Node_node memory_tree_plus_node_Node canonical_mt_node_iff)
qed

lemma memory_tree_disjoint_tagged_le:
  assumes \<open>memory_tree_disjoint x (MT_tagged sh2 tag mc)\<close>
  and \<open>sh1 \<le> sh2\<close>
  shows \<open>memory_tree_disjoint x (MT_tagged sh1 tag mc)\<close>
  using assms proof (induction x arbitrary: mc)
  case MT_unmapped
  then show ?case by clarsimp
next
  case (MT_tagged sh' tag' mc')
  then show ?case
  apply (clarsimp simp add: disjoint_share_def)
  by (metis bot.extremum_uniqueI eq_refl inf_mono less_eq_nonempty_share.rep_eq)
next
  case (MT_node n0 n1)
  then show ?case by auto
qed

lemma memory_tree_plus_unmapped:
  assumes \<open>memory_tree_plus x y = MT_unmapped\<close>
  and \<open>memory_tree_is_canonical x\<close>
  and \<open>memory_tree_is_canonical y\<close>
  shows \<open>x = MT_unmapped \<and> y = MT_unmapped\<close>
  using assms by (induction x y rule: memory_tree_plus.induct) (auto simp: canonical_mt_node_iff)

lemma memory_tree_plus_unmappedE:
  assumes \<open>memory_tree_plus x y = MT_unmapped\<close>
  and \<open>memory_tree_is_canonical x\<close>
  and \<open>memory_tree_is_canonical y\<close>
  and \<open>x = MT_unmapped \<Longrightarrow> y = MT_unmapped \<Longrightarrow> R\<close>
  shows R
  using assms memory_tree_plus_unmapped by fast

lemma memory_tree_plus_unmapped_iff:
  assumes \<open>memory_tree_is_canonical x\<close> \<open>memory_tree_is_canonical y\<close>
  shows \<open>memory_tree_plus x y = MT_unmapped \<longleftrightarrow> x = MT_unmapped \<and> y = MT_unmapped\<close>
  by (meson assms memory_tree_plus_ident2 memory_tree_plus_unmappedE)

lemma memory_tree_apart_plus2:
  assumes \<open>memory_tree_disjoint x (memory_tree_plus y z)\<close>
  and \<open>memory_tree_disjoint y z\<close>
  and \<open>memory_tree_is_canonical x\<close>
  and \<open>memory_tree_is_canonical y\<close>
  and \<open>memory_tree_is_canonical z\<close>
shows \<open>memory_tree_disjoint x y\<close>
  using assms
proof (induction y z arbitrary: x rule: memory_tree_disjoint.induct)
  case 3
  then show ?case
    by (simp add: less_eq_nonempty_share.rep_eq memory_tree_disjoint_tagged_le plus_nonempty_share.rep_eq)
next
  case (4 sh tag x a b z)
  show ?case
  proof (cases z)
    case (MT_tagged sh' tag' x')
    with 4 show ?thesis
      apply (clarsimp simp: canonical_mt_node_iff)
      apply (erule memory_tree_disjoint_TaggedE; simp add: canonical_mc_left memory_tree_plus_unmapped_iff)
      apply (metis canonical_mc_left canonical_mc_right canonical_tagged disjoint_sym mc_left_node mc_left_right_ext mc_right_node memory_tree_disjoint.simps(4))
      by (metis canonical_mc_left canonical_mc_right canonical_tagged mc_left_right_ext memory_tree_disjoint.simps(4) mt_node_eqE)
  next
    case (MT_node u v)
    with 4 show ?thesis
      by (force simp: canonical_mc_left canonical_mc_right elim!: memory_tree_disjoint_NodeE2 mt_node_eqE)
  qed auto
next
  case (5 x y sh tag a z)
  show ?case
  proof (cases z)
    case (MT_tagged sh' tag' x')
    with 5 show ?thesis
      apply (clarsimp simp: canonical_mt_node_iff)
      apply (erule memory_tree_disjoint_TaggedE; simp add: canonical_mc_left memory_tree_plus_unmapped_iff)
      using canonical_mc_left canonical_mc_right apply force
      by (metis canonical_mc_left canonical_mc_right canonical_tagged mt_node_eqE)
  next
    case (MT_node x31 x32)
    with 5 show ?thesis
      by (fastforce elim!: memory_tree_disjoint_NodeE2 mt_node_eqE)
  qed auto
next
  case (6 x y a b z)
  show ?case
  proof (cases z)
    case (MT_tagged sh' tag' x')
    with 6 show ?thesis
      apply (clarsimp simp: canonical_mt_node_iff)
      apply (erule memory_tree_disjoint_TaggedE)
        apply (simp add: memory_tree_plus_unmapped_iff)
      using canonical_mc_left canonical_mc_right apply force
      apply (force elim!: mt_node_eqE)
      done
  next
    case (MT_node x31 x32)
    with 6 show ?thesis
      by (force elim!: memory_tree_disjoint_NodeE2 mt_node_eqE)
  qed auto
qed auto

lemma memory_tree_apart_assoc2:
  assumes \<open>memory_tree_disjoint x (memory_tree_plus y z)\<close>
  and \<open>memory_tree_disjoint y z\<close>
  and \<open>memory_tree_is_canonical x\<close>
  and \<open>memory_tree_is_canonical y\<close>
  and \<open>memory_tree_is_canonical z\<close>
  shows \<open>memory_tree_disjoint (memory_tree_plus x y) z\<close>
  using assms
proof (induction y z arbitrary: x rule: memory_tree_disjoint.induct)
  case (3 sh1 tag x sh2 tag2 y z)
  then show ?case  \<comment> \<open>identical proofs with seemingly no way to consolidate\<close>
    by (metis memory_tree_apart_plus2 memory_tree_disjoint_sym memory_tree_plus_comm mt_plus_disjoint2)
next
  case (4 sh tag x a b z)
  then show ?case
    by (metis memory_tree_apart_plus2 memory_tree_disjoint_sym memory_tree_plus_comm mt_plus_disjoint2)
next
  case (5 x y sh tag a z)
  then show ?case
    by (metis memory_tree_apart_plus2 memory_tree_disjoint_sym memory_tree_plus_comm mt_plus_disjoint2)
next
  case (6 x y a b z)
  then show ?case
    by (metis memory_tree_apart_plus2 memory_tree_disjoint_sym memory_tree_plus_comm mt_plus_disjoint2)
qed auto

lemma memory_tree_plus_strong1:
  assumes \<open>memory_tree_disjoint x y\<close>
    and \<open>memory_tree_disjoint (memory_tree_plus x y) z\<close>
    and \<open>memory_tree_is_canonical x\<close>
    and \<open>memory_tree_is_canonical y\<close>
    and \<open>memory_tree_is_canonical z\<close>
  shows \<open>memory_tree_disjoint y z\<close>
  using assms
proof (induction x y arbitrary: z rule: memory_tree_disjoint.induct)
  case (3 sh1 tag x sh2 tag2 y)
  then show ?case \<comment> \<open>again: identical proofs with seemingly no way to consolidate\<close>
    by (metis memory_tree_apart_plus2 memory_tree_disjoint_sym memory_tree_plus_comm)
next
  case (4 sh tag x a b)
  then show ?case
    by (metis memory_tree_apart_plus2 memory_tree_disjoint_sym memory_tree_plus_comm)
next
  case (5 x y sh tag a)
  then show ?case
    by (metis memory_tree_apart_plus2 memory_tree_disjoint_sym memory_tree_plus_comm)
next
  case (6 x y a b)
  then show ?case
    by (metis memory_tree_apart_plus2 memory_tree_disjoint_sym memory_tree_plus_comm)
qed auto

lemma memory_tree_plus_strong2:
  assumes \<open>memory_tree_disjoint x y\<close>
  and \<open>memory_tree_disjoint (memory_tree_plus x y) z\<close>
  and \<open>memory_tree_is_canonical x\<close>
  and \<open>memory_tree_is_canonical y\<close>
  and \<open>memory_tree_is_canonical z\<close>
  shows \<open>memory_tree_disjoint x z\<close>
  using assms by (metis memory_tree_plus_strong1 memory_tree_disjoint_sym memory_tree_plus_comm)

lemma lookup_memory_tree_node_disjE:
  assumes H: \<open>\<forall>addr. lookup_memory_tree (MT_node a b) (Suc h) addr \<sharp> lookup_memory_tree (MT_node x y) (Suc h) addr\<close>
    and \<open>h < 64\<close>
  obtains \<open>\<forall>addr. lookup_memory_tree a h addr \<sharp> lookup_memory_tree x h addr\<close>
          \<open>\<forall>addr. lookup_memory_tree b h addr \<sharp> lookup_memory_tree y h addr\<close>
proof -
  have *: \<open>(\<And>n. n < h \<Longrightarrow> addr !! n = Generic_set_bit.set_bit addr h u !! n)\<close> for addr :: \<open>64 word\<close> and u
    by (simp add: test_bit_set_gen)
  have \<open>lookup_memory_tree a h addr \<sharp> lookup_memory_tree x h addr\<close> for addr :: \<open>64 word\<close>
    using H[rule_format, of \<open>set_bit addr h False\<close>] 
    by (simp add: test_bit_set_gen lookup_memory_tree_eq [OF *, of h _ addr False])
  moreover
  have \<open>lookup_memory_tree b h addr \<sharp> lookup_memory_tree y h addr\<close> for addr :: \<open>64 word\<close>
    using H[rule_format, of \<open>set_bit addr h True\<close>] \<open>h < 64\<close>
    by (simp add: lookup_memory_tree_eq [OF *, of h _ addr True] bit_set_bit_word_iff)
  ultimately show thesis
    using that by blast
qed

lemma memory_tree_lookup_disjoint2_aux:
  assumes \<open>memory_tree_is_canonical mt2\<close>
  and \<open>memory_contents_canonical x\<close>
  and \<open>mt_height mt2 \<le> h\<close>
  and \<open>mc_height x \<le> h\<close>
  and \<open>h \<le> 64\<close>
  and \<open>\<forall>addr. lookup_memory_tree mt2 h addr \<sharp> Tagged sh tag (lookup_memory_contents x h addr)\<close>
  shows \<open>memory_tree_disjoint (MT_tagged sh tag x) mt2\<close>
using assms proof (induction mt2 arbitrary: h x)
  case MT_unmapped
  then show ?case by clarsimp
next
  case (MT_tagged sh2 tag mc)
  then show ?case
  by (clarsimp simp add: memory_contents_unique[where h=h])
next
  case (MT_node n0 n1 h)
  show ?case
  proof (cases h)
    case (Suc h')
    moreover 
    have \<open>lookup_memory_tree n0 h' addr \<sharp> Tagged sh tag (lookup_memory_contents (mc_left x) h' addr)\<close> for addr :: \<open>64 word\<close>
    proof -
      obtain addr' where addr': \<open>addr' = set_bit addr h' False\<close> by simp
      then have \<open>lookup_memory_tree n0 h' addr' \<sharp> Tagged sh tag (lookup_memory_contents (mc_left x) h' addr')\<close>
        using test_bit_set[of addr h' False] unfolding size_word_def
        using \<open>h \<le> 64\<close> \<open>h = Suc h'\<close> MT_node(3-)
        by (cases x; clarsimp; presburger)
      moreover have \<open>lookup_memory_tree n0 h' addr' = lookup_memory_tree n0 h' addr\<close>
        by (metis (no_types, lifting) addr' lookup_memory_tree_eq nat_neq_iff test_bit_set_gen)
      ultimately show ?thesis
        by (metis (no_types, lifting) addr' lookup_memory_contents_eq nat_neq_iff test_bit_set_gen)
    qed
    moreover 
    have \<open>lookup_memory_tree n1 h' addr \<sharp> Tagged sh tag (lookup_memory_contents (mc_right x) h' addr)\<close> for addr :: \<open>64 word\<close>
    proof -
      obtain addr' where addr': \<open>addr' = set_bit addr h' True\<close> by simp
      then have \<open>lookup_memory_tree n1 h' addr' \<sharp> Tagged sh tag (lookup_memory_contents (mc_right x) h' addr')\<close>
        using test_bit_set[of addr h' True] unfolding size_word_def
        using \<open>h \<le> 64\<close> \<open>h = Suc h'\<close> MT_node(3-)
        by (cases x; clarsimp; presburger)
      moreover have \<open>lookup_memory_tree n1 h' addr' = lookup_memory_tree n1 h' addr\<close>
        by (metis (no_types, lifting) addr' lookup_memory_tree_eq nat_neq_iff test_bit_set_gen)
      ultimately show ?thesis
        by (metis (no_types, lifting) addr' bit_set_bit_word_iff lookup_memory_contents_eq nat_neq_iff)
    qed
    ultimately show ?thesis
      using MT_node
      by (auto simp add: canonical_mc_left canonical_mc_right mc_left_height mc_right_height)
  qed (use MT_node in auto)
qed


theorem memory_tree_lookup_disjoint2:
  assumes \<open>memory_tree_is_canonical mt1\<close>
   and \<open>memory_tree_is_canonical mt2\<close>
   and \<open>mt_height mt1 \<le> h\<close>
   and \<open>mt_height mt2 \<le> h\<close>
   and \<open>h \<le> 64\<close>
  assumes \<open>\<forall>addr. lookup_memory_tree mt1 h addr \<sharp> lookup_memory_tree mt2 h addr\<close>
   shows \<open>memory_tree_disjoint mt1 mt2\<close>
using assms proof (induction mt1 arbitrary: h mt2)
  case MT_unmapped
  then show ?case
  using memory_tree_constant_class[of mt2 h No_Value]
  by auto
next
  case (MT_tagged sh tag x)
  then show ?case by (auto intro: memory_tree_lookup_disjoint2_aux)
next
  case node: (MT_node n0 n1)
  show ?case
  proof (cases mt2)
    case MT_unmapped
    then show ?thesis by auto
  next
    case MT_tagged
    with node.prems show ?thesis
      by (metis canonical_tagged lookup_memory_tree.simps(2) memory_tree_disjoint_sym memory_tree_lookup_disjoint2_aux
          mt_height.simps(2)) 
  next
    case MT_node
    show ?thesis
    proof (cases h)
      case (Suc h')
      with node show ?thesis
        unfolding MT_node by (fastforce elim!: lookup_memory_tree_node_disjE)
    qed (use node in auto)
  qed
qed

lemma memory_tree_lookup_disjoint:
  assumes \<open>memory_tree_disjoint x y\<close>
  shows \<open>lookup_memory_tree x h addr \<sharp> lookup_memory_tree y h addr\<close>
  using assms
proof (induction x y arbitrary: h rule: memory_tree_disjoint.induct)
  case (4 sh tag mc a b h)
  then show ?case
    by (cases h; cases mc; simp)
next
  case (5 x y sh tag mc h)
  then show ?case
    by (cases h; cases mc; simp)
next
  case (6 x y a b)
  then show ?case
    by (cases h; simp)
qed auto

lemma memory_tree_plus_lookup:
  assumes \<open>mt_height x \<le> h\<close> and \<open>mt_height y \<le> h\<close>
   and \<open>memory_tree_disjoint x y\<close>
  shows \<open>lookup_memory_tree (memory_tree_plus x y) h addr =
         lookup_memory_tree x h addr + lookup_memory_tree y h addr\<close>
using assms proof (induction x arbitrary: h y)
  case MT_unmapped
  then show ?case by simp
next
  case (MT_tagged sh tag mc)
  then show ?case
  proof (induction h arbitrary: y mc)
    case 0
    then show ?case apply clarsimp
      by (cases y; cases mc; simp)
  next
    case (Suc h)
    then show ?case
      apply (cases y; cases mc)
      apply (simp_all add: le_imp_less_Suc lookup_memory_tree_mt_node memory_tree_plus_height_le)
      done
  qed
next
  case ind_case: (MT_node m0 m1)
  show ?case
  proof (cases y)
    case MT_unmapped
    then show ?thesis by clarsimp
  next
    case (MT_tagged sh tag mc)
    with ind_case
    have A: \<open>mt_height (memory_tree_plus m0 (MT_tagged sh tag (mc_left mc))) < h\<close>
      using Suc_le_D less_Suc_eq_le mc_left_height memory_tree_plus_height_le by fastforce
    from ind_case MT_tagged
    have B: \<open>mt_height (memory_tree_plus m1 (MT_tagged sh tag (mc_right mc))) < h\<close>
      using Suc_le_D less_Suc_eq_le mc_right_height memory_tree_plus_height_le by fastforce
    show ?thesis
      using MT_tagged ind_case
      apply (simp add: lookup_memory_tree_mt_node A B)
      apply (cases h; cases mc; simp)
      done
  next
    case (MT_node n0 n1)
    have *: \<open>mt_height (memory_tree_plus m0 n0) < h\<close>
            \<open>mt_height (memory_tree_plus m1 n1) < h\<close>
      using ind_case.prems MT_node Suc_le_D memory_tree_plus_height_le by fastforce+
    show ?thesis
      using MT_node ind_case
      apply (simp add: lookup_memory_tree_mt_node *)
      apply (cases h; clarsimp)
      done
  qed
qed


subsection\<open>Splitting physical memory\<close>

fun memory_contents_take_block ::
  \<open>(memory_contents \<Rightarrow> 'tag memory_tree) \<Rightarrow>
   memory_contents \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 'tag memory_tree\<close> where
  \<open>memory_contents_take_block k mc h addr block_h =
    (if h > block_h then
      (if bit addr (h-1) then
        mt_node MT_unmapped (memory_contents_take_block k (mc_right mc) (h-1) addr block_h)
       else
        mt_node (memory_contents_take_block k (mc_left mc) (h-1) addr block_h) MT_unmapped)
     else
       k mc)\<close>

declare memory_contents_take_block.simps [simp del]

lemma memory_contents_take_block_nat_simps [simp]:
  shows \<open>memory_contents_take_block k mc 0 addr block_h = k mc\<close>
  and \<open>memory_contents_take_block k mc (Suc h) addr block_h =
        (if h \<ge> block_h then
         (if bit addr h then
           mt_node MT_unmapped (memory_contents_take_block k (mc_right mc) h addr block_h)
          else
           mt_node (memory_contents_take_block k (mc_left mc) h addr block_h) MT_unmapped)
         else k mc)\<close>
  by (subst memory_contents_take_block.simps; simp)+


fun memory_contents_delete_block ::
  \<open>(memory_contents \<Rightarrow> 'tag memory_tree) \<Rightarrow>
   memory_contents \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 'tag memory_tree\<close> where
  \<open>memory_contents_delete_block k mc h addr block_h =
    (if h > block_h then
      (if bit addr (h-1) then
        mt_node (k (mc_left mc)) (memory_contents_delete_block k (mc_right mc) (h-1) addr block_h)
       else
        mt_node (memory_contents_delete_block k (mc_left mc) (h-1) addr block_h) (k (mc_right mc)))
     else
       MT_unmapped)\<close>

declare memory_contents_delete_block.simps [simp del]

lemma memory_contents_delete_block_nat_simps [simp]:
  shows \<open>memory_contents_delete_block k mc 0 addr block_h = MT_unmapped\<close>
  and \<open>memory_contents_delete_block k mc (Suc h) addr block_h =
        (if h \<ge> block_h then
         (if bit addr h then
           mt_node (k (mc_left mc)) (memory_contents_delete_block k (mc_right mc) h addr block_h)
          else
           mt_node (memory_contents_delete_block k (mc_left mc) h addr block_h) (k (mc_right mc)))
         else MT_unmapped)\<close>
  by (subst memory_contents_delete_block.simps; simp)+

lemma memory_contents_take_delete_canonical:
  assumes \<open>k = MT_tagged tag sh\<close>
   and \<open>memory_contents_canonical mc\<close>
  shows \<open>memory_tree_is_canonical (memory_contents_take_block k mc h addr block_h) \<and>
         memory_tree_is_canonical (memory_contents_delete_block k mc h addr block_h)\<close>
using assms proof (induction h arbitrary: mc)
  case 0
  then show ?case
  by (auto simp add: memory_contents_take_block.simps memory_contents_delete_block.simps
          memory_contents_canonical_def memory_tree_is_canonical_def)
next
  case (Suc h)
  then show ?case
    using canonical_mc_right canonical_mc_left
    by (auto simp add: mt_node_commute memory_contents_canonical_def memory_tree_is_canonical_def
                elim!: canonical_MC_nodeE)
qed

lemma memory_tree_disjoint_mt_node3 [intro]:
  assumes \<open>memory_tree_disjoint (MT_node x y) (MT_node a b)\<close>
   and \<open>memory_tree_is_canonical x\<close>
   and \<open>memory_tree_is_canonical y\<close>
   and \<open>memory_tree_is_canonical a\<close>
   and \<open>memory_tree_is_canonical b\<close>
 shows \<open>memory_tree_disjoint (mt_node x y) (mt_node a b)\<close>
proof (cases \<open>a = MT_unmapped \<and> b = MT_unmapped\<close>)
  case False
  then show ?thesis
    using assms mc_node_canonical 
    by (cases x; cases y; intro memory_tree_disjoint_mt_node) auto    
qed auto

lemma memory_contents_take_height_le:
  assumes \<open>k = MT_tagged tag sh\<close>
  and \<open>mc_height mc \<le> h\<close>
  shows \<open>mt_height (memory_contents_take_block k mc h addr block_h) \<le> h\<close>
using assms
  by (induction h arbitrary: mc)
     (auto intro!: mt_height_mt_nodeI simp add: mc_right_height mc_left_height)

lemma memory_contents_delete_height_le:
  assumes \<open>k = MT_tagged tag sh\<close>
  and \<open>mc_height mc \<le> h\<close>
  shows \<open>mt_height (memory_contents_delete_block k mc h addr block_h) \<le> h\<close>
using assms
  by (induction h arbitrary: mc)
     (auto intro!: mt_height_mt_nodeI simp add: mc_right_height mc_left_height)

lemma lookup_memory_contents_Suc [simp]:
  shows \<open>lookup_memory_contents mc (Suc h) x =
           (if x!!h then lookup_memory_contents (mc_right mc) h x else lookup_memory_contents (mc_left mc) h x)\<close>
  by (cases mc, auto)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma memory_contents_take_delete_lookup:
  assumes \<open>k = MT_tagged tag sh\<close> and \<open>mc_height mc \<le> h\<close>
  shows \<open>lookup_memory_tree (memory_contents_take_block k mc h addr block_h) h x +
         lookup_memory_tree (memory_contents_delete_block k mc h addr block_h) h x =
         lookup_memory_tree (k mc) h x\<close>
using assms proof (induction h arbitrary: mc)
  case 0
  then show ?case
    by auto
next
  case (Suc h)
  have \<open>mt_height (memory_contents_take_block (MT_tagged tag sh) (mc_right mc) h addr block_h) < Suc h\<close>
       \<open>mt_height (memory_contents_take_block (MT_tagged tag sh) (mc_left mc) h addr block_h) < Suc h\<close>
    by (simp_all add: Suc.prems le_imp_less_Suc mc_left_height mc_right_height memory_contents_take_height_le)
  moreover
  have \<open>mc_height (mc_left mc) < Suc h\<close> \<open>mc_height (mc_right mc) < Suc h\<close>
    by (simp_all add: Suc.prems less_Suc_eq_le mc_left_height mc_right_height)
  moreover
  have \<open>mt_height (memory_contents_delete_block (MT_tagged tag sh) (mc_right mc) h addr block_h) < Suc h\<close>
       \<open>mt_height (memory_contents_delete_block (MT_tagged tag sh) (mc_left mc) h addr block_h) < Suc h\<close>
    by (simp_all add: Suc.prems le_imp_less_Suc mc_left_height mc_right_height memory_contents_delete_height_le)
  ultimately show ?case
    using Suc by (simp add: lookup_memory_tree_mt_node)
qed


lemma memory_contents_take_delete_disjoint:
  assumes \<open>k = MT_tagged sh tag\<close>
    and \<open>memory_contents_canonical mc\<close>
  shows \<open>memory_tree_disjoint (memory_contents_take_block k mc h addr block_h)
                              (memory_contents_delete_block k mc h addr block_h)\<close>
using assms proof (induction h arbitrary: mc)
  case 0
  then show ?case
    by (simp add: memory_contents_take_block.simps memory_contents_delete_block.simps)
next
  case (Suc h)
  show ?case
  proof (cases \<open>block_h \<le> h\<close>)
    case le: True
    have unmapped: \<open>memory_tree_is_canonical MT_unmapped\<close>
      by (simp add: memory_tree_is_canonical_def)
    with le Suc unmapped show ?thesis
      by (auto simp: canonical_mc_left canonical_mc_right memory_contents_take_delete_canonical)
  qed auto
qed

fun memory_tree_take_block :: \<open>'tag memory_tree \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 'tag memory_tree\<close> where
  \<open>memory_tree_take_block MT_unmapped h addr block_h = MT_unmapped\<close> |
  \<open>memory_tree_take_block (MT_tagged sh tag mc) h addr block_h =
    memory_contents_take_block (MT_tagged sh tag) mc h addr block_h\<close> |
  \<open>memory_tree_take_block (MT_node n0 n1) h addr block_h =
    (if h > block_h then
      (if bit addr (h-1) then
         mt_node MT_unmapped (memory_tree_take_block n1 (h-1) addr block_h)
       else
         mt_node (memory_tree_take_block n0 (h-1) addr block_h) MT_unmapped)
     else
       MT_node n0 n1)\<close>

fun memory_tree_delete_block :: \<open>'tag memory_tree \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 'tag memory_tree\<close> where
  \<open>memory_tree_delete_block MT_unmapped h addr block_h = MT_unmapped\<close> |
  \<open>memory_tree_delete_block (MT_tagged sh tag mc) h addr block_h =
    memory_contents_delete_block (MT_tagged sh tag) mc h addr block_h\<close> |
  \<open>memory_tree_delete_block (MT_node n0 n1) h addr block_h =
    (if h > block_h then
      (if bit addr (h-1) then
         mt_node n0 (memory_tree_delete_block n1 (h-1) addr block_h)
       else
         mt_node (memory_tree_delete_block n0 (h-1) addr block_h) n1)
     else
       MT_unmapped)\<close>

lemma memory_tree_ummapped_canonical [simp]: \<open>memory_tree_is_canonical MT_unmapped\<close>
  by (simp add: memory_tree_is_canonical_def)

lemma memory_tree_take_canonical:
  assumes \<open>memory_tree_is_canonical mt\<close>
  shows \<open>memory_tree_is_canonical (memory_tree_take_block mt h addr block_h)\<close>
using assms
proof (induction mt h addr block_h rule: memory_tree_take_block.induct)
  case (3 n0 n1 h addr block_h)
  then show ?case
    by (auto intro!: mt_node_canonical)
qed (auto simp add: memory_contents_take_delete_canonical)

lemma memory_tree_delete_canonical:
  assumes \<open>memory_tree_is_canonical mt\<close>
  shows \<open>memory_tree_is_canonical (memory_tree_delete_block mt h addr block_h)\<close>
using assms
proof (induction mt h addr block_h rule: memory_tree_take_block.induct)
  case (1 h addr block_h)
  then show ?case
    by auto
next
  case (2 sh tag mc h addr block_h)
  then show ?case
    by (simp add: memory_contents_take_delete_canonical)
next
  case (3 n0 n1 h addr block_h)
  then show ?case
    by (auto intro!: mt_node_canonical)
qed

lemma memory_tree_take_height_le:
  assumes \<open>mt_height mt \<le> h\<close>
  shows \<open>mt_height (memory_tree_take_block mt h addr block_h) \<le> h\<close>
  using assms
proof (induction mt h addr block_h rule: memory_tree_take_block.induct)
  case (2 sh tag mc h addr block_h)
  then show ?case
    by (simp add: memory_contents_take_height_le)
qed force+

lemma memory_tree_delete_height_le:
  assumes \<open>mt_height mt \<le> h\<close>
  shows \<open>mt_height (memory_tree_delete_block mt h addr block_h) \<le> h\<close>
  using assms
proof (induction mt h addr block_h rule: memory_tree_delete_block.induct)
  case (2 sh tag mc h addr block_h)
  then show ?case
    by (simp add: memory_contents_delete_height_le)
qed force+

lemma memory_tree_take_delete_disjoint:
  assumes \<open>memory_tree_is_canonical mt\<close>
  shows \<open>memory_tree_disjoint (memory_tree_take_block mt h addr block_h)
                              (memory_tree_delete_block mt h addr block_h)\<close>
  using assms
proof (induction mt h addr block_h rule: memory_tree_delete_block.induct)
  case (1 h addr block_h)
  then show ?case
    by simp
next
  case (2 sh tag mc h addr block_h)
  then show ?case
    by (simp add: memory_contents_take_delete_disjoint)
next
  case (3 n0 n1 h addr block_h)
  then show ?case
    by (auto intro!: memory_tree_disjoint_mt_node3 memory_tree_take_canonical memory_tree_delete_canonical)
qed

lemma memory_contents_take_lookup:
  assumes \<open>mc_height mc \<le> h\<close>
  and \<open>k = MT_tagged sh tag\<close>
  shows \<open>lookup_memory_tree (memory_contents_take_block k mc h addr block_h) h x =
         (if x \<in> bits_range addr h block_h then lookup_memory_tree (k mc) h x else Unmapped)\<close>
  using assms
proof (induction h arbitrary: mc)
  case 0
  then show ?case by (clarsimp simp add: bits_range_def)
next
  case (Suc h)
  moreover
  have \<open>mt_height (memory_contents_take_block (MT_tagged sh tag) (mc_right mc) h addr block_h) < Suc h\<close>
       \<open>mt_height (memory_contents_take_block (MT_tagged sh tag) (mc_left mc) h addr block_h) < Suc h\<close>
    by (simp_all add: Suc.prems(1) less_Suc_eq_le mc_left_height mc_right_height memory_contents_take_height_le)
  ultimately show ?case
    by (simp add: lookup_memory_tree_mt_node mc_left_height mc_right_height)
qed

lemma memory_contents_delete_lookup:
  assumes \<open>mc_height mc \<le> h\<close>
  and \<open>k = MT_tagged sh tag\<close>
  shows \<open>lookup_memory_tree (memory_contents_delete_block k mc h addr block_h) h x =
         (if x \<in> bits_range addr h block_h then Unmapped else lookup_memory_tree (k mc) h x)\<close>
  using assms
proof (induction h arbitrary: mc)
  case 0
  then show ?case by (clarsimp simp add: bits_range_def)
next
  case (Suc h)
  moreover
  have \<open>mt_height (memory_contents_delete_block (MT_tagged sh tag) (mc_right mc) h addr block_h) < Suc h\<close>
       \<open>mt_height (memory_contents_delete_block (MT_tagged sh tag) (mc_left mc) h addr block_h) < Suc h\<close>
       \<open>mc_height (mc_left mc) < Suc h\<close> \<open>mc_height (mc_right mc) < Suc h\<close>
    by (simp_all add: Suc.prems(1) less_Suc_eq_le mc_left_height mc_right_height memory_contents_delete_height_le)
  ultimately show ?case
    by (simp add: lookup_memory_tree_mt_node mc_left_height mc_right_height)
qed


lemma memory_tree_take_lookup:
  assumes \<open>mt_height mt \<le> h\<close>
  shows \<open>lookup_memory_tree (memory_tree_take_block mt h addr block_h) h x =
         (if x \<in> bits_range addr h block_h then lookup_memory_tree mt h x else Unmapped)\<close>
  using assms
proof (induction mt h addr block_h rule: memory_tree_take_block.induct)
  case (1 h addr block_h)
  then show ?case
    by auto
next
  case (2 sh tag mc h addr block_h)
  then show ?case
    by (simp add: memory_contents_take_lookup)
next
  case (3 n0 n1 h addr block_h)
  moreover
  have \<open>mt_height (memory_tree_take_block n1 (h - Suc 0) addr block_h) < h\<close>
    using 3 by (simp add: less_Suc_eq_le memory_tree_take_height_le split: nat_diff_split)
  ultimately show ?case
    by (simp add: less_Suc_eq_le lookup_memory_tree_mt_node memory_tree_take_height_le
        split: nat_diff_split_asm)
qed

lemma memory_tree_delete_lookup:
  assumes \<open>mt_height mt \<le> h\<close>
  shows \<open>lookup_memory_tree (memory_tree_delete_block mt h addr block_h) h x =
         (if x \<in> bits_range addr h block_h then Unmapped else lookup_memory_tree mt h x)\<close>
  using assms
proof (induction mt h addr block_h rule: memory_tree_delete_block.induct)
  case (3 n0 n1 h addr block_h)
  moreover
  have \<open>mt_height (memory_tree_delete_block n0 (h - Suc 0) addr block_h) < h\<close>
       \<open>mt_height (memory_tree_delete_block n1 (h - Suc 0) addr block_h) < h\<close>
    using 3 by (simp_all add: less_Suc_eq_le memory_tree_delete_height_le split: nat_diff_split)
  ultimately show ?case
    by (simp add: lookup_memory_tree_mt_node split: nat_diff_split_asm)
qed (auto simp add: memory_contents_delete_lookup)

lemma memory_tree_take_delete_lookup:
  assumes \<open>mt_height mt \<le> h\<close>
  shows \<open>lookup_memory_tree (memory_tree_take_block mt h addr block_h) h x +
         lookup_memory_tree (memory_tree_delete_block mt h addr block_h) h x =
         lookup_memory_tree mt h x\<close>
  using assms by (auto simp add: memory_tree_delete_lookup memory_tree_take_lookup)

section\<open>Physical memory as canonical tries\<close>

definition \<open>wf_memory_tree mt \<equiv>
  memory_tree_is_canonical mt \<and> mt_height mt \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>

typedef (overloaded) 'tag tagged_physical_memory =
  \<open>{ mt::'tag memory_tree. wf_memory_tree mt }\<close>
  by (intro exI [where x=\<open>MT_unmapped\<close>], simp add: memory_tree_is_canonical_def wf_memory_tree_def)

declare Abs_tagged_physical_memory_inject [simp]
declare Abs_tagged_physical_memory_inverse [simp]

setup_lifting type_definition_tagged_physical_memory

lift_definition physical_memory_lookup :: \<open>'tag tagged_physical_memory \<Rightarrow> 64 word \<Rightarrow> 'tag physical_byte_state\<close> is
  \<open>\<lambda>mt a.
     if a < PMEM_TRIE_ADDRESS_LIMIT then
       lookup_memory_tree mt PMEM_TRIE_ADDRESS_WIDTH a
     else Unmapped\<close> .

lift_definition physical_memory_tag_all_bytes :: \<open>8 word \<Rightarrow> nonempty_share \<Rightarrow> 'tag \<Rightarrow> 'tag tagged_physical_memory\<close> is
  \<open>\<lambda>b sh tag. MT_tagged sh tag (MC_byte b)\<close>
  by (clarsimp simp add: memory_contents_canonical_def wf_memory_tree_def)

lemma physical_memory_lookup_out_of_range:
  assumes \<open>pa \<ge> PMEM_TRIE_ADDRESS_LIMIT\<close>
  shows \<open>physical_memory_lookup \<sigma> pa = Unmapped\<close>
  using assms by (transfer; auto)

theorem physical_memory_ext:
  notes pmem_trie_bounds[simp]
  assumes \<open>\<And>addr. physical_memory_lookup x addr = physical_memory_lookup y addr\<close>
  shows \<open>x = y\<close>
proof -
  have *: \<open> \<lbrakk>\<And>addr. (if addr < 0x1000000000000 then lookup_memory_tree u 48 addr else Unmapped) =
               (if addr < 0x1000000000000 then lookup_memory_tree v 48 addr else Unmapped)\<rbrakk>
       \<Longrightarrow> lookup_memory_tree u 48 addr = lookup_memory_tree v 48 addr\<close> for u v addr
    apply (rule lookup_memory_tree_bound_eq; simp)
    apply meson
    done
  show ?thesis
    using assms
    apply (transfer; simp add: wf_memory_tree_def split: if_splits)
    unfolding PMEM_TRIE_ADDRESS_WIDTH_def
    using * memory_tree_unique by (metis numeral_le_iff semiring_norm(71,74,76))
qed

lemma pred_sumI [intro]:
  assumes \<open>\<And>l. x = Inl l \<Longrightarrow> P l\<close>
  and \<open>\<And>r. x = Inr r \<Longrightarrow> Q r\<close>
  shows \<open>pred_sum P Q x\<close>
  using assms by (simp add: setl.simps setr.simps sum.pred_set)

lift_definition (code_dt) physical_memory_memset_block ::
  \<open>'tag tagged_physical_memory \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 8 word \<Rightarrow> memory_fault + 'tag tagged_physical_memory\<close> is
  \<open>\<lambda>mt a block_h b.
     if a < PMEM_TRIE_ADDRESS_LIMIT \<and> block_h \<le> PMEM_TRIE_ADDRESS_WIDTH then
       memset_memory_tree_block mt PMEM_TRIE_ADDRESS_WIDTH a block_h b
     else Inl Unmapped_Address\<close>
  by (auto split: if_splits
           simp add: wf_memory_tree_def memset_memory_tree_block_height_le memset_memory_tree_block_canonical)

lift_definition (code_dt) physical_memory_tag_page ::
  \<open>'tag tagged_physical_memory \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 'tag \<Rightarrow> memory_fault + 'tag tagged_physical_memory\<close> is
  \<open>\<lambda>mt a block_h tag.
    if a < PMEM_TRIE_ADDRESS_LIMIT \<and> block_h \<le> PMEM_TRIE_ADDRESS_WIDTH then
      memory_tree_tag_page mt PMEM_TRIE_ADDRESS_WIDTH a block_h tag
    else
      Inl Unmapped_Address\<close>
  by (auto split: if_splits
           simp add: wf_memory_tree_def memory_tree_tag_page_height_le memory_tree_tag_page_canonical)

lift_definition (code_dt) physical_memory_take_block ::
  \<open>'tag tagged_physical_memory \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 'tag tagged_physical_memory\<close> is
  \<open>\<lambda>mt a block_h. memory_tree_take_block mt PMEM_TRIE_ADDRESS_WIDTH a block_h\<close>
  using memory_tree_take_canonical memory_tree_take_height_le by (auto simp add: wf_memory_tree_def)

lift_definition (code_dt) physical_memory_delete_block ::
  \<open>'tag tagged_physical_memory \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 'tag tagged_physical_memory\<close> is
  \<open>\<lambda>mt a block_h. memory_tree_delete_block mt PMEM_TRIE_ADDRESS_WIDTH a block_h\<close>
  using memory_tree_delete_canonical memory_tree_delete_height_le by (auto simp add: wf_memory_tree_def)

instantiation tagged_physical_memory :: (type) apart
begin
lift_definition zero_tagged_physical_memory :: \<open>'tag tagged_physical_memory\<close>
 is \<open>MT_unmapped\<close>
 by (clarsimp simp add: memory_tree_is_canonical_def wf_memory_tree_def)

lift_definition disjoint_tagged_physical_memory :: \<open>'tag tagged_physical_memory \<Rightarrow> 'tag tagged_physical_memory \<Rightarrow> bool\<close>
 is \<open>memory_tree_disjoint\<close> .

instance
proof (standard; transfer)
  fix x y :: \<open>'a memory_tree\<close>
  assume \<open>wf_memory_tree x\<close> \<open>wf_memory_tree y\<close>
  then show \<open>memory_tree_disjoint x y = memory_tree_disjoint y x\<close>
    using memory_tree_disjoint_sym by blast
next
  fix x :: \<open>'a memory_tree\<close>
  assume \<open>wf_memory_tree x\<close> \<open>memory_tree_disjoint x x\<close>
  then show \<open>x = MT_unmapped\<close>
    by (simp add: memory_tree_zero_unique wf_memory_tree_def)
qed auto

end

instantiation tagged_physical_memory :: (type) sepalg
begin
lift_definition (code_dt) plus_tagged_physical_memory :: \<open>'tag tagged_physical_memory \<Rightarrow> 'tag tagged_physical_memory \<Rightarrow> 'tag tagged_physical_memory\<close>
 is \<open>memory_tree_plus\<close>
 by (simp add: memory_tree_plus_canonical memory_tree_plus_height_le wf_memory_tree_def)

instance
  apply (standard; transfer)
  apply simp
  using memory_tree_plus_comm apply blast
  apply (simp add: memory_tree_plus_assoc wf_memory_tree_def)
  using memory_tree_apart_plus2 wf_memory_tree_def apply blast
  using memory_tree_apart_assoc2 wf_memory_tree_def apply blast
  done
end

instantiation tagged_physical_memory :: (type) strong_sepalg
begin
instance
proof (standard; transfer)
  fix x y z :: \<open>'a memory_tree\<close>
  assume \<open>wf_memory_tree x\<close> \<open>wf_memory_tree y\<close> \<open>wf_memory_tree z\<close> \<open>memory_tree_disjoint x y\<close>
  then show \<open>memory_tree_disjoint (memory_tree_plus x y) z = (memory_tree_disjoint y z \<and> memory_tree_disjoint x z)\<close>
    by (metis memory_tree_plus_strong1 memory_tree_plus_strong2 mt_plus_disjoint2 wf_memory_tree_def)
qed

end

instantiation tagged_physical_memory :: (type) cancellative_sepalg
begin
instance
  apply standard
  apply (rule physical_memory_ext)
  apply (transfer, clarsimp simp add: wf_memory_tree_def)
  by (metis memory_tree_plus_lookup memory_tree_lookup_disjoint sepalg_cancel)
end


lemma lookup_memory_tree_disjoint_eq:
  assumes \<open>\<And>addr. addr < 2^h \<Longrightarrow> lookup_memory_tree x h addr \<sharp> lookup_memory_tree y h addr\<close>
   and \<open>h < 64\<close>
  shows \<open>\<And>addr. lookup_memory_tree x h addr \<sharp> lookup_memory_tree y h addr\<close>
proof -
  fix addr :: \<open>64 word\<close>
  obtain addr' where \<open>addr' = addr AND mask h\<close> by simp
  moreover have \<open>(mask h :: 64 word) < 2^h\<close>
    using assms by (simp add: mask_lt_2pn)
  moreover from calculation have \<open>addr' < 2^h\<close>
    using word_and_less' by clarsimp
  moreover from calculation have \<open>\<And>n. n < h \<Longrightarrow> addr!!n = addr'!!n\<close>
    by clarsimp (metis bit_take_bit_iff take_bit_eq_mask)
  ultimately show \<open>lookup_memory_tree x h addr \<sharp> lookup_memory_tree y h addr\<close>
    using assms lookup_memory_tree_eq by (metis (no_types, lifting))
qed

theorem physical_memory_disjoint_eq:
  fixes x y :: \<open>'tag tagged_physical_memory\<close>
  shows \<open>x\<sharp>y = (\<forall>addr. physical_memory_lookup x addr \<sharp> physical_memory_lookup y addr)\<close>
  apply transfer
  apply (auto intro: memory_tree_lookup_disjoint simp add: wf_memory_tree_def)
  apply (intro memory_tree_lookup_disjoint2)
  apply (force intro: lookup_memory_tree_disjoint_eq simp add: pmem_trie_bounds)+
  done

theorem physical_memory_plus_eq:
  fixes x y :: \<open>'tag tagged_physical_memory\<close>
  assumes \<open>x\<sharp>y\<close>
  shows \<open>physical_memory_lookup (x+y) addr = physical_memory_lookup x addr + physical_memory_lookup y addr\<close>
  using assms by (transfer, auto intro: memory_tree_plus_lookup simp add: wf_memory_tree_def)


lemma physical_memory_lookup_local:
  assumes \<open>physical_memory_lookup x addr = a\<close> and \<open>x\<sharp>y\<close>
  shows \<open>\<exists>b. physical_memory_lookup (x+y) addr = (a+b) \<and> a\<sharp>b\<close>
  using assms by (meson physical_memory_disjoint_eq physical_memory_plus_eq)

lemma physical_memory_memset_block_InrE:
  assumes \<open>physical_memory_memset_block mem addr n b = Inr mem'\<close>
  obtains mt mt' where \<open>wf_memory_tree mt\<close> \<open>wf_memory_tree mt'\<close>
                       \<open>mem = Abs_tagged_physical_memory mt\<close>
                       \<open>mem' = Abs_tagged_physical_memory mt'\<close>
                       \<open>addr < PMEM_TRIE_ADDRESS_LIMIT\<close> \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
                       \<open>memset_memory_tree_block mt PMEM_TRIE_ADDRESS_WIDTH addr n b = Inr mt'\<close>
  using assms
  by (metis Rep_tagged_physical_memory Rep_tagged_physical_memory_inverse map_sum.simps(2) 
        mem_Collect_eq physical_memory_memset_block.rep_eq sum.simps(4))

lemma physical_memory_tag_block_result:
 notes pmem_trie_bounds[simp]
 fixes m :: \<open>'a tagged_physical_memory\<close>
 assumes \<open>physical_memory_tag_page mem addr n tag = Inr mem'\<close>
 shows \<open>physical_memory_lookup mem' x =
         (if x \<in> block_range addr n then tag_byte_state tag (physical_memory_lookup mem x) else physical_memory_lookup mem x)\<close>
  using assms
  by (transfer, auto split: if_splits simp add: memory_tree_tag_page_result
    block_range_to_bits wf_memory_tree_def)

lemma state_to_class_elim1:
  assumes \<open>state_to_class s = Shared_Value sh tag\<close>
  obtains b where \<open>s = Tagged sh tag b\<close>
  using assms by (cases s; auto)

lemma state_to_class_elim2:
  assumes \<open>Shared_Value sh tag = state_to_class s\<close>
  obtains b where \<open>s = Tagged sh tag b\<close>
  by (metis assms state_to_class_elim1)

lemmas state_to_class_elims = state_to_class_elim1 state_to_class_elim2

lemma physical_memory_memset_block_result:
  assumes \<open>physical_memory_memset_block mem addr n b = Inr mem'\<close>
   shows \<open>physical_memory_lookup mem' x =
            (if x \<in> block_range addr n then set_byte_state (physical_memory_lookup mem x) b else physical_memory_lookup mem x)\<close>
using assms
  memory_tree_memset_block_lookup[of \<open>Rep_tagged_physical_memory mem\<close> \<open>PMEM_TRIE_ADDRESS_WIDTH\<close> \<open>addr\<close> n b \<open>Rep_tagged_physical_memory mem'\<close> \<open>x\<close>]
  memory_tree_memset_block_lookup_diff[of \<open>Rep_tagged_physical_memory mem\<close> \<open>PMEM_TRIE_ADDRESS_WIDTH\<close> \<open>addr\<close> n b \<open>Rep_tagged_physical_memory mem'\<close> \<open>x\<close>]
  memory_tree_memset_block_lookup_class[of \<open>Rep_tagged_physical_memory mem\<close> \<open>PMEM_TRIE_ADDRESS_WIDTH\<close> \<open>addr\<close> n b \<open>Rep_tagged_physical_memory mem'\<close> \<open>x\<close>]
  apply (auto elim!: physical_memory_memset_block_InrE state_to_class_elims
       simp add: physical_memory_lookup.rep_eq set_byte_state_def Abs_tagged_physical_memory_inverse wf_memory_tree_def
                  block_range_to_bits bits_range_def
       split: shareable_value.splits)
  apply (simp add: map_shareable_value_def)+
  done

lemma word_align_down_transfer_lt:
  assumes \<open>x \<in> block_range addr n\<close>
      and \<open>addr < t\<close>
      and \<open>is_aligned t n\<close>
    shows \<open>x < t\<close>
    using assms is_aligned_neg_mask_eq [OF \<open>is_aligned t n\<close>]
    by (simp add: block_range_def) (metis neg_mask_mono_le word_and_less' word_bw_comms(1) word_le_not_less)


term is_owned_with_other_tag
lemma physical_memory_tag_page_succeeds:
  assumes \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
  shows
   \<open>(\<forall>x \<in> block_range addr n. is_owned_with_other_tag tag (state_to_class (physical_memory_lookup mem x))) \<longleftrightarrow>
    (\<exists>m. physical_memory_tag_page mem addr n tag = Inr m)\<close>
proof -
  \<comment>\<open>First, we prove the underlying statement about memory trees, which is almost but not
    quite what we proved above. Then, we use transfer to prove the goal case by case.\<close>
  { fix mem :: \<open>'a memory_tree\<close> 
    assume \<open>wf_memory_tree mem\<close>
      and \<section>: \<open>(\<forall>x \<in> block_range addr n.
                is_owned_with_other_tag tag (state_to_class  (if x < PMEM_TRIE_ADDRESS_LIMIT then
                                 lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x
                               else Unmapped)))\<close>
    have if_simp: \<open>\<And>P x. is_owned_with_other_tag tag (state_to_class ( (if P then x else Unmapped))) =
        (P \<and> is_owned_with_other_tag tag (state_to_class x))\<close>
      using is_owned_with_other_tagE by force
    have \<open>\<exists>mem'. memory_tree_tag_page mem PMEM_TRIE_ADDRESS_WIDTH addr n tag = Inr mem'\<close>
    proof (intro memory_tree_tag_page_succeeds1 strip)
      fix x :: \<open>64 word\<close>
      assume \<open>x \<in> bits_range addr PMEM_TRIE_ADDRESS_WIDTH n\<close>
        and \<open>x < 2 ^ PMEM_TRIE_ADDRESS_WIDTH\<close>
      then show \<open>is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x))\<close>
        by (metis \<section> PMEM_TRIE_ADDRESS_LIMIT_def assms block_range_includes block_range_to_bits if_simp)
    next
      show \<open>(PMEM_TRIE_ADDRESS_WIDTH::nat) < 64\<close>
        by (simp add: PMEM_TRIE_ADDRESS_WIDTH_def)
    next
      show \<open>mt_height mem \<le> PMEM_TRIE_ADDRESS_WIDTH\<close> \<open>memory_tree_is_canonical mem\<close>
        using \<section> wf_memory_tree_def \<open>wf_memory_tree mem\<close> by blast+
    qed
    then obtain mem' where mem': \<open>memory_tree_tag_page mem PMEM_TRIE_ADDRESS_WIDTH addr n tag = Inr mem'\<close> by blast
    with \<open>wf_memory_tree mem\<close> \<section> have \<open>wf_memory_tree mem'\<close>
      by (metis memory_tree_tag_page_canonical memory_tree_tag_page_height_le wf_memory_tree_def)
    with mem' \<section> have \<open>\<exists>mem'. wf_memory_tree mem' \<and> (if addr < PMEM_TRIE_ADDRESS_LIMIT \<and> n \<le> PMEM_TRIE_ADDRESS_WIDTH then
              memory_tree_tag_page mem PMEM_TRIE_ADDRESS_WIDTH addr n tag
           else Inl Unmapped_Address) = Inr mem'\<close>
      using assms block_range_includes if_simp by auto
  }
  then have
     A: \<open>(\<forall>x \<in> block_range addr n. is_owned_with_other_tag tag (state_to_class (physical_memory_lookup mem x)))
      \<Longrightarrow> (\<exists>m. physical_memory_tag_page mem addr n tag = Inr m)\<close>
  proof (induction mem)
    case (Abs_tagged_physical_memory y)
    then show ?case
      apply (clarsimp simp: physical_memory_lookup.rep_eq eq_onp_same_args physical_memory_tag_page.abs_eq)
      by (metis Abs_tagged_physical_memory.hyps Abs_tagged_physical_memory_inverse Inl_Inr_False map_sum.simps(2))
  qed
  have B:
    \<open>(\<forall>x \<in> block_range addr n.
         is_owned_with_other_tag tag (state_to_class (if x < PMEM_TRIE_ADDRESS_LIMIT then
                                 lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x
                               else Unmapped)))\<close>
    if mem: \<open>wf_memory_tree mem\<close> 
      \<open>\<exists>mem'. (wf_memory_tree mem' \<and> (if addr < PMEM_TRIE_ADDRESS_LIMIT \<and> n \<le> PMEM_TRIE_ADDRESS_WIDTH then
              memory_tree_tag_page mem PMEM_TRIE_ADDRESS_WIDTH addr n tag
           else Inl Unmapped_Address) = Inr mem')\<close>
    for mem :: \<open>'a memory_tree\<close> 
  proof -
    have writeable_simp: \<open>\<And>P r. is_owned_with_other_tag tag (state_to_class (if P then r else Unmapped))
                                    = (P \<and> is_owned_with_other_tag tag (state_to_class r))\<close>
      using is_owned_with_other_tagE by force
    obtain mem' 
      where mem': \<open>wf_memory_tree mem'\<close> \<open>addr < PMEM_TRIE_ADDRESS_LIMIT\<close> 
        \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close> 
        \<open>memory_tree_tag_page mem PMEM_TRIE_ADDRESS_WIDTH addr n tag = Inr mem'\<close>
      by (metis (no_types, lifting) mem sum_if_cases)
    with \<open>wf_memory_tree mem\<close> 
    have *: \<open>\<forall>x \<in> bits_range addr PMEM_TRIE_ADDRESS_WIDTH n. x < 2^PMEM_TRIE_ADDRESS_WIDTH \<longrightarrow>
          is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x))\<close>
      by (subst memory_tree_tag_page_succeeds[where tag=tag]; clarsimp simp add:
          PMEM_TRIE_ADDRESS_WIDTH_def wf_memory_tree_def)
    show ?thesis
    proof -
      have \<open>x < PMEM_TRIE_ADDRESS_LIMIT\<close> if \<open>x \<in> block_range addr n\<close> for x 
        using that mem'
        by (metis PMEM_TRIE_ADDRESS_LIMIT_def is_aligned_power2 word_align_down_transfer_lt)
      moreover have \<open>is_owned_with_other_tag tag (state_to_class (lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x))\<close>
        if \<open>x \<in> block_range addr n\<close> for x
        using that mem' calculation *
        by (metis PMEM_TRIE_ADDRESS_LIMIT_def assms block_range_to_bits_core(1)) 
      ultimately show ?thesis
        by (auto simp add: writeable_simp)
    qed
  qed
  have
    \<open>x \<in> block_range addr n \<Longrightarrow>
     physical_memory_tag_page mem addr n tag = Inr m \<Longrightarrow> 
     is_owned_with_other_tag tag
                (state_to_class (physical_memory_lookup mem x))\<close> for x m
  proof (induction mem)
    case (Abs_tagged_physical_memory y)
    then have \<open>x < PMEM_TRIE_ADDRESS_LIMIT\<close>
      by (metis Inl_Inr_False PMEM_TRIE_ADDRESS_LIMIT_def is_aligned_power2 map_sum.simps(2) physical_memory_tag_page.rep_eq word_align_down_transfer_lt)
    then obtain mem' where \<open>wf_memory_tree mem'\<close> \<open>memory_tree_tag_page y PMEM_TRIE_ADDRESS_WIDTH addr n tag =
        Inr mem'\<close>
      using Abs_tagged_physical_memory physical_memory_tag_page.rep_eq[of "Abs_tagged_physical_memory y" addr n tag]
      apply (simp add: split: if_splits)
      by (metis Rep_tagged_physical_memory mem_Collect_eq)
    moreover have \<open>addr < PMEM_TRIE_ADDRESS_LIMIT\<close>
      by (metis Abs_tagged_physical_memory.prems(2) Inl_Inr_False map_sum.simps(2) physical_memory_tag_page.rep_eq)
    ultimately show ?case
      using Abs_tagged_physical_memory B[of y] assms
      by (auto simp add: eq_onp_same_args physical_memory_lookup.abs_eq split: if_splits)
  qed
  with A show ?thesis by auto
qed

lemma physical_memory_memset_block_succeeds:
  assumes \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
  shows
   \<open>(\<forall>x \<in> block_range addr n. writeable_byte_state (physical_memory_lookup mem x)) \<longleftrightarrow>
    (\<exists>m. physical_memory_memset_block mem addr n b = Inr m)\<close>
proof -
  \<comment>\<open>First, we prove the underlying statement about memory trees, which is almost but not
    quite what we proved above. Then, we use transfer to prove the goal case by case.\<close>
  have *: \<open>\<exists>mem'. wf_memory_tree mem' \<and> (if addr < PMEM_TRIE_ADDRESS_LIMIT \<and> n \<le> PMEM_TRIE_ADDRESS_WIDTH then
              memset_memory_tree_block mem PMEM_TRIE_ADDRESS_WIDTH addr n b
           else Inl Unmapped_Address) = Inr mem'\<close>
    if \<open>wf_memory_tree mem\<close> 
     and \<open>(\<forall>x \<in> block_range addr n.
                   writeable_byte_state (if x < PMEM_TRIE_ADDRESS_LIMIT then
                                           lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x
                                         else Unmapped))\<close>
   for mem :: \<open>'a memory_tree\<close> 
  proof - 
    have if_simp: \<open>\<And>P x. (writeable_byte_state (if P then x else Unmapped)) = (P \<and> writeable_byte_state x)\<close>
      by force
    have \<open>\<exists>mem'. memset_memory_tree_block mem PMEM_TRIE_ADDRESS_WIDTH addr n b = Inr mem'\<close>
    proof (intro memory_tree_memset_block_succeeds1 strip)
      show \<open>PMEM_TRIE_ADDRESS_WIDTH < 64\<close>
        by (simp add: PMEM_TRIE_ADDRESS_WIDTH_def)
    next
      show \<open>memory_tree_is_canonical mem\<close> \<open>mt_height mem \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
        using \<open>wf_memory_tree mem\<close> wf_memory_tree_def by force+
    next
      show \<open>\<And>x. x \<in> bits_range addr PMEM_TRIE_ADDRESS_WIDTH n \<Longrightarrow>
                x < 2 ^ PMEM_TRIE_ADDRESS_WIDTH \<Longrightarrow> 
                writeable_byte_state (lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x)\<close>
        using block_range_includes block_range_to_bits assms that
        by (simp add: if_simp flip: PMEM_TRIE_ADDRESS_LIMIT_def)
    qed
    then obtain mem' where mem': \<open>memset_memory_tree_block mem PMEM_TRIE_ADDRESS_WIDTH addr n b = Inr mem'\<close> ..
    then have \<open>wf_memory_tree mem'\<close>
      using \<open>wf_memory_tree mem\<close> memset_memory_tree_block_canonical memset_memory_tree_block_height_le wf_memory_tree_def by blast
    with mem' show ?thesis
      by (metis (mono_tags, lifting) assms block_range_includes that(2) shareable_value.case(2))
  qed
  have A: \<open>(\<forall>x \<in> block_range addr n. writeable_byte_state (physical_memory_lookup mem x)) \<Longrightarrow>
         (\<exists>m. physical_memory_memset_block mem addr n b = Inr m)\<close>
  proof (induction mem)
    case (Abs_tagged_physical_memory y)                 
    with * [of y] Abs_tagged_physical_memory show ?case
      by (auto simp add: eq_onp_same_args physical_memory_memset_block.abs_eq physical_memory_lookup.rep_eq split: if_splits)
  qed
  have **: \<open>(\<forall>x \<in> block_range addr n.
         writeable_byte_state (if x < PMEM_TRIE_ADDRESS_LIMIT then
                                 lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x
                               else Unmapped))\<close>
    if \<open>wf_memory_tree mem\<close> and
      \<open>\<exists>mem'. (wf_memory_tree mem' \<and> (if addr < PMEM_TRIE_ADDRESS_LIMIT \<and> n \<le> PMEM_TRIE_ADDRESS_WIDTH then
              memset_memory_tree_block mem PMEM_TRIE_ADDRESS_WIDTH addr n b
           else Inl Unmapped_Address) = Inr mem')\<close>
    for mem :: \<open>'a memory_tree\<close>
  proof -
    have writeable_simp: \<open>\<And>P r. writeable_byte_state (if P then r else Unmapped) = (P \<and> writeable_byte_state r)\<close> by auto
    from that obtain mem'
      where mem': \<open>wf_memory_tree mem'\<close> \<open>addr < PMEM_TRIE_ADDRESS_LIMIT\<close>  
                  \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close> 
                  \<open>memset_memory_tree_block mem PMEM_TRIE_ADDRESS_WIDTH addr n b = Inr mem'\<close>
      by (metis (no_types, lifting) sum_if_cases)
    with \<open>wf_memory_tree mem\<close> 
    have \<section>: \<open>\<forall>x \<in> bits_range addr PMEM_TRIE_ADDRESS_WIDTH n. x < 2^PMEM_TRIE_ADDRESS_WIDTH \<longrightarrow> 
                  writeable_byte_state (lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x)\<close>
      by (subst memory_tree_memset_block_succeeds[where b=b]; 
          clarsimp simp add: PMEM_TRIE_ADDRESS_WIDTH_def wf_memory_tree_def)
    show ?thesis
      unfolding writeable_simp
    proof (intro conjI strip)
      fix x
      assume x: \<open>x \<in> block_range addr n\<close>
      then show \<open>x < PMEM_TRIE_ADDRESS_LIMIT\<close>
        by (metis PMEM_TRIE_ADDRESS_LIMIT_def assms is_aligned_power2 mem'(2) word_align_down_transfer_lt)
      then show \<open>writeable_byte_state (lookup_memory_tree mem PMEM_TRIE_ADDRESS_WIDTH x)\<close>
        by (metis \<section> PMEM_TRIE_ADDRESS_LIMIT_def assms block_range_to_bits mem'(2) x)
    qed
  qed
  have
    \<open>physical_memory_memset_block mem addr n b = Inr m \<Longrightarrow>
       x \<in> block_range addr n \<Longrightarrow> writeable_byte_state (physical_memory_lookup mem x)\<close> for m x
  proof (induction mem)
    case (Abs_tagged_physical_memory y)
    then have \<open>x < PMEM_TRIE_ADDRESS_LIMIT\<close>
      by (metis PMEM_TRIE_ADDRESS_LIMIT_def is_aligned_power2 physical_memory_memset_block_InrE word_align_down_transfer_lt)
    then show ?case
      using Abs_tagged_physical_memory ** [of y] assms 
      by (auto simp add: physical_memory_lookup.rep_eq split: if_splits elim!: physical_memory_memset_block_InrE)
  qed
  with A show ?thesis by auto
qed

lemma physical_memory_take_delete_disjoint:
  shows \<open>physical_memory_take_block m pa n \<sharp> physical_memory_delete_block m pa n\<close>
  using memory_tree_take_delete_disjoint[where 'a='a]
  by (transfer, clarsimp simp add: wf_memory_tree_def)

lemma physical_memory_lookup_take_delete:
  shows \<open>physical_memory_lookup (physical_memory_take_block m pa n) addr +
       physical_memory_lookup (physical_memory_delete_block m pa n) addr =
       physical_memory_lookup m addr\<close>
  apply transfer
  using memory_tree_take_delete_lookup by (force simp add: wf_memory_tree_def)

lemma physical_memory_take_delete_eq:
  shows \<open>physical_memory_take_block m pa n + physical_memory_delete_block m pa n = m\<close>
  by (metis physical_memory_ext physical_memory_lookup_take_delete physical_memory_plus_eq physical_memory_take_delete_disjoint)

lemma physical_memory_take_lookup:
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close> and \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
  shows \<open>physical_memory_lookup (physical_memory_take_block m pa n) x =
          (if x \<in> block_range pa n then physical_memory_lookup m x else Unmapped)\<close>
  using assms block_range_to_bits[of pa x n]
  by (transfer, auto split: if_splits simp add: PMEM_TRIE_ADDRESS_WIDTH_def memory_tree_take_lookup wf_memory_tree_def)

lemma physical_memory_delete_lookup:
  assumes \<open>pa < PMEM_TRIE_ADDRESS_LIMIT\<close> and \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
  shows \<open>physical_memory_lookup (physical_memory_delete_block m pa n) x =
          (if x \<in> block_range pa n then Unmapped else physical_memory_lookup m x)\<close>
  using assms block_range_to_bits[of pa x n]
  by (transfer, auto split: if_splits simp add: PMEM_TRIE_ADDRESS_WIDTH_def memory_tree_delete_lookup wf_memory_tree_def)

lemma physical_memory_tag_all_bytes_lookup:
  shows \<open>physical_memory_lookup (physical_memory_tag_all_bytes b sh tag) x =
        (if x < PMEM_TRIE_ADDRESS_LIMIT then Shared_Value sh (tag, b) else Unmapped)\<close>
proof -
have \<open>eq_onp wf_memory_tree (MT_tagged sh tag (MC_byte b))
     (MT_tagged sh tag (MC_byte b))\<close>
  by (auto simp: eq_onp_same_args memory_tree_is_canonical_def wf_memory_tree_def)
  then show ?thesis
    by (simp add: physical_memory_lookup.rep_eq physical_memory_tag_all_bytes.rep_eq)
qed

lemma physical_memory_tag_page_local:
  assumes \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
    and m1: \<open>physical_memory_tag_page m1 adr n tag = Inr m1'\<close> and \<open>m1\<sharp>m2\<close>
  shows \<open>physical_memory_tag_page (m1+m2) adr n tag = Inr (m1'+m2) \<and> m1'\<sharp>m2\<close>
proof 
  have A: \<open>\<forall>x \<in> block_range adr n. is_owned_with_other_tag tag (state_to_class (physical_memory_lookup m1 x))\<close>
    using assms physical_memory_tag_page_succeeds by fast
  with assms 
  have B: \<open>is_owned_with_other_tag tag (state_to_class (physical_memory_lookup (m1+m2) x))\<close>
    if \<open>x \<in> block_range adr n\<close> for x
    using that
    apply (clarsimp simp add: physical_memory_plus_eq is_owned_with_other_tag_def state_to_class_def map_shareable_value_def)
    apply (cases \<open>physical_memory_lookup m1 x\<close>; cases \<open>physical_memory_lookup m2 x\<close>)
    using plus_nonempty_share.rep_eq apply auto
    done
  then obtain mem' where mem': \<open>physical_memory_tag_page (m1+m2) adr n tag = Inr mem'\<close>
    by (meson assms(1) physical_memory_tag_page_succeeds)
  show \<open>m1'\<sharp>m2\<close>
  proof (clarsimp simp add: physical_memory_disjoint_eq)
    fix addr
    have C: \<open>physical_memory_lookup m1 addr \<sharp> physical_memory_lookup m2 addr\<close>
      using assms(3) physical_memory_disjoint_eq by blast
    then have \<open>\<And>sh a b. \<lbrakk>physical_memory_lookup m2 addr = Tagged sh a b\<rbrakk> \<Longrightarrow> physical_memory_lookup m1' addr \<sharp> Tagged sh a b\<close>
      by (metis A is_owned_with_other_tagE m1 physical_memory_tag_block_result shareable_value.simps(3) state_to_class_elim1
          tagged_disjoint_lemma')
    then show \<open>physical_memory_lookup m1' addr \<sharp> physical_memory_lookup m2 addr\<close>
      by (metis A C disjoint_sym is_owned_with_other_tagE m1
          physical_memory_tag_block_result shareable_value_disjoint_top(2) state_to_class_elim1 zero_disjoint)
  qed
  have \<open>mem' = m1'+m2\<close>
  proof (intro physical_memory_ext strip)
    fix addr
    show \<open>physical_memory_lookup mem' addr = physical_memory_lookup (m1' + m2) addr\<close>
      using physical_memory_tag_block_result[of m1 adr n tag _ addr] \<open>m1\<sharp>m2\<close> \<open>m1'\<sharp>m2\<close> A
      apply (simp add: m1 physical_memory_tag_block_result[OF mem'] physical_memory_plus_eq split: if_splits)
      by (metis is_owned_with_other_tagE no_value_unit physical_memory_disjoint_eq shareable_value_disjoint_top(1) state_to_class_elim2)
  qed
  with \<open>m1'\<sharp>m2\<close> mem' show \<open>physical_memory_tag_page (m1+m2) adr n tag = Inr (m1'+m2)\<close> by blast
qed

lemma physical_memory_memset_block_local:
  assumes \<open>n \<le> PMEM_TRIE_ADDRESS_WIDTH\<close>
    and m1: \<open>physical_memory_memset_block m1 adr n b = Inr m1'\<close> and \<open>m1\<sharp>m2\<close>
  shows \<open>physical_memory_memset_block (m1+m2) adr n b = Inr (m1'+m2) \<and> m1'\<sharp>m2\<close>
proof 
  have *: \<open>(\<forall>x \<in> block_range adr n. writeable_byte_state (physical_memory_lookup m1 x))\<close>
    using assms physical_memory_memset_block_succeeds by blast
  then have \<open>(\<forall>x \<in> block_range adr n. writeable_byte_state (physical_memory_lookup (m1+m2) x))\<close>
    using assms
    by (metis no_value_unit physical_memory_lookup_local writeable_byte_state_disjoint)
  then obtain mem' where mem': \<open>physical_memory_memset_block (m1+m2) adr n b = Inr mem'\<close>
    using assms physical_memory_memset_block_succeeds[of n adr \<open>m1+m2\<close> b] by clarsimp
  with assms show \<open>m1'\<sharp>m2\<close>
    using physical_memory_memset_block_result[OF m1] *
    by (metis disjoint_sharable_valueI physical_memory_disjoint_eq writeable_byte_state_disjoint)
  have \<open>mem' = m1'+m2\<close>
  proof (intro physical_memory_ext strip)
    fix addr
    show \<open>physical_memory_lookup mem' addr = physical_memory_lookup (m1' + m2) addr\<close>
      using physical_memory_memset_block_result[of m1 adr n b m1' addr] \<open>m1\<sharp>m2\<close> \<open>m1'\<sharp>m2\<close> *
      apply (simp add: physical_memory_plus_eq m1 physical_memory_memset_block_result[OF mem'] split: if_splits)
      by (metis no_value_unit physical_memory_disjoint_eq writeable_byte_state_disjoint)
  qed
  with mem' show \<open>physical_memory_memset_block (m1+m2) adr n b = Inr (m1'+m2)\<close>
    by blast
qed

(*<*)
end
(*>*)
