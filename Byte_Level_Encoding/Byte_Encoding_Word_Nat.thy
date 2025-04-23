(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Byte_Encoding_Word_Nat
  imports "HOL-Library.Word" Lenses_And_Other_Optics.Lenses_And_Other_Optics "HOL-Library.Code_Target_Numeral" Misc.Array
begin
(*>*)

section\<open>Byte encoding for natural numbers and words\<close>

text\<open>This section develops basic material about converting between unsigned numbers (nats or words)
and byte lists. We consider both little-endian and big-endian presentations.\<close>

subsection\<open>Interpreting byte lists as natural numbers\<close>

text\<open>We begin by introducing little and big endian interpretations of byte lists as natural numbers.\<close>

type_synonym byte = \<open>8 word\<close>

definition BYTE_LIMIT :: nat where
  \<open>BYTE_LIMIT \<equiv> 256\<close>

definition shift_insert_byte :: \<open>byte \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>shift_insert_byte b n \<equiv> unat b + BYTE_LIMIT * n\<close>

lemma shift_insert_byte_correct:
  shows \<open>word_of_nat (shift_insert_byte b n mod 256) = b\<close> (is ?g1)
    and \<open>shift_insert_byte b n div 256 = n\<close> (is ?g2)
proof -
  have \<open>unat b < 256\<close>
    using unsigned_less[where 'b=8] by simp
  from this show \<open>?g1\<close> and \<open>?g2\<close>
    by (auto simp add: shift_insert_byte_def BYTE_LIMIT_def)
qed

text\<open>Big endian interpretation of byte lists as natural numbers:\<close>
definition byte_list_to_nat_be :: \<open>byte list \<Rightarrow> nat\<close> where
  \<open>byte_list_to_nat_be bs \<equiv> fold shift_insert_byte bs 0\<close>

text\<open>Little endian interpretation of byte lists as natural numbers:\<close>
definition byte_list_to_nat_le :: \<open>byte list \<Rightarrow> nat\<close> where
  \<open>byte_list_to_nat_le bs \<equiv> foldr shift_insert_byte bs 0\<close>

text\<open>The little endian interpretation of a byte list is the big endian
presentation of its reverse:\<close>

named_theorems byte_encoding_be_le
named_theorems byte_encoding_le_be

lemma byte_list_to_nat_le_be:
  shows [byte_encoding_le_be]: \<open>byte_list_to_nat_le bs = byte_list_to_nat_be (rev bs)\<close>
by (simp add: byte_list_to_nat_be_def byte_list_to_nat_le_def foldr_conv_fold)

lemma byte_list_to_nat_be_le:
  shows [byte_encoding_be_le]: \<open>byte_list_to_nat_be bs = byte_list_to_nat_le (rev bs)\<close>
by (simp add: byte_list_to_nat_le_be)

text\<open>The following is useful for inductive reasoning about little endian interpretations:\<close>
lemma byte_list_to_nat_le_cases:
  shows \<open>byte_list_to_nat_le [] = 0\<close>
    and \<open>byte_list_to_nat_le (b # bs) = shift_insert_byte b (byte_list_to_nat_le bs)\<close>
by (auto simp add: byte_list_to_nat_le_def)

text\<open>The following gives a bound on the absolute value of the little and big endian
interpretations:\<close>
lemma byte_list_to_nat_le_bound:
  shows \<open>byte_list_to_nat_le bs < 256^(length bs)\<close>
proof -
  {
       fix b :: byte
       and k :: nat
       and n :: nat
    assume \<open>n < 256^k\<close>
    have \<open>unat b < 256\<close>
      using unsigned_less[where 'b=8] by simp
    from \<open>n < 256^k\<close> have \<open>256 + 256 * n \<le> 256 * 256^k\<close>
      by linarith
    from this have \<open>\<And>b. b < 256 \<Longrightarrow> b + 256 * n < 256 * 256^k\<close>
      by fastforce
    from this and \<open>unat b < 256\<close> have \<open>unat b + 256 * n < 256 * 256^k\<close>
      by fastforce
  }
  from this show ?thesis
    by (induction bs; simp add: byte_list_to_nat_le_cases shift_insert_byte_def BYTE_LIMIT_def)
qed

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma byte_list_to_nat_be_bound:
  shows \<open>byte_list_to_nat_be bs < 256^(length bs)\<close>
using byte_list_to_nat_le_bound[where bs=\<open>rev bs\<close>] by (simp add: byte_list_to_nat_be_le)

text\<open>The bounds established above are tight:\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma byte_list_to_nat_le_max:
  shows \<open>byte_list_to_nat_le (replicate n 0xFF) = (256^n) - 1\<close>
proof -
  {
       fix x :: \<open>nat\<close>
    assume \<open>x > 0\<close>
    from this have \<open>255 + 256 * (x - 1) = 256*x - 1\<close>
      by linarith
  }
  from this show ?thesis
    by (induction n; simp add: byte_list_to_nat_le_cases shift_insert_byte_def BYTE_LIMIT_def)
qed

subsection\<open>Encoding natural numbers as byte lists\<close>

text\<open>Next, we define the little and big endian encodings of natural numbers as byte lists.

First, the big endian case. We provide a minimal length for the encoding.\<close>

fun nat_to_nat_byte_list_be :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>nat_to_nat_byte_list_be n min_len = (
      if n = 0 then
         replicate min_len 0
      else
        let b  = n mod 256 in
        let n' = n div 256 in
           nat_to_nat_byte_list_be n' (min_len - 1) @ [b])\<close>
declare nat_to_nat_byte_list_be.simps[simp del]

text\<open>Next, the little endian encoding. Again, we provide a minimal length.\<close>

fun nat_to_nat_byte_list_le :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>nat_to_nat_byte_list_le n min_len = (
      if n = 0 then
         replicate min_len 0
      else
        let b  = n mod 256 in
        let n' = n div 256 in
           b # (nat_to_nat_byte_list_le n' (min_len - 1)))\<close>
declare nat_to_nat_byte_list_le.simps[simp del]

text\<open>The following two lemmas are useful for inductive proofs:\<close>
lemma nat_to_nat_byte_list_be_cases:
  shows \<open>nat_to_nat_byte_list_be 0 min_len = replicate min_len 0\<close>
   and \<open>n \<noteq> 0 \<Longrightarrow> nat_to_nat_byte_list_be n min_len =
          nat_to_nat_byte_list_be (n div 256) (min_len - 1) @ [n mod 256]\<close>
by (simp add: nat_to_nat_byte_list_be.simps) (subst nat_to_nat_byte_list_be.simps; simp)

lemma nat_to_nat_byte_list_le_cases:
  shows \<open>nat_to_nat_byte_list_le 0 min_len = replicate min_len 0\<close>
    and \<open>n \<noteq> 0 \<Longrightarrow> nat_to_nat_byte_list_le n min_len =
            n mod 256#nat_to_nat_byte_list_le (n div 256) (min_len - 1)\<close>
by (simp add: nat_to_nat_byte_list_le.simps) (subst nat_to_nat_byte_list_le.simps; simp)

text\<open>The i-th element of the little endian encoding can be explicitly described
as a coefficient in the \<^verbatim>\<open>256\<close>-adic presentation of the input:\<close>
\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma nat_to_nat_byte_list_le_nth:
  assumes \<open>i < length (nat_to_nat_byte_list_le n min_len)\<close>
    shows \<open>nat_to_nat_byte_list_le n min_len ! i = n div 256^i mod 256\<close>
  using assms
proof (induction i arbitrary: n min_len)
  case 0
  then show ?case
    by (cases \<open>n = 0\<close>; simp add: nat_to_nat_byte_list_le_cases)
next
  case (Suc i)
  then show ?case
    by (cases \<open>n = 0\<close>; simp add: div_mult2_eq nat_to_nat_byte_list_le_cases)
qed

text\<open>The following recursive description of \<^term>\<open>nat_to_nat_byte_list_le\<close>
can sometimes be easier to reason about:\<close>
lemma nat_to_nat_byte_list_le_cases_alt:
  assumes \<open>min_len \<noteq> 0\<close>
    shows \<open>nat_to_nat_byte_list_le n min_len =
             n mod 256#nat_to_nat_byte_list_le (n div 256) (min_len - 1)\<close>
using assms by (induction min_len arbitrary: n; simp; case_tac \<open>n = 0\<close>; simp add: nat_to_nat_byte_list_le_cases)

text\<open>As intended, the \<^verbatim>\<open>min_len\<close> argument is indeed a lower bound on the length of the
little endian interpretation:\<close>

lemma nat_to_nat_byte_list_le_len_bound_lower:
  shows \<open>length (nat_to_nat_byte_list_le n min_len) \<ge> min_len\<close>
by (induction min_len arbitrary: n; simp add: nat_to_nat_byte_list_le_cases_alt)

text\<open>Next, we establish an upper bound for the length of the little endian interpretation.
The following two lemmas are technical helpers that can be safely skipped.\<close>
lemma div256_smaller:
    fixes n k :: nat
  assumes \<open>k > 0\<close>
      and \<open>n < 256^k\<close>
    shows \<open>n div 256 < 256^(k-1)\<close>
proof -
  from assms have \<open>n div 256 * 256 < 256^k\<close>
    by linarith
  from this and assms show ?thesis
    by (metis less_mult_imp_div_less power_minus_mult)
qed

lemma suc_le_maxI:
    fixes x a b :: nat
  assumes \<open>a > 0\<close>
      and \<open>x \<le> max (a-1) (b-1)\<close>
    shows \<open>Suc x \<le> max a b\<close>
using assms by linarith

text\<open>The desired upper bound on the length of the little endian interpretation:\<close>

lemma nat_to_nat_byte_list_le_len_bound_upper:
  assumes \<open>n < 256^k\<close>
    shows \<open>length (nat_to_nat_byte_list_le n min_len) \<le> max k min_len\<close>
  using assms 
proof (induct n arbitrary: k min_len rule: less_induct)
  case (less n k min_len)
  show ?case
  proof (cases \<open>n=0 \<or> k=0\<close>)
    case False
    let ?m = \<open>n div 256\<close>
    obtain \<open>?m < n\<close> \<open>?m < 256^(k-1)\<close>
      using False div256_smaller less.prems by auto
    with less have \<open>Suc (length (nat_to_nat_byte_list_le ?m (min_len - 1))) \<le> max k min_len\<close>
      by (metis False One_nat_def not_gr0 suc_le_maxI)
    then show ?thesis
      by (metis False One_nat_def Suc_eq_plus1 list.size(4) nat_to_nat_byte_list_le_cases(2))
  qed (use less.prems nat_to_nat_byte_list_le_cases in auto)
qed

corollary nat_to_nat_byte_list_le_len:
  assumes \<open>n < 2^(8*k)\<close>
    shows \<open>length (nat_to_nat_byte_list_le n k) = k\<close> (is \<open>?a = ?b\<close>)
proof -
  have \<open>?a \<ge> k\<close>
    by (simp add: nat_to_nat_byte_list_le_len_bound_lower)
  moreover from assms have \<open>n < 256^k\<close>
    by (simp add: power_mult)
  moreover from this and nat_to_nat_byte_list_le_len_bound_upper have
    \<open>?a \<le> max k k\<close>
    by blast
  ultimately show ?thesis
    by simp
qed

text\<open>As before, little and big endian encoding are related via list reversal:\<close>
lemma nat_to_nat_byte_list_le_be:
  shows [byte_encoding_le_be]: \<open>nat_to_nat_byte_list_le n min_len = rev (nat_to_nat_byte_list_be n min_len)\<close>
proof (induct n arbitrary: min_len rule: less_induct)
  case (less n)
  then show ?case by (cases \<open>n = 0\<close>; simp add: nat_to_nat_byte_list_be_cases nat_to_nat_byte_list_le_cases)
qed

lemma nat_to_nat_byte_list_be_le:
  shows [byte_encoding_be_le]: \<open>nat_to_nat_byte_list_be n min_len = rev (nat_to_nat_byte_list_le n min_len)\<close>
by (simp add: nat_to_nat_byte_list_le_be)

text\<open>This allows us to transfer the length bounds above to the big endian case as well:\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma nat_to_nat_byte_list_be_ben_bound_lower:
  shows \<open>length (nat_to_nat_byte_list_be n min_ben) \<ge> min_ben\<close>
by (simp add: nat_to_nat_byte_list_be_le nat_to_nat_byte_list_le_len_bound_lower)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma nat_to_nat_byte_list_be_len_bound_upper:
  assumes \<open>n < 256^k\<close>
    shows \<open>length (nat_to_nat_byte_list_be n min_len) \<le> max k min_len\<close>
using assms by (simp add: nat_to_nat_byte_list_be_le nat_to_nat_byte_list_le_len_bound_upper)

lemma nat_to_nat_byte_list_be_len:
  assumes \<open>n < 2^(8*k)\<close>
    shows \<open>length (nat_to_nat_byte_list_be n k) = k\<close>
using assms by (simp add: nat_to_nat_byte_list_be_le nat_to_nat_byte_list_le_len)

text\<open>The following is a tail-recursive variant of the big endian encoding that is more suitable
for code extraction:\<close>
fun nat_to_nat_byte_list_be_core' :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list\<close> where
  \<open>nat_to_nat_byte_list_be_core' n min_len acc = (
      if n = 0 then
         replicate min_len 0 @ acc
      else
        let b  = n mod 256 in
        let n' = n div 256 in
           nat_to_nat_byte_list_be_core' n' (min_len - 1) (b # acc))\<close>
declare nat_to_nat_byte_list_be_core'.simps[simp del]

definition nat_to_nat_byte_list_be' :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list\<close> where
  \<open>nat_to_nat_byte_list_be' n min_len \<equiv> nat_to_nat_byte_list_be_core' n min_len []\<close>

lemma nat_to_nat_byte_list_be_alt:
  shows \<open>nat_to_nat_byte_list_be_core' n min_len acc = nat_to_nat_byte_list_be n min_len @ acc\<close>
by (induction n arbitrary: acc min_len rule: Nat.nat_less_induct)
  (case_tac \<open>n = 0\<close>; simp add: nat_to_nat_byte_list_be_core'.simps nat_to_nat_byte_list_be_cases Let_def)

corollary [code]: \<open>nat_to_nat_byte_list_be n min_len = nat_to_nat_byte_list_be_core' n min_len []\<close>
  by (simp add: nat_to_nat_byte_list_be_alt)

text\<open>The little/big endian encodings above are valued in \<^typ>\<open>nat list\<close>. Since all values are
\<^verbatim>\<open>< BYTE_LIMIT\<close>, we lose no information by casting to \<^typ>\<open>byte list\<close>:\<close>

definition nat_to_byte_list_be :: \<open>nat \<Rightarrow> nat \<Rightarrow> byte list\<close> where
  \<open>nat_to_byte_list_be n min_len \<equiv> List.map word_of_nat (nat_to_nat_byte_list_be n min_len)\<close>

definition nat_to_byte_list_le :: \<open>nat \<Rightarrow> nat \<Rightarrow> byte list\<close> where
  \<open>nat_to_byte_list_le n min_len \<equiv> List.map word_of_nat (nat_to_nat_byte_list_le n min_len)\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma nat_to_byte_list_le_be:
  shows [byte_encoding_le_be]: \<open>nat_to_byte_list_le n min_len = rev (nat_to_byte_list_be n min_len)\<close>
by (simp add: nat_to_byte_list_le_def nat_to_byte_list_be_def nat_to_nat_byte_list_le_be rev_map)

lemma nat_to_byte_list_be_le:
  shows [byte_encoding_be_le]: \<open>nat_to_byte_list_be n min_len = rev (nat_to_byte_list_le n min_len)\<close>
by (simp add: nat_to_byte_list_le_def nat_to_byte_list_be_def nat_to_nat_byte_list_be_le rev_map)

text\<open>Again, the following recursive description is sometimes convenient for inductive reasoning:\<close>
lemma nat_to_byte_list_le_cases_alt:
  shows \<open>nat_to_byte_list_le 0 0 = []\<close>
    and \<open>n \<noteq> 0 \<Longrightarrow> nat_to_byte_list_le n 0
             = word_of_nat (n mod 256) # nat_to_byte_list_le (n div 256) 0\<close>
    and \<open>min_len \<noteq> 0 \<Longrightarrow> nat_to_byte_list_le n min_len
             = word_of_nat (n mod 256) # nat_to_byte_list_le (n div 256) (min_len - 1)\<close>
by (auto simp add: nat_to_byte_list_le_def nat_to_nat_byte_list_le_cases
  nat_to_nat_byte_list_le_cases_alt)

lemma unat_word_of_nat_mod256:
  shows \<open>unat (word_of_nat (n mod 256) :: 8 word) = (n :: nat) mod 256\<close>
proof -
  have \<open>n mod 256 < 256\<close>
    by simp
  moreover have \<open>\<And>m :: nat. m < 256 \<Longrightarrow> unat ((word_of_nat m) :: 8 word) = m\<close>
    by (subst le_unat_uoi[where z=255]; simp)
  ultimately show ?thesis
    by auto
qed

lemma add_byte_0s:
  shows \<open>(shift_insert_byte 0 ^^ n) 0 = 0\<close>
by (induction n; simp add: shift_insert_byte_def)

subsection\<open>Properties of little/big endian encoding and decoding\<close>

text\<open>The big endian encoding inverts the big endian interpretation:\<close>
lemma nat_to_byte_list_be_correct:
  shows \<open>byte_list_to_nat_be (nat_to_byte_list_be n min_len) = n\<close>
by (induction n arbitrary: min_len rule: Nat.nat_less_induct; case_tac \<open>n = 0\<close>;
  simp add: byte_list_to_nat_be_def nat_to_byte_list_be_def nat_to_nat_byte_list_be_cases
  shift_insert_byte_def unat_word_of_nat_mod256 BYTE_LIMIT_def add_byte_0s)

text\<open>The little endian encoding inverts the little endian interpretation:\<close>
lemma nat_to_byte_list_le_correct:
  shows \<open>byte_list_to_nat_le (nat_to_byte_list_le n min_len) = n\<close>
by (simp add: byte_encoding_le_be rev_map nat_to_byte_list_be_correct)

text\<open>The little endian interpretation inverts the little endian encoding:\<close>
lemma byte_list_to_nat_le_correct:
  shows \<open>nat_to_byte_list_le (byte_list_to_nat_le bs) (length bs) = bs\<close>
by (induction bs; simp add: byte_list_to_nat_le_cases nat_to_byte_list_le_cases_alt
  shift_insert_byte_correct)

lemma byte_list_to_nat_le_correctI:
  assumes \<open>l = length bs\<close>
    shows \<open>nat_to_byte_list_le (byte_list_to_nat_le bs) l = bs\<close>
using assms by (simp add: byte_list_to_nat_le_correct)

text\<open>The big endian interpretation inverts the big endian encoding:\<close>
lemma byte_list_to_nat_be_correct:
  shows \<open>nat_to_byte_list_be (byte_list_to_nat_be bs) (length bs) = bs\<close>
using byte_list_to_nat_le_correct[where bs=\<open>rev bs\<close>] by (simp add: byte_encoding_be_le)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma byte_list_to_nat_be_correctI:
  assumes \<open>l = length bs\<close>
    shows \<open>nat_to_byte_list_be (byte_list_to_nat_be bs) l = bs\<close>
using assms by (simp add: byte_list_to_nat_be_correct)

subsection\<open>Little/Big endian encoding/decoding for words\<close>

text\<open>In this section, we specialize the little/big endian encodingd/decoding to the common
cases of 16/32/64-bit words. In this case, encoding/decoding are bijections between 16/32/64-bit
words and length-2/4/8 lists of bytes.

We focus on the little endian case first.\<close>

corollary nat_to_nat_byte_list_le_len_cases:
  shows \<open>\<And>n. n < 2^64 \<Longrightarrow> length (nat_to_nat_byte_list_le n 8) = 8\<close>
    and \<open>\<And>n. n < 2^32 \<Longrightarrow> length (nat_to_nat_byte_list_le n 4) = 4\<close>
    and \<open>\<And>n. n < 2^16 \<Longrightarrow> length (nat_to_nat_byte_list_le n 2) = 2\<close>
by (auto simp add: nat_to_nat_byte_list_le_len)

definition word64_to_byte_list_le :: \<open>64 word \<Rightarrow> byte list\<close> where
  \<open>word64_to_byte_list_le n \<equiv> nat_to_byte_list_le (unat n) 8\<close>

definition word64_from_byte_list_le :: \<open>byte list \<Rightarrow> 64 word\<close> where
  \<open>word64_from_byte_list_le bs \<equiv> word_of_nat (byte_list_to_nat_le bs)\<close>

definition word32_to_byte_list_le :: \<open>32 word \<Rightarrow> byte list\<close> where
  \<open>word32_to_byte_list_le n \<equiv> nat_to_byte_list_le (unat n) 4\<close>

definition word32_from_byte_list_le :: \<open>byte list \<Rightarrow> 32 word\<close> where
  \<open>word32_from_byte_list_le bs \<equiv> word_of_nat (byte_list_to_nat_le bs)\<close>

definition word16_to_byte_list_le :: \<open>16 word \<Rightarrow> byte list\<close> where
  \<open>word16_to_byte_list_le n \<equiv> nat_to_byte_list_le (unat n) 2\<close>

definition word16_from_byte_list_le :: \<open>byte list \<Rightarrow> 16 word\<close> where
  \<open>word16_from_byte_list_le bs \<equiv> word_of_nat (byte_list_to_nat_le bs)\<close>

lemma word_from_byte_list_le_unat:
  shows \<open>length bs = 8 \<Longrightarrow> unat (word_of_nat (byte_list_to_nat_le bs)::64 word) = byte_list_to_nat_le bs\<close>
    and \<open>length bs = 4 \<Longrightarrow> unat (word_of_nat (byte_list_to_nat_le bs)::32 word) = byte_list_to_nat_le bs\<close>
    and \<open>length bs = 2 \<Longrightarrow> unat (word_of_nat (byte_list_to_nat_le bs)::16 word) = byte_list_to_nat_le bs\<close>
proof -
  assume \<open>length bs = 8\<close>
  then show \<open>unat (word_of_nat (byte_list_to_nat_le bs) :: 64 word) = byte_list_to_nat_le bs\<close>
    using byte_list_to_nat_le_bound[where bs=bs] by (simp add: unat_of_nat)
next
  assume \<open>length bs = 4\<close>
  then show \<open>unat (word_of_nat (byte_list_to_nat_le bs) :: 32 word) = byte_list_to_nat_le bs\<close>
    using byte_list_to_nat_le_bound[where bs=bs] by (simp add: unat_of_nat)
next
  assume \<open>length bs = 2\<close>
  then show \<open>unat (word_of_nat (byte_list_to_nat_le bs) :: 16 word) = byte_list_to_nat_le bs\<close>
    using byte_list_to_nat_le_bound[where bs=bs] by (simp add: unat_of_nat)
qed

lemma word_byte_list_le_bij:
  shows \<open>word64_from_byte_list_le (word64_to_byte_list_le n64) = n64\<close> (is ?g1)
    and \<open>word32_from_byte_list_le (word32_to_byte_list_le n32) = n32\<close> (is ?g2)
    and \<open>word16_from_byte_list_le (word16_to_byte_list_le n16) = n16\<close> (is ?g3)
    and \<open>length (word64_to_byte_list_le n64) = 8\<close> (is ?g4)
    and \<open>length (word32_to_byte_list_le n32) = 4\<close> (is ?g5)
    and \<open>length (word16_to_byte_list_le n16) = 2\<close> (is ?g6)
    and \<open>length bs = 8 \<Longrightarrow> word64_to_byte_list_le (word64_from_byte_list_le bs) = bs\<close>
    and \<open>length bs = 4 \<Longrightarrow> word32_to_byte_list_le (word32_from_byte_list_le bs) = bs\<close>
    and \<open>length bs = 2 \<Longrightarrow> word16_to_byte_list_le (word16_from_byte_list_le bs) = bs\<close>
proof -
  show \<open>?g1\<close> \<open>?g2\<close> \<open>?g3\<close>
    by (auto simp add: nat_to_byte_list_le_correct word64_from_byte_list_le_def
      word32_from_byte_list_le_def word16_from_byte_list_le_def word64_to_byte_list_le_def
      word32_to_byte_list_le_def word16_to_byte_list_le_def)
next
  show \<open>?g4\<close> \<open>?g5\<close> \<open>?g6\<close>
    by (auto simp add: word64_to_byte_list_le_def word32_to_byte_list_le_def
       word16_to_byte_list_le_def nat_to_byte_list_le_def unsigned_less[where 'b=64, simplified]
       unsigned_less[where 'b=32, simplified] unsigned_less[where 'b=16, simplified]
       intro!: nat_to_nat_byte_list_le_len_cases)
next
  assume \<open>length bs = 8\<close> then show \<open>word64_to_byte_list_le (word64_from_byte_list_le bs) = bs\<close>
    by (clarsimp simp add: word64_from_byte_list_le_def word64_to_byte_list_le_def
      word_from_byte_list_le_unat intro!: byte_list_to_nat_le_correctI)
next
  assume \<open>length bs = 4\<close> then show \<open>word32_to_byte_list_le (word32_from_byte_list_le bs) = bs\<close>
    by (clarsimp simp add: word32_from_byte_list_le_def word32_to_byte_list_le_def
      word_from_byte_list_le_unat intro!: byte_list_to_nat_le_correctI)
next
  assume \<open>length bs = 2\<close> then show \<open>word16_to_byte_list_le (word16_from_byte_list_le bs) = bs\<close>
    by (clarsimp simp add: word16_from_byte_list_le_def word16_to_byte_list_le_def
      word_from_byte_list_le_unat intro!: byte_list_to_nat_le_correctI)
qed

text\<open>Next, the big endian case.\<close>

definition word64_to_byte_list_be :: \<open>64 word \<Rightarrow> byte list\<close> where
  \<open>word64_to_byte_list_be n \<equiv> nat_to_byte_list_be (unat n) 8\<close>

definition word64_from_byte_list_be :: \<open>byte list \<Rightarrow> 64 word\<close> where
  \<open>word64_from_byte_list_be bs \<equiv> word_of_nat (byte_list_to_nat_be bs)\<close>

definition word32_to_byte_list_be :: \<open>32 word \<Rightarrow> byte list\<close> where
  \<open>word32_to_byte_list_be n \<equiv> nat_to_byte_list_be (unat n) 4\<close>

definition word32_from_byte_list_be :: \<open>byte list \<Rightarrow> 32 word\<close> where
  \<open>word32_from_byte_list_be bs \<equiv> word_of_nat (byte_list_to_nat_be bs)\<close>

definition word16_to_byte_list_be :: \<open>16 word \<Rightarrow> byte list\<close> where
  \<open>word16_to_byte_list_be n \<equiv> nat_to_byte_list_be (unat n) 2\<close>

definition word16_from_byte_list_be :: \<open>byte list \<Rightarrow> 16 word\<close> where
  \<open>word16_from_byte_list_be bs \<equiv> word_of_nat (byte_list_to_nat_be bs)\<close>

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word64_to_byte_list_be_le:
  shows [byte_encoding_be_le]: \<open>word64_to_byte_list_be n = rev (word64_to_byte_list_le n)\<close>
by (simp add: nat_to_byte_list_be_le word64_to_byte_list_be_def word64_to_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word64_to_byte_list_le_be:
  shows [byte_encoding_le_be]: \<open>word64_to_byte_list_le n = rev (word64_to_byte_list_be n)\<close>
by (simp add: nat_to_byte_list_be_le word64_to_byte_list_be_def word64_to_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word32_to_byte_list_be_le:
  shows [byte_encoding_be_le]: \<open>word32_to_byte_list_be n = rev (word32_to_byte_list_le n)\<close>
by (simp add: nat_to_byte_list_be_le word32_to_byte_list_be_def word32_to_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word32_to_byte_list_le_be:
  shows [byte_encoding_le_be]: \<open>word32_to_byte_list_le n = rev (word32_to_byte_list_be n)\<close>
by (simp add: nat_to_byte_list_be_le word32_to_byte_list_be_def word32_to_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word16_to_byte_list_be_le:
  shows [byte_encoding_be_le]: \<open>word16_to_byte_list_be n = rev (word16_to_byte_list_le n)\<close>
by (simp add: nat_to_byte_list_be_le word16_to_byte_list_be_def word16_to_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word16_to_byte_list_le_be:
  shows [byte_encoding_le_be]: \<open>word16_to_byte_list_le n = rev (word16_to_byte_list_be n)\<close>
by (simp add: nat_to_byte_list_be_le word16_to_byte_list_be_def word16_to_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word64_from_byte_list_be_le:
  shows [byte_encoding_be_le]: \<open>word64_from_byte_list_be bs = word64_from_byte_list_le (rev bs)\<close>
by (simp add: byte_list_to_nat_le_be word64_from_byte_list_be_def word64_from_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word64_from_byte_list_le_be:
  shows [byte_encoding_le_be]: \<open>word64_from_byte_list_le bs = word64_from_byte_list_be (rev bs)\<close>
by (simp add: byte_list_to_nat_le_be word64_from_byte_list_be_def word64_from_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word32_from_byte_list_be_le:
  shows [byte_encoding_be_le]: \<open>word32_from_byte_list_be bs = word32_from_byte_list_le (rev bs)\<close>
by (simp add: byte_list_to_nat_le_be word32_from_byte_list_be_def word32_from_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word32_from_byte_list_le_be:
  shows [byte_encoding_le_be]: \<open>word32_from_byte_list_le bs = word32_from_byte_list_be (rev bs)\<close>
by (simp add: byte_list_to_nat_le_be word32_from_byte_list_be_def word32_from_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word16_from_byte_list_be_le:
  shows [byte_encoding_be_le]: \<open>word16_from_byte_list_be bs = word16_from_byte_list_le (rev bs)\<close>
by (simp add: byte_list_to_nat_le_be word16_from_byte_list_be_def word16_from_byte_list_le_def)

\<comment>\<open>NOTE: This lemma is not used at present, but seems worth keeping.\<close>
lemma word16_from_byte_list_le_be:
  shows [byte_encoding_le_be]: \<open>word16_from_byte_list_le bs = word16_from_byte_list_be (rev bs)\<close>
by (simp add: byte_list_to_nat_le_be word16_from_byte_list_be_def word16_from_byte_list_le_def)

lemma word_byte_list_be_bij:
  shows \<open>word64_from_byte_list_be (word64_to_byte_list_be n64) = n64\<close> (is ?g1)
    and \<open>word32_from_byte_list_be (word32_to_byte_list_be n32) = n32\<close> (is ?g2)
    and \<open>word16_from_byte_list_be (word16_to_byte_list_be n16) = n16\<close> (is ?g3)
    and \<open>length (word64_to_byte_list_be n64) = 8\<close> (is ?g4)
    and \<open>length (word32_to_byte_list_be n32) = 4\<close> (is ?g5)
    and \<open>length (word16_to_byte_list_be n16) = 2\<close> (is ?g6)
    and \<open>length bs = 8 \<Longrightarrow> word64_to_byte_list_be (word64_from_byte_list_be bs) = bs\<close>
    and \<open>length bs = 4 \<Longrightarrow> word32_to_byte_list_be (word32_from_byte_list_be bs) = bs\<close>
    and \<open>length bs = 2 \<Longrightarrow> word16_to_byte_list_be (word16_from_byte_list_be bs) = bs\<close>
by (auto simp add: word_byte_list_le_bij byte_encoding_be_le)

text\<open>The above results can be recast as bijections between word types and arrays of bytes:\<close>

lift_definition word64_to_byte_array_le :: \<open>64 word \<Rightarrow> (byte, 8) array\<close> is
  \<open>brauns1 \<circ> word64_to_byte_list_le\<close>
by (clarsimp simp add: is_array_def) (metis brauns1_correct size_list word_byte_list_le_bij)

lift_definition word64_from_byte_array_le :: \<open>(byte, 8) array \<Rightarrow> 64 word\<close> is \<open>word64_from_byte_list_le \<circ> list_fast\<close> .

lift_definition word64_to_byte_array_be :: \<open>64 word \<Rightarrow> (byte, 8) array\<close> is
  \<open>brauns1 \<circ> word64_to_byte_list_be\<close>
by (clarsimp simp add: is_array_def) (metis brauns1_correct size_list word_byte_list_be_bij)

lift_definition word64_from_byte_array_be :: \<open>(byte, 8) array \<Rightarrow> 64 word\<close> is \<open>word64_from_byte_list_be \<circ> list_fast\<close> .

lift_definition word32_to_byte_array_le :: \<open>32 word \<Rightarrow> (byte, 4) array\<close> is
  \<open>brauns1 \<circ> word32_to_byte_list_le\<close>
by (clarsimp simp add: is_array_def) (metis brauns1_correct size_list word_byte_list_le_bij)

lift_definition word32_from_byte_array_le :: \<open>(byte, 4) array \<Rightarrow> 32 word\<close> is \<open>word32_from_byte_list_le \<circ> list_fast\<close> .

lift_definition word32_to_byte_array_be :: \<open>32 word \<Rightarrow> (byte, 4) array\<close> is
  \<open>brauns1 \<circ> word32_to_byte_list_be\<close>
by (clarsimp simp add: is_array_def) (metis brauns1_correct size_list word_byte_list_be_bij)

lift_definition word32_from_byte_array_be :: \<open>(byte, 4) array \<Rightarrow> 32 word\<close> is \<open>word32_from_byte_list_be \<circ> list_fast\<close> .

lift_definition word16_to_byte_array_le :: \<open>16 word \<Rightarrow> (byte, 2) array\<close> is
  \<open>brauns1 \<circ> word16_to_byte_list_le\<close>
by (clarsimp simp add: is_array_def) (metis brauns1_correct size_list word_byte_list_le_bij)

lift_definition word16_from_byte_array_le :: \<open>(byte, 2) array \<Rightarrow> 16 word\<close> is \<open>word16_from_byte_list_le \<circ> list_fast\<close> .

lift_definition word16_to_byte_array_be :: \<open>16 word \<Rightarrow> (byte, 2) array\<close> is
  \<open>brauns1 \<circ> word16_to_byte_list_be\<close>
by (clarsimp simp add: is_array_def) (metis brauns1_correct size_list word_byte_list_be_bij)

lift_definition word16_from_byte_array_be :: \<open>(byte, 2) array \<Rightarrow> 16 word\<close>  is \<open>word16_from_byte_list_be \<circ> list_fast\<close> .

lemma brauns1_list [simp]:
  assumes \<open>braun l\<close>
    shows \<open>brauns1 (braun_list l) = l\<close>
using assms
  apply (intro braun_tree_ext; simp add: brauns1_correct)
  apply (metis Suc_eq_plus1 brauns1_correct nth_list_lookup1 size_list)
  apply (metis brauns1_correct size_list)
  done

lemma word_byte_array_le_bij:
  shows \<open>word64_from_byte_array_le (word64_to_byte_array_le n64) = n64\<close>
    and \<open>word32_from_byte_array_le (word32_to_byte_array_le n32) = n32\<close>
    and \<open>word16_from_byte_array_le (word16_to_byte_array_le n16) = n16\<close>
    and \<open>word64_to_byte_array_le (word64_from_byte_array_le bs8) = bs8\<close>
    and \<open>word32_to_byte_array_le (word32_from_byte_array_le bs4) = bs4\<close>
    and \<open>word16_to_byte_array_le (word16_from_byte_array_le bs2) = bs2\<close>
by (transfer, auto simp add: word_byte_list_le_bij size_list list_fast_correct brauns1_correct
  is_array_def)+

lemma word_byte_array_be_bij:
  shows \<open>word64_from_byte_array_be (word64_to_byte_array_be n64) = n64\<close>
    and \<open>word32_from_byte_array_be (word32_to_byte_array_be n32) = n32\<close>
    and \<open>word16_from_byte_array_be (word16_to_byte_array_be n16) = n16\<close>
    and \<open>word64_to_byte_array_be (word64_from_byte_array_be bs8) = bs8\<close>
    and \<open>word32_to_byte_array_be (word32_from_byte_array_be bs4) = bs4\<close>
    and \<open>word16_to_byte_array_be (word16_from_byte_array_be bs2) = bs2\<close>
by (transfer, auto simp add: word_byte_list_be_bij size_list list_fast_correct brauns1_correct
  is_array_def)+

text\<open>Finally, we can package everything together as a prism from byte lists to words.\<close>

named_theorems word_byte_array_iso_prism_defs

definition word64_byte_array_iso_prism_be :: \<open>((byte, 8) array, 64 word) prism\<close> where
  [word_byte_array_iso_prism_defs]: \<open>word64_byte_array_iso_prism_be \<equiv>
    iso_prism word64_from_byte_array_be word64_to_byte_array_be\<close>

definition word32_byte_array_iso_prism_be :: \<open>((byte, 4) array, 32 word) prism\<close> where
  [word_byte_array_iso_prism_defs]: \<open>word32_byte_array_iso_prism_be \<equiv>
    iso_prism word32_from_byte_array_be word32_to_byte_array_be\<close>

definition word16_byte_array_iso_prism_be :: \<open>((byte, 2) array, 16 word) prism\<close> where
  [word_byte_array_iso_prism_defs]: \<open>word16_byte_array_iso_prism_be \<equiv>
    iso_prism word16_from_byte_array_be word16_to_byte_array_be\<close>

definition word64_byte_array_iso_prism_le :: \<open>((byte, 8) array, 64 word) prism\<close> where
  [word_byte_array_iso_prism_defs]: \<open>word64_byte_array_iso_prism_le \<equiv>
    iso_prism word64_from_byte_array_le word64_to_byte_array_le\<close>

definition word32_byte_array_iso_prism_le :: \<open>((byte, 4) array, 32 word) prism\<close> where
  [word_byte_array_iso_prism_defs]: \<open>word32_byte_array_iso_prism_le \<equiv>
    iso_prism word32_from_byte_array_le word32_to_byte_array_le\<close>

definition word16_byte_array_iso_prism_le :: \<open>((byte, 2) array, 16 word) prism\<close> where
  [word_byte_array_iso_prism_defs]: \<open>word16_byte_array_iso_prism_le \<equiv>
    iso_prism word16_from_byte_array_le word16_to_byte_array_le\<close>

lemma word_byte_array_iso_prism_validity:
  shows \<open>is_valid_prism word64_byte_array_iso_prism_be\<close>
    and \<open>is_valid_prism word32_byte_array_iso_prism_be\<close>
    and \<open>is_valid_prism word16_byte_array_iso_prism_be\<close>
    and \<open>is_valid_prism word64_byte_array_iso_prism_le\<close>
    and \<open>is_valid_prism word32_byte_array_iso_prism_le\<close>
    and \<open>is_valid_prism word16_byte_array_iso_prism_le\<close>
by (auto intro!: iso_prism_valid simp add: word_byte_array_iso_prism_defs word_byte_array_be_bij
  word_byte_array_le_bij)

named_theorems word_byte_array_prism_defs

definition word64_byte_list_prism_be :: \<open>(byte list, 64 word) prism\<close> where
  [word_byte_array_prism_defs]: \<open>word64_byte_list_prism_be \<equiv>
    prism_compose list_fixlen_prism word64_byte_array_iso_prism_be\<close>

definition word32_byte_list_prism_be :: \<open>(byte list, 32 word) prism\<close> where
  [word_byte_array_prism_defs]: \<open>word32_byte_list_prism_be \<equiv>
    prism_compose list_fixlen_prism word32_byte_array_iso_prism_be\<close>

definition word16_byte_list_prism_be :: \<open>(byte list, 16 word) prism\<close> where
  [word_byte_array_prism_defs]: \<open>word16_byte_list_prism_be \<equiv>
    prism_compose list_fixlen_prism word16_byte_array_iso_prism_be\<close>

definition word64_byte_list_prism_le :: \<open>(byte list, 64 word) prism\<close> where
  [word_byte_array_prism_defs]: \<open>word64_byte_list_prism_le \<equiv>
    prism_compose list_fixlen_prism word64_byte_array_iso_prism_le\<close>

definition word32_byte_list_prism_le :: \<open>(byte list, 32 word) prism\<close> where
  [word_byte_array_prism_defs]: \<open>word32_byte_list_prism_le \<equiv>
    prism_compose list_fixlen_prism word32_byte_array_iso_prism_le\<close>

definition word16_byte_list_prism_le :: \<open>(byte list, 16 word) prism\<close> where
  [word_byte_array_prism_defs]: \<open>word16_byte_list_prism_le \<equiv>
    prism_compose list_fixlen_prism word16_byte_array_iso_prism_le\<close>

lemma word_byte_array_prism_validity:
  shows \<open>is_valid_prism word64_byte_list_prism_be\<close>
    and \<open>is_valid_prism word32_byte_list_prism_be\<close>
    and \<open>is_valid_prism word16_byte_list_prism_be\<close>
    and \<open>is_valid_prism word64_byte_list_prism_le\<close>
    and \<open>is_valid_prism word32_byte_list_prism_le\<close>
    and \<open>is_valid_prism word16_byte_list_prism_le\<close>
by (auto intro!: prism_compose_valid simp add: word_byte_array_prism_defs
  word_byte_array_iso_prism_validity list_fixlen_prism_valid)

context
  notes word_byte_array_prism_validity[simp]
    and word_byte_array_iso_prism_validity[simp]
    and prism_to_focus_raw_valid[simp]
    and prism_to_focus_raw_components[simp]
begin

lift_definition word64_byte_list_focus_be :: \<open>(byte list, 64 word) focus\<close> is
  \<open>prism_to_focus_raw word64_byte_list_prism_be\<close>
by simp

lift_definition word32_byte_list_focus_be :: \<open>(byte list, 32 word) focus\<close> is
  \<open>prism_to_focus_raw word32_byte_list_prism_be\<close>
by simp

lift_definition word16_byte_list_focus_be :: \<open>(byte list, 16 word) focus\<close> is
  \<open>prism_to_focus_raw word16_byte_list_prism_be\<close>
by simp

lift_definition word64_byte_list_focus_le :: \<open>(byte list, 64 word) focus\<close> is
  \<open>prism_to_focus_raw word64_byte_list_prism_le\<close>
by simp

lift_definition word32_byte_list_focus_le :: \<open>(byte list, 32 word) focus\<close> is
  \<open>prism_to_focus_raw word32_byte_list_prism_le\<close>
by simp

lift_definition word16_byte_list_focus_le :: \<open>(byte list, 16 word) focus\<close> is
  \<open>prism_to_focus_raw word16_byte_list_prism_le\<close>
by simp

lemmas word_byte_list_foci_defs =
  word64_byte_list_focus_be_def word32_byte_list_focus_be_def word16_byte_list_focus_be_def
  word64_byte_list_focus_le_def word32_byte_list_focus_le_def  word16_byte_list_focus_le_def

lift_definition word64_byte_array_focus_be :: \<open>((byte, 8) array, 64 word) focus\<close> is
  \<open>prism_to_focus_raw word64_byte_array_iso_prism_be\<close>
by simp

lift_definition word32_byte_array_focus_be :: \<open>((byte, 4) array, 32 word) focus\<close> is
  \<open>prism_to_focus_raw word32_byte_array_iso_prism_be\<close>
by simp

lift_definition word16_byte_array_focus_be :: \<open>((byte, 2) array, 16 word) focus\<close> is
  \<open>prism_to_focus_raw word16_byte_array_iso_prism_be\<close>
by simp

lift_definition word64_byte_array_focus_le :: \<open>((byte, 8) array, 64 word) focus\<close> is
  \<open>prism_to_focus_raw word64_byte_array_iso_prism_le\<close>
by simp

lift_definition word32_byte_array_focus_le :: \<open>((byte, 4) array, 32 word) focus\<close> is
  \<open>prism_to_focus_raw word32_byte_array_iso_prism_le\<close>
by simp

lift_definition word16_byte_array_focus_le :: \<open>((byte, 2) array, 16 word) focus\<close> is
  \<open>prism_to_focus_raw word16_byte_array_iso_prism_le\<close>
by simp

lemmas word_byte_array_foci_defs =
  word64_byte_array_focus_be_def word32_byte_array_focus_be_def word16_byte_array_focus_be_def
  word64_byte_array_focus_le_def word32_byte_array_focus_le_def  word16_byte_array_focus_le_def
end

lemmas word_byte_list_focus_components =
  word_byte_array_prism_validity[THEN prism_to_focus_components(1), folded word_byte_list_foci_defs]
  word_byte_array_prism_validity[THEN prism_to_focus_components(2), folded word_byte_list_foci_defs]
  word_byte_array_prism_validity[THEN prism_to_focus_components(3), folded word_byte_list_foci_defs]

lemmas word_byte_array_focus_components =
  word_byte_array_prism_validity[THEN prism_to_focus_components(1), folded word_byte_array_foci_defs]
  word_byte_array_prism_validity[THEN prism_to_focus_components(2), folded word_byte_array_foci_defs]
  word_byte_array_prism_validity[THEN prism_to_focus_components(3), folded word_byte_array_foci_defs]

(*<*)
end
(*>*)
