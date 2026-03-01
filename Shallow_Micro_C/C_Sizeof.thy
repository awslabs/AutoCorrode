theory C_Sizeof
  imports
    C_Numeric_Types
    "Byte_Level_Encoding.Byte_Encoding_Word_Nat"
begin

section \<open>C sizeof Reasoning\<close>

text \<open>
  We define @{text "c_sizeof"} as an overloaded constant mapping C types
  to their byte sizes, mirroring the C @{text "sizeof"} operator. This is
  connected to the byte-level encoding: the sizeof a type equals the
  number of bytes in its encoding.
\<close>

consts c_sizeof :: \<open>'a itself \<Rightarrow> nat\<close>

overloading
  c_sizeof_char \<equiv> \<open>c_sizeof :: c_char itself \<Rightarrow> nat\<close>
begin
  definition c_sizeof_char :: \<open>c_char itself \<Rightarrow> nat\<close> where
    \<open>c_sizeof_char _ \<equiv> 1\<close>
end

overloading
  c_sizeof_short \<equiv> \<open>c_sizeof :: c_short itself \<Rightarrow> nat\<close>
begin
  definition c_sizeof_short :: \<open>c_short itself \<Rightarrow> nat\<close> where
    \<open>c_sizeof_short _ \<equiv> 2\<close>
end

overloading
  c_sizeof_ushort \<equiv> \<open>c_sizeof :: c_ushort itself \<Rightarrow> nat\<close>
begin
  definition c_sizeof_ushort :: \<open>c_ushort itself \<Rightarrow> nat\<close> where
    \<open>c_sizeof_ushort _ \<equiv> 2\<close>
end

overloading
  c_sizeof_int \<equiv> \<open>c_sizeof :: c_int itself \<Rightarrow> nat\<close>
begin
  definition c_sizeof_int :: \<open>c_int itself \<Rightarrow> nat\<close> where
    \<open>c_sizeof_int _ \<equiv> 4\<close>
end

overloading
  c_sizeof_uint \<equiv> \<open>c_sizeof :: c_uint itself \<Rightarrow> nat\<close>
begin
  definition c_sizeof_uint :: \<open>c_uint itself \<Rightarrow> nat\<close> where
    \<open>c_sizeof_uint _ \<equiv> 4\<close>
end

overloading
  c_sizeof_long \<equiv> \<open>c_sizeof :: c_long itself \<Rightarrow> nat\<close>
begin
  definition c_sizeof_long :: \<open>c_long itself \<Rightarrow> nat\<close> where
    \<open>c_sizeof_long _ \<equiv> 8\<close>
end

overloading
  c_sizeof_ulong \<equiv> \<open>c_sizeof :: c_ulong itself \<Rightarrow> nat\<close>
begin
  definition c_sizeof_ulong :: \<open>c_ulong itself \<Rightarrow> nat\<close> where
    \<open>c_sizeof_ulong _ \<equiv> 8\<close>
end

overloading
  c_sizeof_int128 \<equiv> \<open>c_sizeof :: c_int128 itself \<Rightarrow> nat\<close>
begin
  definition c_sizeof_int128 :: \<open>c_int128 itself \<Rightarrow> nat\<close> where
    \<open>c_sizeof_int128 _ \<equiv> 16\<close>
end

overloading
  c_sizeof_uint128 \<equiv> \<open>c_sizeof :: c_uint128 itself \<Rightarrow> nat\<close>
begin
  definition c_sizeof_uint128 :: \<open>c_uint128 itself \<Rightarrow> nat\<close> where
    \<open>c_sizeof_uint128 _ \<equiv> 16\<close>
end

text \<open>Basic sizeof lemmas.\<close>

lemma c_sizeof_char_val [simp]:
  shows \<open>c_sizeof TYPE(c_char) = 1\<close>
by (simp add: c_sizeof_char_def)

lemma c_sizeof_short_val [simp]:
  shows \<open>c_sizeof TYPE(c_short) = 2\<close>
by (simp add: c_sizeof_short_def)

lemma c_sizeof_int_val [simp]:
  shows \<open>c_sizeof TYPE(c_int) = 4\<close>
by (simp add: c_sizeof_int_def)

lemma c_sizeof_uint_val [simp]:
  shows \<open>c_sizeof TYPE(c_uint) = 4\<close>
by (simp add: c_sizeof_uint_def)

lemma c_sizeof_long_val [simp]:
  shows \<open>c_sizeof TYPE(c_long) = 8\<close>
by (simp add: c_sizeof_long_def)

lemma c_sizeof_ulong_val [simp]: 
  shows \<open>c_sizeof TYPE(c_ulong) = 8\<close>
by (simp add: c_sizeof_ulong_def)

lemma c_sizeof_int128_val [simp]:
  shows \<open>c_sizeof TYPE(c_int128) = 16\<close>
by (simp add: c_sizeof_int128_def)

lemma c_sizeof_uint128_val [simp]:
  shows \<open>c_sizeof TYPE(c_uint128) = 16\<close>
by (simp add: c_sizeof_uint128_def)

text \<open>
  Connection to byte-level encoding: the sizeof value is consistent
  with the encoding length from @{theory Byte_Level_Encoding.Byte_Encoding_Word_Nat}.
\<close>

lemma c_sizeof_uint_encoding:
  shows \<open>c_sizeof TYPE(c_uint) = length (word32_to_byte_list_le n)\<close>
by (simp add: word_byte_list_le_bij)

lemma c_sizeof_ulong_encoding:
  shows \<open>c_sizeof TYPE(c_ulong) = length (word64_to_byte_list_le n)\<close>
by (simp add: word_byte_list_le_bij)

end
