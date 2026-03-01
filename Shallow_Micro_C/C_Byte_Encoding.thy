theory C_Byte_Encoding
  imports
    C_Sizeof
    "Byte_Level_Encoding.Byte_Encoding_Word_Nat"
    "Lenses_And_Other_Optics.Prism"
begin

section \<open>Signed/Unsigned ISO Prism\<close>

text \<open>
  @{type sword} is a type copy of @{type word} via typedef. @{const scast} and @{const ucast}
  convert between same-width @{type word} and @{type sword} and satisfy inverse laws.
  We package this as an iso prism.
\<close>

definition word_sword_iso_prism :: \<open>('l::len word, 'l sword) prism\<close> where
  \<open>word_sword_iso_prism \<equiv> iso_prism scast scast\<close>

lemma word_sword_iso_prism_valid:
  shows \<open>is_valid_prism word_sword_iso_prism\<close>
  by (auto intro!: iso_prism_valid simp: word_sword_iso_prism_def)

section \<open>Single-Element Array ISO Prism\<close>

text \<open>
  For @{type c_char} (= @{type byte} = @{typ \<open>8 word\<close>}), we need a prism from byte lists
  to a single byte. We build this by composing @{const list_fixlen_prism} (which accepts
  exactly LENGTH('l)-element lists) with an iso between @{typ \<open>('a, 1) array\<close>} and @{typ 'a}.
\<close>

definition array_single_to :: \<open>('a, 1) array \<Rightarrow> 'a\<close> where
  \<open>array_single_to a \<equiv> array_nth a 0\<close>

definition array_single_from :: \<open>'a \<Rightarrow> ('a, 1) array\<close> where
  \<open>array_single_from x \<equiv> array_of_list [x]\<close>

lemma array_single_bij:
  shows \<open>array_single_to (array_single_from x) = x\<close>
    and \<open>array_single_from (array_single_to a) = a\<close>
  by (simp_all add: array_single_to_def array_single_from_def) (intro array_extI; simp)

definition array_single_iso_prism :: \<open>(('a, 1) array, 'a) prism\<close> where
  \<open>array_single_iso_prism \<equiv> iso_prism array_single_to array_single_from\<close>

lemma array_single_iso_prism_valid:
  shows \<open>is_valid_prism array_single_iso_prism\<close>
  by (auto intro!: iso_prism_valid simp: array_single_iso_prism_def array_single_bij)

section \<open>Per-C-Type Byte Encoding Prisms\<close>

text \<open>
  We define a validated @{typ \<open>(byte list, 'v) prism\<close>} for every C numeric type.
  Unsigned types reuse the existing @{const word16_byte_list_prism_le} etc.
  Signed types compose the unsigned prism with @{const word_sword_iso_prism}.
  The char type composes @{const list_fixlen_prism} with @{const array_single_iso_prism}.
\<close>

datatype c_endianness = C_LE | C_BE

definition c_endianness_of_bool :: \<open>bool \<Rightarrow> c_endianness\<close> where
  \<open>c_endianness_of_bool b \<equiv> (if b then C_BE else C_LE)\<close>

subsection \<open>Char (8-bit)\<close>

definition c_char_byte_prism :: \<open>(byte list, c_char) prism\<close> where
  \<open>c_char_byte_prism \<equiv> prism_compose list_fixlen_prism array_single_iso_prism\<close>

definition c_schar_byte_prism :: \<open>(byte list, c_schar) prism\<close> where
  \<open>c_schar_byte_prism \<equiv> prism_compose c_char_byte_prism word_sword_iso_prism\<close>

subsection \<open>Short (16-bit)\<close>

definition c_ushort_byte_prism :: \<open>(byte list, c_ushort) prism\<close> where
  \<open>c_ushort_byte_prism \<equiv> word16_byte_list_prism_le\<close>

definition c_ushort_byte_prism_be :: \<open>(byte list, c_ushort) prism\<close> where
  \<open>c_ushort_byte_prism_be \<equiv> word16_byte_list_prism_be\<close>

definition c_short_byte_prism :: \<open>(byte list, c_short) prism\<close> where
  \<open>c_short_byte_prism \<equiv> prism_compose word16_byte_list_prism_le word_sword_iso_prism\<close>

definition c_short_byte_prism_be :: \<open>(byte list, c_short) prism\<close> where
  \<open>c_short_byte_prism_be \<equiv> prism_compose word16_byte_list_prism_be word_sword_iso_prism\<close>

subsection \<open>Int (32-bit)\<close>

definition c_uint_byte_prism :: \<open>(byte list, c_uint) prism\<close> where
  \<open>c_uint_byte_prism \<equiv> word32_byte_list_prism_le\<close>

definition c_uint_byte_prism_be :: \<open>(byte list, c_uint) prism\<close> where
  \<open>c_uint_byte_prism_be \<equiv> word32_byte_list_prism_be\<close>

definition c_int_byte_prism :: \<open>(byte list, c_int) prism\<close> where
  \<open>c_int_byte_prism \<equiv> prism_compose word32_byte_list_prism_le word_sword_iso_prism\<close>

definition c_int_byte_prism_be :: \<open>(byte list, c_int) prism\<close> where
  \<open>c_int_byte_prism_be \<equiv> prism_compose word32_byte_list_prism_be word_sword_iso_prism\<close>

subsection \<open>Long (64-bit)\<close>

definition c_ulong_byte_prism :: \<open>(byte list, c_ulong) prism\<close> where
  \<open>c_ulong_byte_prism \<equiv> word64_byte_list_prism_le\<close>

definition c_ulong_byte_prism_be :: \<open>(byte list, c_ulong) prism\<close> where
  \<open>c_ulong_byte_prism_be \<equiv> word64_byte_list_prism_be\<close>

definition c_long_byte_prism :: \<open>(byte list, c_long) prism\<close> where
  \<open>c_long_byte_prism \<equiv> prism_compose word64_byte_list_prism_le word_sword_iso_prism\<close>

definition c_long_byte_prism_be :: \<open>(byte list, c_long) prism\<close> where
  \<open>c_long_byte_prism_be \<equiv> prism_compose word64_byte_list_prism_be word_sword_iso_prism\<close>

subsection \<open>128-bit\<close>

definition c_uint128_byte_prism :: \<open>(byte list, c_uint128) prism\<close> where
  \<open>c_uint128_byte_prism \<equiv> word128_byte_list_prism_le\<close>

definition c_uint128_byte_prism_be :: \<open>(byte list, c_uint128) prism\<close> where
  \<open>c_uint128_byte_prism_be \<equiv> word128_byte_list_prism_be\<close>

definition c_int128_byte_prism :: \<open>(byte list, c_int128) prism\<close> where
  \<open>c_int128_byte_prism \<equiv> prism_compose word128_byte_list_prism_le word_sword_iso_prism\<close>

definition c_int128_byte_prism_be :: \<open>(byte list, c_int128) prism\<close> where
  \<open>c_int128_byte_prism_be \<equiv> prism_compose word128_byte_list_prism_be word_sword_iso_prism\<close>

subsection \<open>Endianness Selectors\<close>

definition c_ushort_byte_prism_of :: \<open>c_endianness \<Rightarrow> (byte list, c_ushort) prism\<close> where
  \<open>c_ushort_byte_prism_of e \<equiv> (case e of C_LE \<Rightarrow> c_ushort_byte_prism | C_BE \<Rightarrow> c_ushort_byte_prism_be)\<close>

definition c_short_byte_prism_of :: \<open>c_endianness \<Rightarrow> (byte list, c_short) prism\<close> where
  \<open>c_short_byte_prism_of e \<equiv> (case e of C_LE \<Rightarrow> c_short_byte_prism | C_BE \<Rightarrow> c_short_byte_prism_be)\<close>

definition c_uint_byte_prism_of :: \<open>c_endianness \<Rightarrow> (byte list, c_uint) prism\<close> where
  \<open>c_uint_byte_prism_of e \<equiv> (case e of C_LE \<Rightarrow> c_uint_byte_prism | C_BE \<Rightarrow> c_uint_byte_prism_be)\<close>

definition c_int_byte_prism_of :: \<open>c_endianness \<Rightarrow> (byte list, c_int) prism\<close> where
  \<open>c_int_byte_prism_of e \<equiv> (case e of C_LE \<Rightarrow> c_int_byte_prism | C_BE \<Rightarrow> c_int_byte_prism_be)\<close>

definition c_ulong_byte_prism_of :: \<open>c_endianness \<Rightarrow> (byte list, c_ulong) prism\<close> where
  \<open>c_ulong_byte_prism_of e \<equiv> (case e of C_LE \<Rightarrow> c_ulong_byte_prism | C_BE \<Rightarrow> c_ulong_byte_prism_be)\<close>

definition c_long_byte_prism_of :: \<open>c_endianness \<Rightarrow> (byte list, c_long) prism\<close> where
  \<open>c_long_byte_prism_of e \<equiv> (case e of C_LE \<Rightarrow> c_long_byte_prism | C_BE \<Rightarrow> c_long_byte_prism_be)\<close>

definition c_uint128_byte_prism_of :: \<open>c_endianness \<Rightarrow> (byte list, c_uint128) prism\<close> where
  \<open>c_uint128_byte_prism_of e \<equiv> (case e of C_LE \<Rightarrow> c_uint128_byte_prism | C_BE \<Rightarrow> c_uint128_byte_prism_be)\<close>

definition c_int128_byte_prism_of :: \<open>c_endianness \<Rightarrow> (byte list, c_int128) prism\<close> where
  \<open>c_int128_byte_prism_of e \<equiv> (case e of C_LE \<Rightarrow> c_int128_byte_prism | C_BE \<Rightarrow> c_int128_byte_prism_be)\<close>


section \<open>Validity Proofs\<close>

named_theorems c_byte_prism_defs
declare c_char_byte_prism_def [c_byte_prism_defs]
    and c_schar_byte_prism_def [c_byte_prism_defs]
    and c_ushort_byte_prism_def [c_byte_prism_defs]
    and c_short_byte_prism_def [c_byte_prism_defs]
    and c_uint_byte_prism_def [c_byte_prism_defs]
    and c_uint_byte_prism_be_def [c_byte_prism_defs]
    and c_int_byte_prism_def [c_byte_prism_defs]
    and c_int_byte_prism_be_def [c_byte_prism_defs]
    and c_ulong_byte_prism_def [c_byte_prism_defs]
    and c_ulong_byte_prism_be_def [c_byte_prism_defs]
    and c_long_byte_prism_def [c_byte_prism_defs]
    and c_long_byte_prism_be_def [c_byte_prism_defs]
    and c_uint128_byte_prism_def [c_byte_prism_defs]
    and c_uint128_byte_prism_be_def [c_byte_prism_defs]
    and c_int128_byte_prism_def [c_byte_prism_defs]
    and c_int128_byte_prism_be_def [c_byte_prism_defs]
    and c_ushort_byte_prism_be_def [c_byte_prism_defs]
    and c_short_byte_prism_be_def [c_byte_prism_defs]

named_theorems c_byte_prism_validity

lemma c_byte_prism_valid [c_byte_prism_validity]:
  shows \<open>is_valid_prism c_char_byte_prism\<close>
    and \<open>is_valid_prism c_schar_byte_prism\<close>
    and \<open>is_valid_prism c_ushort_byte_prism\<close>
    and \<open>is_valid_prism c_short_byte_prism\<close>
    and \<open>is_valid_prism c_uint_byte_prism\<close>
    and \<open>is_valid_prism c_int_byte_prism\<close>
    and \<open>is_valid_prism c_ulong_byte_prism\<close>
    and \<open>is_valid_prism c_long_byte_prism\<close>
    and \<open>is_valid_prism c_uint128_byte_prism\<close>
    and \<open>is_valid_prism c_int128_byte_prism\<close>
  by (auto simp: c_byte_prism_defs
           intro!: prism_compose_valid list_fixlen_prism_valid
                   array_single_iso_prism_valid word_sword_iso_prism_valid
                   word_byte_array_prism_validity word128_byte_array_prism_validity)

lemma c_byte_prism_valid_be [c_byte_prism_validity]:
  shows \<open>is_valid_prism c_ushort_byte_prism_be\<close>
    and \<open>is_valid_prism c_short_byte_prism_be\<close>
    and \<open>is_valid_prism c_uint_byte_prism_be\<close>
    and \<open>is_valid_prism c_int_byte_prism_be\<close>
    and \<open>is_valid_prism c_ulong_byte_prism_be\<close>
    and \<open>is_valid_prism c_long_byte_prism_be\<close>
    and \<open>is_valid_prism c_uint128_byte_prism_be\<close>
    and \<open>is_valid_prism c_int128_byte_prism_be\<close>
  by (auto simp: c_byte_prism_defs
           intro!: prism_compose_valid
                   word_sword_iso_prism_valid
                   word_byte_array_prism_validity word128_byte_array_prism_validity)

section \<open>Embed Length Consistency (sizeof match)\<close>

lemma c_char_byte_embed_length:
  shows \<open>length (prism_embed c_char_byte_prism v) = 1\<close>
  by (simp add: c_char_byte_prism_def prism_compose_def list_fixlen_prism_def
                list_fixlen_embed_def array_single_iso_prism_def iso_prism_def
                array_single_from_def)

lemma c_ushort_byte_embed_length:
  shows \<open>length (prism_embed c_ushort_byte_prism v) = 2\<close>
  by (simp add: c_ushort_byte_prism_def word16_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word16_byte_array_iso_prism_le_def
                iso_prism_def)

lemma c_uint_byte_embed_length:
  shows \<open>length (prism_embed c_uint_byte_prism v) = 4\<close>
  by (simp add: c_uint_byte_prism_def word32_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word32_byte_array_iso_prism_le_def
                iso_prism_def)

lemma c_ulong_byte_embed_length:
  shows \<open>length (prism_embed c_ulong_byte_prism v) = 8\<close>
  by (simp add: c_ulong_byte_prism_def word64_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word64_byte_array_iso_prism_le_def
                iso_prism_def)

lemma c_schar_byte_embed_length:
  shows \<open>length (prism_embed c_schar_byte_prism v) = 1\<close>
  by (simp add: c_schar_byte_prism_def c_char_byte_prism_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def array_single_iso_prism_def
                iso_prism_def word_sword_iso_prism_def array_single_from_def)

lemma c_short_byte_embed_length:
  shows \<open>length (prism_embed c_short_byte_prism v) = 2\<close>
  by (simp add: c_short_byte_prism_def word16_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word16_byte_array_iso_prism_le_def
                iso_prism_def word_sword_iso_prism_def)

lemma c_int_byte_embed_length:
  shows \<open>length (prism_embed c_int_byte_prism v) = 4\<close>
  by (simp add: c_int_byte_prism_def word32_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word32_byte_array_iso_prism_le_def
                iso_prism_def word_sword_iso_prism_def)

lemma c_long_byte_embed_length:
  shows \<open>length (prism_embed c_long_byte_prism v) = 8\<close>
  by (simp add: c_long_byte_prism_def word64_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word64_byte_array_iso_prism_le_def
                iso_prism_def word_sword_iso_prism_def)

lemma c_uint128_byte_embed_length:
  shows \<open>length (prism_embed c_uint128_byte_prism v) = 16\<close>
  by (simp add: c_uint128_byte_prism_def word128_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word128_byte_array_iso_prism_le_def
                iso_prism_def)

lemma c_int128_byte_embed_length:
  shows \<open>length (prism_embed c_int128_byte_prism v) = 16\<close>
  by (simp add: c_int128_byte_prism_def word128_byte_list_prism_le_def prism_compose_def
                list_fixlen_prism_def list_fixlen_embed_def word128_byte_array_iso_prism_le_def
                iso_prism_def word_sword_iso_prism_def)

section \<open>Sizeof Consistency\<close>

lemma c_char_sizeof_encoding:
  shows \<open>c_sizeof TYPE(c_char) = length (prism_embed c_char_byte_prism v)\<close>
  by (simp add: c_char_byte_embed_length)

lemma c_uint_sizeof_encoding:
  shows \<open>c_sizeof TYPE(c_uint) = length (prism_embed c_uint_byte_prism v)\<close>
  by (simp add: c_uint_byte_embed_length)

lemma c_int_sizeof_encoding:
  shows \<open>c_sizeof TYPE(c_int) = length (prism_embed c_int_byte_prism v)\<close>
  by (simp add: c_int_byte_embed_length)

lemma c_ulong_sizeof_encoding:
  shows \<open>c_sizeof TYPE(c_ulong) = length (prism_embed c_ulong_byte_prism v)\<close>
  by (simp add: c_ulong_byte_embed_length)

lemma c_uint128_sizeof_encoding:
  shows \<open>c_sizeof TYPE(c_uint128) = length (prism_embed c_uint128_byte_prism v)\<close>
  by (simp add: c_uint128_byte_embed_length)

lemma c_int128_sizeof_encoding:
  shows \<open>c_sizeof TYPE(c_int128) = length (prism_embed c_int128_byte_prism v)\<close>
  by (simp add: c_int128_byte_embed_length)

end
