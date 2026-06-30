(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Byte_Encoding_Enum
  imports Byte_Encoding_Bool "Enum_Theory.Enum_Theory"
  keywords "define_byte_enum" :: thy_decl
begin
(*>*)

section\<open>Byte encoding for enumerations\<close>

text\<open>An enumeration is encoded as a single \<^emph>\<open>discriminant\<close> byte.  Like the
boolean encoding — of which this is the generalisation — decoding is
\<^emph>\<open>partial\<close>: only the bytes that name a constructor are valid, every other byte
projects to \<^term>\<open>None\<close>.

Unlike the fixed word encodings, an enumeration has no canonical numeric layout:
each concrete enum chooses its own discriminant assignment.  The encoding is
therefore a \<^emph>\<open>combinator\<close> parameterised by a discriminant encoding
\<^term>\<open>to_byte\<close> / \<^term>\<open>from_byte\<close>; a concrete enum becomes an instance by
supplying the two functions and discharging the two round-trip facts (a legal
discriminant decodes back to its constructor; an illegal one decodes to
\<^term>\<open>None\<close>).\<close>

subsection\<open>The enum byte-prism combinator\<close>

definition enum_byte_prism :: \<open>('e \<Rightarrow> byte) \<Rightarrow> (byte \<Rightarrow> 'e option) \<Rightarrow> (byte, 'e) prism\<close> where
  \<open>enum_byte_prism to_byte from_byte \<equiv> make_prism to_byte from_byte\<close>

text\<open>Validity is the enum round-trip law: it follows from the two facts that a
concrete enum's discriminant encoding must satisfy.\<close>

lemma enum_byte_prism_valid:
  assumes \<open>\<And>e. from_byte (to_byte e) = Some e\<close>
      and \<open>\<And>w e. from_byte w = Some e \<Longrightarrow> to_byte e = w\<close>
    shows \<open>is_valid_prism (enum_byte_prism to_byte from_byte)\<close>
using assms by (auto simp add: is_valid_prism_def enum_byte_prism_def)

text\<open>A concrete enum becomes an instance by supplying \<^term>\<open>to_byte\<close> /
\<^term>\<open>from_byte\<close> and discharging the two round-trip facts;
\<^verbatim>\<open>enum_byte_prism_valid\<close> then yields validity unconditionally, and the prism
lifts to a focus exactly as the boolean encoding does
(\<^const>\<open>bool_byte_focus\<close>).  The generic combinator itself stops at the
conditional validity law, since the lift to a focus requires the discriminant
encoding to be fixed; the \<^verbatim>\<open>define_byte_enum\<close> command below automates the
per-instance boilerplate.\<close>

subsection\<open>The \<^verbatim>\<open>define_byte_enum\<close> command\<close>

text\<open>The \<^verbatim>\<open>define_byte_enum\<close> command automates the instance boilerplate.  Given
a name and a discriminant assignment

\<^verbatim>\<open>define_byte_enum <T> = <C0>: <d0> | <C1>: <d1> | ...\<close>

it defines the enumeration type (via the \<^verbatim>\<open>enum\<close> command), generates the
discriminant encoding \<^verbatim>\<open><T>_to_byte\<close> / \<^verbatim>\<open><T>_from_byte\<close>, defines
\<^verbatim>\<open><T>_byte_prism\<close> as an instance of \<^const>\<open>enum_byte_prism\<close>, and proves the
round-trip law \<^verbatim>\<open><T>_byte_prism_valid\<close> automatically.\<close>

ML_file \<open>byte_encoding_enum_cmd.ML\<close>

subsection\<open>Worked example\<close>

text\<open>A three-constructor enumeration, defined in one line by the command, with the
type, discriminant encoding, prism, and round-trip proof all generated
automatically.\<close>

define_byte_enum demo_enum =
    DE_First: 0 | DE_Second: 1 | DE_Third: 2

text\<open>The command generated the type and all four artifacts.  We check them:\<close>

\<comment>\<open>The type and its constructors exist.\<close>
term \<open>DE_First\<close> term \<open>DE_Second\<close> term \<open>DE_Third\<close>

\<comment>\<open>The encoding functions and prism exist, with the expected types.\<close>
term \<open>demo_enum_to_byte :: demo_enum \<Rightarrow> byte\<close>
term \<open>demo_enum_from_byte :: byte \<Rightarrow> demo_enum option\<close>
term \<open>demo_enum_byte_prism :: (byte, demo_enum) prism\<close>

\<comment>\<open>The round-trip law was proven automatically.\<close>
lemma \<open>is_valid_prism demo_enum_byte_prism\<close>
  by (rule demo_enum_byte_prism_valid)

\<comment>\<open>The generated encoding maps the discriminants as specified.\<close>
lemma \<open>demo_enum_to_byte DE_First = 0\<close>
  and \<open>demo_enum_to_byte DE_Second = 1\<close>
  and \<open>demo_enum_to_byte DE_Third = 2\<close>
  by (simp_all add: demo_enum_to_byte_def)

\<comment>\<open>Decoding inverts encoding, and an illegal discriminant fails.\<close>
lemma \<open>demo_enum_from_byte 1 = Some DE_Second\<close>
  and \<open>demo_enum_from_byte 7 = None\<close>
  by (simp_all add: demo_enum_from_byte_def)

(*<*)
end
(*>*)
