(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Byte_Encoding_Record
  imports Byte_Parser Byte_Encoding_Enum
  keywords "define_byte_record" :: thy_decl
begin
(*>*)

section\<open>Byte-parser serialization for fixed-layout records\<close>

text\<open>A fixed-layout record lays its fields out contiguously: its byte encoding is
the concatenation of the field encodings, in order.  The \<^verbatim>\<open>define_byte_record\<close>
command automates the whole record: from a one-line field declaration it defines
the record type, builds a byte parser by sequencing the per-field parsers with
\<open>--\<^sub>\<integral>\<close> and relabelling the resulting nested tuple to the record via
\<^const>\<open>iso_focus\<close>, and derives the round-trip law.  Because a parser is a
validity-carrying focus, that round-trip law is obtained for free rather than
proved field by field.\<close>

subsection\<open>The \<^verbatim>\<open>define_byte_record\<close> command\<close>

text\<open>Given a name and a field assignment

\<^verbatim>\<open>define_byte_record <T> = <f0>: <ty0> | <f1>: <ty1> | ...\<close>

it defines the record type (via \<^verbatim>\<open>datatype_record\<close>), the record parser
\<^verbatim>\<open><T>_parser\<close>, the closed focus \<^verbatim>\<open><T>_focus\<close> = \<^const>\<open>run_parser_all\<close> of the
parser, and its round-trip law \<^verbatim>\<open><T>_focus_valid\<close>.  Field types may be
\<^verbatim>\<open>u8\<close>/\<^verbatim>\<open>u16\<close>/\<^verbatim>\<open>u32\<close>/\<^verbatim>\<open>u64\<close>/\<^verbatim>\<open>u128\<close>, \<^verbatim>\<open>bool\<close>, a pad \<^verbatim>\<open>[u8; N]\<close>, a word array
\<^verbatim>\<open>[uW; N]\<close>, an enum (from \<^verbatim>\<open>define_byte_enum\<close>), or a nested record (from a prior
\<^verbatim>\<open>define_byte_record\<close>).  A nested record reuses its \<^verbatim>\<open><T>_parser\<close>, so records
compose.\<close>

ML_file \<open>byte_encoding_record_cmd.ML\<close>

subsection\<open>Worked example\<close>

context includes code_parser_notation begin

text\<open>A small record, to be used as a nested field below.\<close>

define_byte_record pair_rec =
    pair_x: u32 | pair_y: u32

text\<open>A single record exercising every field kind at once: word fields, an enum
(\<^verbatim>\<open>demo_enum\<close>, from \<^verbatim>\<open>define_byte_enum\<close>), a boolean, a \<^verbatim>\<open>u8\<close>, a pad \<^verbatim>\<open>[u8; N]\<close>, a
nested record (\<^verbatim>\<open>pair_rec\<close>, reusing its parser), and a word array \<^verbatim>\<open>[uW; N]\<close>.
The command generates the type, the parser, the closed focus, and the round-trip
law; array/pad field types are written in a cartouche.\<close>

define_byte_record demo_record =
    dr_tag: u16 | dr_kind: demo_enum | dr_flag: bool | dr_id: u8
  | dr_pad: \<open>[u8; 3]\<close> | dr_inner: pair_rec | dr_vec: \<open>[u64; 2]\<close>

text\<open>The round-trip law was generated automatically.\<close>

lemma \<open>is_valid_focus (Rep_focus demo_record_focus)\<close>
  by (rule demo_record_focus_valid)

text\<open>The generated parser is executable.  The 32 input bytes lay out as: \<^verbatim>\<open>dr_tag\<close>
(2), \<^verbatim>\<open>dr_kind\<close> (1), \<^verbatim>\<open>dr_flag\<close> (1), \<^verbatim>\<open>dr_id\<close> (1), \<^verbatim>\<open>dr_pad\<close> (3), \<^verbatim>\<open>dr_inner\<close> (8),
\<^verbatim>\<open>dr_vec\<close> (16).  We decode them, then re-encode with an identity update and recover
the input.\<close>

definition demo_record_bytes :: \<open>byte list\<close> where
  \<open>demo_record_bytes \<equiv>
     [0x34, 0x12, 0x01, 0x01, 0x2A, 0xAA, 0xBB, 0xCC,
      0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00,
      0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
      0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10]\<close>

value[code] \<open>decode demo_record_parser demo_record_bytes\<close>

text\<open>Decoding yields exactly the expected record value.\<close>

lemma \<open>decode demo_record_parser demo_record_bytes =
         Some (make_demo_record
                 0x1234 DE_Second True 0x2A
                 (array_of_list [0xAA, 0xBB, 0xCC])
                 (make_pair_rec 1 2)
                 (array_of_list [0x0807060504030201, 0x100F0E0D0C0B0A09]))\<close>
  by eval

text\<open>Re-encoding with an identity update recovers the input bytes.\<close>

lemma \<open>encode demo_record_parser (\<lambda>x. x) demo_record_bytes = demo_record_bytes\<close>
  by eval

end

(*<*)
end
(*>*)
