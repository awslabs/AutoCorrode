(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Byte_Parser
  imports Lenses_And_Other_Optics.Lenses_And_Other_Optics Byte_Encoding_Word_Nat Byte_Encoding_Bool
    Byte_Encoding_Array Focus_Parser "Word_Lib.Hex_Words" "HOL-Library.Datatype_Records"
begin
(*>*)

section\<open>Byte parsers\<close>

type_synonym 'a byte_parser = \<open>(byte list, 'a) focus_parser\<close>

context
  includes code_parser_notation
begin

text\<open>Read a word\<close>

definition \<open>parse_byte \<equiv> parse_single :: byte byte_parser\<close>
definition \<open>parse_bool \<equiv> parse_byte >>\<^sub>\<integral> bool_byte_focus\<close>
definition \<open>parse_word16 \<equiv> parse_array2 >>\<^sub>\<integral> word16_byte_array_focus_le\<close>
definition \<open>parse_word32 \<equiv> parse_array4 >>\<^sub>\<integral> word32_byte_array_focus_le\<close>
definition \<open>parse_word64 \<equiv> parse_array8 >>\<^sub>\<integral> word64_byte_array_focus_le\<close>
definition \<open>parse_word128 \<equiv> parse_array16 >>\<^sub>\<integral> word128_byte_array_focus_le\<close>

end

subsection\<open>Parsing a fixed-length word array\<close>

text\<open>A word array \<^verbatim>\<open>[uW; N]\<close> parser, sibling to the word parsers above: for an
element prism \<^term>\<open>p\<close> of fixed width \<^term>\<open>w\<close> it peels \<^term>\<open>w * N\<close> bytes off the
front and decodes them into a length-\<^term>\<open>N\<close> array, handing the rest back.  A
parser needs a proper (typedef) focus, which only \<^verbatim>\<open>lift_definition\<close> can build;
\<^verbatim>\<open>lift_definition\<close> in turn requires the lifted raw focus to be valid for \<^emph>\<open>all\<close>
\<^term>\<open>w\<close>/\<^term>\<open>p\<close>.  The array focus is valid only when the element prism is
fixed-width, so we lift a \<^emph>\<open>guarded\<close> raw focus: the real focus when the element
is fixed-width, and the always-valid \<^const>\<open>dummy_focus\<close> otherwise.  Real call
sites always supply a fixed-width element prism, so the dummy branch is never
taken; \<^verbatim>\<open>array_parser_valid\<close> records the round-trip law under that assumption.\<close>

lift_definition array_focus ::
    \<open>nat \<Rightarrow> (byte list, 'e) prism \<Rightarrow> (byte list, ('e, 'l::len) array \<times> byte list) focus\<close> is
  \<open>\<lambda>w p. if fixed_width_prism w p
         then prism_to_focus_raw (array_split_prism w p :: (byte list, ('e, 'l) array \<times> byte list) prism)
         else dummy_focus\<close>
  by (simp add: dummy_focus_is_valid prism_to_focus_raw_valid array_split_prism_valid)

definition array_parser ::
    \<open>nat \<Rightarrow> (byte list, 'e) prism \<Rightarrow> (byte list, ('e, 'l::len) array) focus_parser\<close> where
  \<open>array_parser w p \<equiv> FocusParser (array_focus w p)\<close>

lemma array_parser_valid:
  assumes \<open>fixed_width_prism w p\<close>
    shows \<open>is_valid_focus (Rep_focus
             (array_focus w p :: (byte list, ('e, 'l::len) array \<times> byte list) focus))\<close>
  using assms by (simp add: array_focus.rep_eq array_split_prism_valid prism_to_focus_raw_valid)

subsection\<open>Examples\<close>

(*<*)
context
  includes code_parser_notation
begin
(*>*)

definition \<open>decode p \<equiv> focus_view (run_parser_all p)\<close>
definition \<open>encode p \<equiv> focus_modify (run_parser_all p)\<close>

definition \<open>data \<equiv> [0x0, 0x10, 0xDE, 0xAD, 0x10, 0x20, 0x30, 0x50, 0xBE] :: byte list\<close>
(* "Some (0x1000, 0x50302010)" :: "(16 word \<times> 32 word) option" *)
export_code  parse_byte  in OCaml

(* "Some (0x1000, 0x50302010)" *)
value[code] \<open>decode (parse_word16 --| parse_word16 -- parse_word32 --| parse_byte) data\<close>

definition \<open>too_short \<equiv> [0x0] :: byte list\<close>
(* "None" *)
value[code] \<open>decode (parse_word16 --| parse_word16 -- parse_word32 --| parse_byte) too_short\<close>

(* Decode, update, encode *)

(* "[0x2A, 0x11, 0xDE, 0xAD, 0x20, 0x40, 0x60, 0xA0, 0xBE]"
  :: "8 word list \<times> 8 word list" *)
value[code] \<open>encode (parse_word16 --| parse_word16 -- parse_word32 --| parse_byte) 
           (\<lambda>(x,y). (x+42+256,2*y)) data\<close>

(*<*)
end

end
(*>*)
