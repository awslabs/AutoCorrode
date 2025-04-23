(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Byte_Parser
  imports Lenses_And_Other_Optics.Lenses_And_Other_Optics Byte_Encoding_Word_Nat Focus_Parser
    "Word_Lib.Hex_Words" "HOL-Library.Datatype_Records"
begin
(*>*)

section\<open>Byte parsers\<close>

type_synonym 'a byte_parser = \<open>(byte list, 'a) focus_parser\<close>

context
  includes code_parser_notation
begin

text\<open>Read a word\<close>

definition \<open>parse_byte \<equiv> parse_single :: byte byte_parser\<close>
definition \<open>parse_word16 \<equiv> parse_array2 >>\<^sub>\<integral> word16_byte_array_focus_le\<close>
definition \<open>parse_word32 \<equiv> parse_array4 >>\<^sub>\<integral> word32_byte_array_focus_le\<close>
definition \<open>parse_word64 \<equiv> parse_array8 >>\<^sub>\<integral> word64_byte_array_focus_le\<close>

end 

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
