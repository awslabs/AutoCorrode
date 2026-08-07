(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* The `define_byte_record` command.  Given a name and a list of (field,
   field-type) pairs, it
     (1) defines the record type via `datatype_record`,
     (2) builds the record parser by sequencing the per-field parsers with the
         `--` combinator and relabelling the resulting nested tuple to the named
         record via `iso_focus`, and
     (3) proves `<T>_focus_valid` (the round-trip law) automatically --- for free,
         since a parser is a validity-carrying focus.
   Field types: u8/u16/u32/u64/u128, bool, pad [u8; N], word array [uW; N],
   enum, and nested record.

   Field parsers:
     word W    -> parse_wordW           (library)
     u8        -> parse_byte            (library)
     bool      -> parse_bool            (library)
     enum T    -> parse_byte >> T_focus (T_focus from define_byte_enum)
     [uW; N]   -> FocusParser <T>_<f>_focus, where <T>_<f>_focus = array_focus w p
     nested T  -> T_parser              (from a prior define_byte_record)
   Array/pad fields need a per-field focus definition plus a [code abstract]
   equation making it executable; the other field parsers are library constants,
   already executable. *)

signature BYTE_ENCODING_RECORD_CMD =
sig
  val define_byte_record: binding -> (binding * string) list -> local_theory -> local_theory
end

structure Byte_Encoding_Record_Cmd : BYTE_ENCODING_RECORD_CMD =
struct

(* Parse an array field type `[uW; N]` into (W, N), or NONE. *)
fun parse_array ty =
  case Scan.finite Symbol.stopper
         (Scan.option (Scan.this_string "[u" |--
            Scan.many1 Symbol.is_ascii_digit -- (Scan.this_string ";" |-- Scan.many Symbol.is_ascii_blank |--
              Scan.many1 Symbol.is_ascii_digit) --| Scan.this_string "]"))
         (Symbol.explode (String.translate (fn c => if c = #" " then "" else str c) ty))
  of (SOME (w, n), _) => SOME (the (Int.fromString (implode w)), the (Int.fromString (implode n)))
   | _ => NONE

(* The element byte-width and element prism for a word width W (in bits). *)
fun word_elem 16  = (2,  "word16_byte_list_prism_le")
  | word_elem 32  = (4,  "word32_byte_list_prism_le")
  | word_elem 64  = (8,  "word64_byte_list_prism_le")
  | word_elem 128 = (16, "word128_byte_list_prism_le")
  | word_elem w   = error ("define_byte_record: unsupported word width " ^ string_of_int w)

(* The fixed-width fact for a word element prism (used in the array focus's
   [code abstract] proof). *)
fun word_elem_fw 16  = @{thm fixed_width_word16_le}
  | word_elem_fw 32  = @{thm fixed_width_word32_le}
  | word_elem_fw 64  = @{thm fixed_width_word64_le}
  | word_elem_fw 128 = @{thm fixed_width_word128_le}
  | word_elem_fw w   = error ("define_byte_record: unsupported word width " ^ string_of_int w)

(* A field's parser info:
     hol_ty  - the HOL field type (for datatype_record)
     parser  - either a library parser term (Direct), or an array/pad field that
               needs a per-field focus definition (Array).
   Array carries (element width w, element prism string, element fixed-width thm),
   from which the command generates <T>_<f>_focus = array_focus w p and its
   [code abstract] equation, then uses FocusParser <T>_<f>_focus as the parser. *)
datatype parser_info =
    Direct of string                       (* a ready library parser term *)
  | Array of int * string * thm * string   (* (elem width, elem prism, elem fw thm, array hol type) *)

type field_info = { hol_ty : string, parser : parser_info }

(* Map a field type name to its HOL type and parser info. *)
fun field_info _ "u16"  = { hol_ty = "16 word",  parser = Direct "parse_word16" }
  | field_info _ "u32"  = { hol_ty = "32 word",  parser = Direct "parse_word32" }
  | field_info _ "i32"  = { hol_ty = "32 word",  parser = Direct "parse_word32" }  (* i32: same 4 bytes as u32 *)
  | field_info _ "u64"  = { hol_ty = "64 word",  parser = Direct "parse_word64" }
  | field_info _ "u128" = { hol_ty = "128 word", parser = Direct "parse_word128" }
  | field_info _ "u8"   = { hol_ty = "byte",     parser = Direct "parse_byte" }
  | field_info _ "bool" = { hol_ty = "bool",     parser = Direct "parse_bool" }
  | field_info ctxt ty =
      (case parse_array ty of
         SOME (8, n) =>   (* pad [u8; N]: array of raw bytes *)
           let val aty = "(byte, " ^ string_of_int n ^ ") array" in
             { hol_ty = aty, parser = Array (1, "byte_id_prism", @{thm fixed_width_byte_id}, aty) }
           end
       | SOME (w, n) =>   (* word array [uW; N] *)
           let
             val (ew, cname) = word_elem w
             val aty = "(" ^ string_of_int w ^ " word, " ^ string_of_int n ^ ") array"
           in
             { hol_ty = aty, parser = Array (ew, cname, word_elem_fw w, aty) }
           end
       | NONE =>          (* enum or nested record, by naming convention.
             A nested record (define_byte_record) exposes T_parser directly.
             An enum (define_byte_enum) exposes a single-byte focus T_focus,
             composed with parse_byte to read one discriminant byte. *)
           (case try (Proof_Context.get_thm ctxt) (ty ^ "_parser_def") of
              SOME _ => { hol_ty = ty, parser = Direct (ty ^ "_parser") }   (* nested record *)
            | NONE   => { hol_ty = ty,
                          parser = Direct ("focus_parser_map parse_byte " ^ ty ^ "_focus") }))

(* Define a constant `<bind>` from a term string, returning (def theorem, lthy). *)
fun define_from_string bind rhs_str lthy =
  let
    val rhs = Syntax.read_term lthy rhs_str
    val ((_, (_, def_thm)), lthy') = lthy
      |> Local_Theory.define ((bind, NoSyn), ((Binding.suffix_name "_def" bind, []), rhs))
  in (def_thm, lthy') end

fun define_byte_record typ_binding (fields : (binding * string) list) lthy =
  let
    val _ = if null fields
            then error "define_byte_record: need at least one field" else ()
    val typ_name = Binding.name_of typ_binding
    val field_binds = map fst fields
    val field_name_strs = map Binding.name_of field_binds
    val field_tys = map snd fields
    val infos = map (field_info lthy) field_tys
    val n = length fields

    (* Step 1: define the record type via datatype_record, in a nested target so
       its constructor/selectors are committed before we build later terms. *)
    val args = map2 (fn b => fn i => (b, #hol_ty i)) field_binds infos
    val lthy1 = lthy
      |> Local_Theory.begin_nested |> snd
      |> Datatype_Records.record_cmd typ_binding Datatype_Records.default_ctr_options_cmd [] args
      |> Local_Theory.end_nested

    (* Step 2: for each array/pad field, define <T>_<f>_focus = array_focus w p
       and prove its [code abstract] rep equation, so the field parser is
       executable.  Returns the parser term string for each field. *)
    fun field_parser (fname, { parser = Direct s, ... } : field_info) lthy_acc = (s, lthy_acc)
      | field_parser (fname, { parser = Array (ew, elem, elem_fw, aty), ... }) lthy_acc =
          let
            val focus_bind = Binding.name (typ_name ^ "_" ^ fname ^ "_focus")
            val focus_name = Binding.name_of focus_bind
            (* Annotate with the concrete array type so the length N is pinned,
               not left schematic. *)
            val focus_ty = "(byte list, " ^ aty ^ " \<times> byte list) focus"
            val (_, lthy_a) =
              define_from_string focus_bind
                ("array_focus " ^ string_of_int ew ^ " " ^ elem ^ " :: " ^ focus_ty) lthy_acc
            val focus_def = Proof_Context.get_thm lthy_a (focus_name ^ "_def")
            val rep_prop =
              Syntax.read_prop lthy_a
                ("Rep_focus " ^ focus_name ^ " = prism_to_focus_raw (array_split_prism "
                   ^ string_of_int ew ^ " " ^ elem ^ " :: (byte list, " ^ aty ^ " \<times> byte list) prism)")
            val rep_thm = Goal.prove lthy_a [] [] rep_prop
              (fn {context = ctxt, ...} =>
                Local_Defs.unfold_tac ctxt [focus_def]
                THEN EqSubst.eqsubst_tac ctxt [0] @{thms array_focus.rep_eq} 1
                THEN asm_full_simp_tac (ctxt addsimps [elem_fw] delsimps @{thms One_nat_def}) 1)
            val lthy_b = lthy_a |> Code.declare_abstract_eqn rep_thm
          in ("FocusParser " ^ focus_name, lthy_b) end

    val (parser_strs, lthy2) =
      fold_map field_parser (field_name_strs ~~ infos) lthy1

    (* Step 3: sequence the field parsers with focus_parser_sequence (the -- of
       the parser notation) left-associatively, producing a left-nested tuple
       ((..((x0,x1),x2)..),x(n-1)).  We use the full constant name rather than the
       -- notation so the command does not depend on the notation bundle being in
       scope at the call site. *)
    val parser_chain =
      foldl1 (fn (a, b) => "focus_parser_sequence (" ^ a ^ ") (" ^ b ^ ")") parser_strs

    (* The left-nested tuple pattern and the constructor application. *)
    val xs = map (fn i => "x" ^ string_of_int i) (0 upto n - 1)
    fun left_nest [x] = x
      | left_nest xs' = "(" ^ left_nest (rev (tl (rev xs'))) ^ ", " ^ List.last xs' ^ ")"
    val tuple_pat = left_nest xs
    val make_app = "make_" ^ typ_name ^ " " ^ space_implode " " xs
    val sels_nest = left_nest (map (fn f => f ^ " r") field_name_strs)

    val forward_str = "\<lambda>" ^ tuple_pat ^ ". " ^ make_app
    val backward_str = "\<lambda>r. " ^ sels_nest

    (* Step 4: define <T>_tuple_focus = iso_focus <forward> <backward> and prove
       its [code abstract] rep equation (the iso laws hold by the record simps). *)
    val tuple_bind = Binding.name (typ_name ^ "_tuple_focus")
    val tuple_name = Binding.name_of tuple_bind
    val (_, lthy3) =
      define_from_string tuple_bind
        ("iso_focus (" ^ forward_str ^ ") (" ^ backward_str ^ ")") lthy2
    val tuple_def = Proof_Context.get_thm lthy3 (tuple_name ^ "_def")
    val tuple_rep_prop =
      Syntax.read_prop lthy3
        ("Rep_focus " ^ tuple_name ^ " = iso\<^sub>\<integral> (" ^ forward_str ^ ") (" ^ backward_str ^ ")")
    val tuple_rep_thm = Goal.prove lthy3 [] [] tuple_rep_prop
      (fn {context = ctxt, ...} =>
        Local_Defs.unfold_tac ctxt [tuple_def]
        THEN EqSubst.eqsubst_tac ctxt [0] @{thms iso_focus.rep_eq} 1
        THEN asm_full_simp_tac (fold Splitter.add_split @{thms prod.split} ctxt) 1)
    val lthy4 = lthy3 |> Code.declare_abstract_eqn tuple_rep_thm

    (* Step 5: <T>_parser = (parser chain) >> <T>_tuple_focus.  Declare its
       defining equation as a code equation so the parser is executable (the
       field parsers and focus reps are already executable). *)
    val parser_bind = Binding.suffix_name "_parser" typ_binding
    val (parser_def, lthy5) =
      define_from_string parser_bind
        ("focus_parser_map (" ^ parser_chain ^ ") " ^ tuple_name) lthy4
    val lthy5 = lthy5 |> Code.declare_default_eqns [(parser_def, true)]

    (* Step 6: <T>_focus = run_parser_all <T>_parser, and its validity --- for
       free, since a focus is validity-carrying (Rep_focus lands in the typedef). *)
    val focus_bind = Binding.suffix_name "_focus" typ_binding
    val (_, lthy6) =
      define_from_string focus_bind
        ("run_parser_all " ^ Binding.name_of parser_bind) lthy5
    val focus_def = Proof_Context.get_thm lthy6 (Binding.name_of focus_bind ^ "_def")
    val valid_prop =
      Syntax.read_prop lthy6
        ("is_valid_focus (Rep_focus " ^ Binding.name_of focus_bind ^ ")")
    val valid_thm = Goal.prove lthy6 [] [] valid_prop
      (fn {context = ctxt, ...} =>
        Local_Defs.unfold_tac ctxt [focus_def]
        THEN resolve_tac ctxt @{thms Rep_focus[simplified]} 1)
    val valid_bind = Binding.suffix_name "_focus_valid" typ_binding
    val (_, lthy7) = lthy6
      |> Local_Theory.note ((valid_bind, []), [valid_thm])
  in
    lthy7
  end

end

(* Parser: `define_byte_record <name> = <f0>: <ty0> | <f1>: <ty1> | ...` *)
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>define_byte_record\<close>
    "define a fixed-layout record type together with its byte-parser serialization"
    (Parse.binding --
      (Parse.$$$ "=" |--
        Parse.enum1 "|" (Parse.binding --| Parse.$$$ ":" -- Parse.embedded))
      >> (fn (b, fields) => Byte_Encoding_Record_Cmd.define_byte_record b fields))
