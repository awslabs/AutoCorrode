(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* The `define_byte_record` command.  Given a name and a list of (field,
   field-type) pairs, it
     (1) defines the record type via `datatype_record`,
     (2) builds the field byte-prism by nesting `prod_byte_prism` over the
         per-field prisms and relabelling the resulting tuple to the named
         record via `iso_prism`, and
     (3) proves `<T>_byte_prism_valid` (the round-trip law) automatically.
   Field types: u8/u16/u32/u64/u128, bool, pad [u8; N], word array [uW; N],
   enum, and nested record. *)

signature BYTE_ENCODING_RECORD_CMD =
sig
  val define_byte_record: binding -> (binding * string) list -> local_theory -> local_theory
end

structure Byte_Encoding_Record_Cmd : BYTE_ENCODING_RECORD_CMD =
struct

(* A field's encoding info:
     hol_ty  - the HOL field type (for datatype_record)
     codec   - the byte-list codec term, as a string
     fw_thm  - a PROVED `fixed_width_prism <n> <codec>` theorem (concrete codec).
   The width <n> is read off `fw_thm`. *)
type field_enc = { hol_ty : string, codec : string, fw_thm : thm }

(* Instantiate a schematic length type variable 'l in a fixed-width theorem to a
   concrete numeral type, and simplify (turning LENGTH('l)/w*LENGTH('l) into a
   literal width).  Optionally discharge a premise with `OF [prem]` first. *)
fun inst_len ctxt n prems thm =
  let
    val thm' = case prems of [] => thm | _ => thm OF prems
    val inst = Rule_Insts.where_rule ctxt [((("'l", 0), Position.none), string_of_int n)] [] thm'
    (* Delete One_nat_def so the width is left as the numeral 1, not Suc 0
       (otherwise downstream numeral/Suc unification in the validity proof fails). *)
    val ctxt' = ctxt delsimps @{thms One_nat_def}
  in
    Simplifier.simplify ctxt' inst
  end

(* The word codec name and width for an integer width W (in bits). *)
fun word_codec 16  = ("word16_byte_list_prism_le",  2)
  | word_codec 32  = ("word32_byte_list_prism_le",  4)
  | word_codec 64  = ("word64_byte_list_prism_le",  8)
  | word_codec 128 = ("word128_byte_list_prism_le", 16)
  | word_codec w   = error ("define_byte_record: unsupported word width " ^ string_of_int w)

fun word_fw_thm 16  = @{thm fixed_width_word16_le}
  | word_fw_thm 32  = @{thm fixed_width_word32_le}
  | word_fw_thm 64  = @{thm fixed_width_word64_le}
  | word_fw_thm 128 = @{thm fixed_width_word128_le}
  | word_fw_thm w   = error ("define_byte_record: unsupported word width " ^ string_of_int w)

(* Parse an array field type `[uW; N]` into (W, N), or NONE. *)
fun parse_array ty =
  case Scan.finite Symbol.stopper
         (Scan.option (Scan.this_string "[u" |--
            Scan.many1 Symbol.is_ascii_digit -- (Scan.this_string ";" |-- Scan.many Symbol.is_ascii_blank |--
              Scan.many1 Symbol.is_ascii_digit) --| Scan.this_string "]"))
         (Symbol.explode (String.translate (fn c => if c = #" " then "" else str c) ty))
  of (SOME (w, n), _) => SOME (the (Int.fromString (implode w)), the (Int.fromString (implode n)))
   | _ => NONE

(* Map a field type name to its encoding info.  Supports: word fields (u16/u32/
   u64/u128), bool, pad [u8; N], word arrays [uW; N], and (by naming convention)
   enum / nested record types T (codec T_byte_prism, lemma fixed_width_T). *)
fun field_info _ "u16"  = { hol_ty = "16 word",  codec = "word16_byte_list_prism_le",
                            fw_thm = @{thm fixed_width_word16_le} }
  | field_info _ "u32"  = { hol_ty = "32 word",  codec = "word32_byte_list_prism_le",
                            fw_thm = @{thm fixed_width_word32_le} }
  | field_info _ "i32"  = { hol_ty = "32 word",  codec = "word32_byte_list_prism_le",
                            fw_thm = @{thm fixed_width_word32_le} }  (* i32: same 4 bytes as u32 *)
  | field_info _ "u64"  = { hol_ty = "64 word",  codec = "word64_byte_list_prism_le",
                            fw_thm = @{thm fixed_width_word64_le} }
  | field_info _ "u128" = { hol_ty = "128 word", codec = "word128_byte_list_prism_le",
                            fw_thm = @{thm fixed_width_word128_le} }
  | field_info _ "u8"   = { hol_ty = "byte",     codec = "byte_byte_list_prism",
                            fw_thm = @{thm fixed_width_u8} }
  | field_info _ "bool" = { hol_ty = "bool",     codec = "bool_byte_list_prism",
                            fw_thm = @{thm fixed_width_bool} }
  | field_info ctxt ty =
      (case parse_array ty of
         SOME (8, n) =>   (* pad: [u8; N] *)
           { hol_ty = "(byte, " ^ string_of_int n ^ ") array",
             codec  = "list_fixlen_prism :: (byte list, (byte, " ^ string_of_int n ^ ") array) prism",
             fw_thm = inst_len ctxt n [] @{thm fixed_width_pad} }
       | SOME (w, n) =>   (* word array: [uW; N] *)
           let val (cname, ew) = word_codec w in
             { hol_ty = "(" ^ string_of_int w ^ " word, " ^ string_of_int n ^ ") array",
               codec  = "array_byte_prism " ^ string_of_int ew ^ " " ^ cname
                          ^ " :: (byte list, (" ^ string_of_int w ^ " word, " ^ string_of_int n ^ ") array) prism",
               fw_thm = inst_len ctxt n [word_fw_thm w] @{thm fixed_width_array} }
           end
       | NONE =>          (* enum / nested record, by naming convention.
             A nested record (define_byte_record) has both T_byte_prism (already
             a byte-list codec) and fixed_width_T.  An enum (define_byte_enum) has
             a single-byte T_byte_prism + T_byte_prism_valid only, so we lift it
             with single_byte_prism and build its fixed width on the spot. *)
           (case try (Proof_Context.get_thm ctxt) ("fixed_width_" ^ ty) of
              SOME fw =>     (* nested record *)
                { hol_ty = ty, codec = ty ^ "_byte_prism", fw_thm = fw }
            | NONE =>        (* enum *)
                { hol_ty = ty,
                  codec  = "single_byte_prism " ^ ty ^ "_byte_prism",
                  fw_thm = @{thm fixed_width_single_byte}
                             OF [Proof_Context.get_thm ctxt (ty ^ "_byte_prism_valid")] }))

(* A nat literal may appear as a numeral, as 0, or as Suc (...) (e.g. simp leaves
   `Suc 0` for length 1).  Extract its value robustly. *)
fun dest_nat \<^Const_>\<open>Groups.zero _\<close> = 0
  | dest_nat \<^Const_>\<open>Suc for m\<close> = dest_nat m + 1
  | dest_nat t = snd (HOLogic.dest_number t)

(* Read the width <n> out of a `fixed_width_prism <n> <codec>` theorem. *)
fun width_of_fw_thm thm =
  case HOLogic.dest_Trueprop (Thm.concl_of thm) of
    \<^Const_>\<open>fixed_width_prism _\<close> $ n $ _ => dest_nat n
  | _ => error "define_byte_record: malformed fixed_width theorem"

fun define_byte_record typ_binding (fields : (binding * string) list) lthy =
  let
    val _ = if null fields
            then error "define_byte_record: need at least one field" else ()
    val typ_name = Binding.name_of typ_binding
    val field_binds = map fst fields
    val field_tys = map snd fields
    val infos = map (field_info lthy) field_tys
    val hol_tys = map #hol_ty infos

    (* Step 1: define the record type via datatype_record, inside a nested target
       so its constructor/selectors are committed before we build terms. *)
    val args = map2 (fn b => fn ty => (b, ty)) field_binds hol_tys
    val lthy1 = lthy
      |> Local_Theory.begin_nested |> snd
      |> Datatype_Records.record_cmd typ_binding Datatype_Records.default_ctr_options_cmd [] args
      |> Local_Theory.end_nested

    (* Step 2: build the codec prism as a STRING and let type inference resolve it.

       Nested prod_byte_prism (right-associative) over the per-field codecs:
         prod_byte_prism w0 p0 (prod_byte_prism w1 p1 (... p(n-1)))
       then relabel the resulting nested tuple to the named record via iso_prism:
         forward  = \<lambda>(x0, ..., x(n-1)). make_<T> x0 ... x(n-1)
         backward = \<lambda>r. (f0 r, ..., f(n-1) r)
       The record constructor is `make_<T>` and the selectors are the field names. *)
    val codec_names = map #codec infos
    val widths = map (width_of_fw_thm o #fw_thm) infos

    fun nested_prod [(_, p)] = "(" ^ p ^ ")"
      | nested_prod ((w, p) :: rest) =
          "prod_byte_prism " ^ string_of_int w ^ " (" ^ p ^ ") (" ^ nested_prod rest ^ ")"
      | nested_prod [] = error "unreachable"
    val tuple_prism_str = nested_prod (widths ~~ codec_names)

    val field_name_strs = map Binding.name_of field_binds
    val n = length fields
    val xs = map (fn i => "x" ^ string_of_int i) (0 upto n - 1)
    (* For a single field the tuple degenerates to a bare value: the iso is
       (\<lambda>x0. make_T x0) / (\<lambda>r. f0 r); otherwise it pairs the fields. *)
    val forward_str =
      if n = 1
      then "\<lambda>x0. make_" ^ typ_name ^ " x0"
      else "\<lambda>(" ^ space_implode ", " xs ^ "). make_" ^ typ_name ^ " " ^ space_implode " " xs
    val backward_str =
      if n = 1
      then "\<lambda>r. " ^ hd field_name_strs ^ " r"
      else "\<lambda>r. (" ^ space_implode ", " (map (fn f => f ^ " r") field_name_strs) ^ ")"

    val prism_str =
      "prism_compose (" ^ tuple_prism_str ^ ") (iso_prism (" ^ forward_str ^ ") (" ^ backward_str ^ "))"

    val prism_body = Syntax.read_term lthy1 prism_str
    val prism_bind = Binding.suffix_name "_byte_prism" typ_binding
    val ((_, (_, prism_def)), lthy2) = lthy1
      |> Local_Theory.define ((prism_bind, NoSyn),
           ((Binding.suffix_name "_def" prism_bind, []), prism_body))

    (* Step 3: prove <T>_byte_prism_valid.

       The codec is `prism_compose <prod-chain> <iso>`.  After prism_compose_valid:
         goal L: is_valid_prism <prod-chain>
         goal R: is_valid_prism <iso>
       For L, the prod-chain is right-nested over fields [f0, ..., f(n-1)].  Each
       prod_byte_prism_valid needs `fixed_width_prism (f_i)` for the head and
       `is_valid_prism (rest)` for the tail; the innermost field is closed by
       `fixed_width_prism_valid OF <its fw_thm>`.  Walking the field fw_thms in
       order discharges the whole chain. *)
    val fw_thms = map #fw_thm infos
    val total_width = fold (fn t => fn acc => acc + width_of_fw_thm t) fw_thms 0

    (* Discharge `is_valid_prism <prod-chain>` by walking the field fw_thms. *)
    fun prod_valid_tac ctxt [last_fw] =
          resolve_tac ctxt [@{thm fixed_width_prism_valid} OF [last_fw]] 1
      | prod_valid_tac ctxt (fw :: rest) =
          resolve_tac ctxt @{thms prod_byte_prism_valid} 1
          THEN resolve_tac ctxt [fw] 1
          THEN prod_valid_tac ctxt rest
      | prod_valid_tac _ [] = no_tac

    (* Discharge `fixed_width_prism <w> <prod-chain>` by walking the fw_thms. *)
    fun prod_fw_tac ctxt [last_fw] =
          resolve_tac ctxt [last_fw] 1
      | prod_fw_tac ctxt (fw :: rest) =
          resolve_tac ctxt @{thms prod_byte_prism_fixed_width} 1
          THEN resolve_tac ctxt [fw] 1
          THEN prod_fw_tac ctxt rest
      | prod_fw_tac _ [] = no_tac

    val iso_tac = fn ctxt =>
      resolve_tac ctxt @{thms iso_prism_valid} 1
      THEN ALLGOALS (asm_full_simp_tac (fold Splitter.add_split @{thms prod.split} ctxt))

    (* Step 3: prove <T>_byte_prism_valid. *)
    val valid_prop =
      Syntax.read_prop lthy2 ("is_valid_prism " ^ Binding.name_of prism_bind)
    val valid_thm = Goal.prove lthy2 [] [] valid_prop
      (fn {context = ctxt, ...} =>
        Local_Defs.unfold_tac ctxt [prism_def]
        THEN resolve_tac ctxt @{thms prism_compose_valid} 1
        THEN prod_valid_tac ctxt fw_thms
        THEN iso_tac ctxt)
    val valid_bind = Binding.suffix_name "_byte_prism_valid" typ_binding
    val (_, lthy3) = lthy2
      |> Local_Theory.note ((valid_bind, []), [valid_thm])

    (* Step 4: prove fixed_width_<T>, so the record can itself be a nested field.
       State the width as the sum w0 + w1 + ... (NOT pre-summed) so each
       prod_byte_prism_fixed_width step unifies its nA + nB without arithmetic;
       then simplify the registered theorem so its width is the literal total. *)
    (* right-associated sum w0 + (w1 + (... + w(n-1))), matching the right-nested
       prod chain, so prod_byte_prism_fixed_width unifies nA + nB at each step. *)
    fun right_sum [w] = string_of_int w
      | right_sum (w :: rest) = string_of_int w ^ " + (" ^ right_sum rest ^ ")"
      | right_sum [] = "0"
    val width_sum = right_sum (map width_of_fw_thm fw_thms)
    val fw_prop =
      Syntax.read_prop lthy3
        ("fixed_width_prism (" ^ width_sum ^ ") " ^ Binding.name_of prism_bind)
    val fw_thm0 = Goal.prove lthy3 [] [] fw_prop
      (fn {context = ctxt, ...} =>
        Local_Defs.unfold_tac ctxt [prism_def]
        THEN resolve_tac ctxt @{thms fixed_width_compose_iso} 1
        THEN prod_fw_tac ctxt fw_thms
        THEN ALLGOALS (asm_full_simp_tac (fold Splitter.add_split @{thms prod.split} ctxt)))
    val fw_thm = Simplifier.simplify lthy3 fw_thm0
    val fw_bind = Binding.name ("fixed_width_" ^ typ_name)
    val (_, lthy4) = lthy3
      |> Local_Theory.note ((fw_bind, []), [fw_thm])
    val _ = total_width
  in
    lthy4
  end

end

(* Parser: `define_byte_record <name> = <f0>: <ty0> | <f1>: <ty1> | ...` *)
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>define_byte_record\<close>
    "define a fixed-layout record type together with its byte serialization"
    (Parse.binding --
      (Parse.$$$ "=" |--
        Parse.enum1 "|" (Parse.binding --| Parse.$$$ ":" -- Parse.embedded))
      >> (fn (b, fields) => Byte_Encoding_Record_Cmd.define_byte_record b fields))
