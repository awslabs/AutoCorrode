(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Two uRust plugins for `simple_word_enum`, both keyed off the declaration's optional
   `urust: "Name"` clause and independently selectable:

     urust_notation   -- each variant Ci as the uRust notation `Name::Ci`
     urust_conversion -- the word_conversion plugin's to/try_from functions lifted into
                         uRust function_body form, as `Name::to_uN` / `Name::try_from`

   These live here rather than beside the command in Misc.Simple_Word_Enums because
   `micro_rust_notation` is defined in this session, which depends on Misc --- not the other
   way round. Registering a plugin from a downstream theory is exactly what the plugin
   mechanism is for (cf. bnf_lfp_size.ML registering against datatype). *)

(*<*)
theory Simple_Word_Enum_uRust
  imports
    Misc.Simple_Word_Enums
    (* Micro_Rust_Notations for the registry itself; the shallow embedding for the `\<lbrakk> _ \<rbrakk>`
       brackets the tests below use to check that the names really do resolve in uRust, and
       Core_Expression_Lemmas for the micro_rust_simps rules (call_literal2 in particular)
       that reduce a lifted call in those tests. *)
    Micro_Rust_Shallow_Embedding
    Core_Expression_Lemmas
begin
(*>*)

section\<open>\<open>\<mu>Rust\<close> notation for simple word enums\<close>

text\<open>A \<^verbatim>\<open>simple_word_enum\<close> declaration may carry an optional \<^verbatim>\<open>urust: "Name"\<close> clause. The command
itself only records that name on the \<^verbatim>\<open>enum_info\<close> it hands to plugins; the two plugins defined
here are what act on it, and they are selectable independently:

  \<^item> \<^verbatim>\<open>urust_notation\<close> --- each variant as \<^verbatim>\<open>Name::Ci\<close>;
  \<^item> \<^verbatim>\<open>urust_conversion\<close> --- the conversion functions as \<^verbatim>\<open>Name::to_uN\<close> / \<^verbatim>\<open>Name::try_from\<close>.

Both are no-ops without a \<^verbatim>\<open>urust:\<close> clause.\<close>

subsection\<open>\<open>\<mu>Rust\<close> names for the variants\<close>

text\<open>The \<^verbatim>\<open>urust_notation\<close> plugin registers

\<^verbatim>\<open>Name::Ci\<close>

as \<open>\<mu>Rust\<close> notation for each variant \<^verbatim>\<open>Ci\<close>, so that \<open>\<mu>Rust\<close> code can write \<^verbatim>\<open>MyEnum::Answer\<close> where
HOL writes \<^verbatim>\<open>Answer\<close>. This is the same registration \<^verbatim>\<open>StdLib_Ordering\<close> performs by hand for the
\<^verbatim>\<open>ordering\<close> datatype (\<^verbatim>\<open>Ordering::Less\<close> and friends), just derived from the declaration instead
of written out per variant.

Variants are registered as \<^emph>\<open>literals\<close>: a variant is a nullary constant of the enum type, which
is what \<^verbatim>\<open>infer_kind_of_type\<close> classifies as a literal anyway --- we force it so that a variant
whose enum type somehow looked function- or lens-shaped could not be misfiled.

With no \<^verbatim>\<open>urust:\<close> clause the plugin does nothing, so it is harmless on every enum that does not
want \<open>\<mu>Rust\<close> notation. It can also be suppressed explicitly with
\<^verbatim>\<open>simple_word_enum (plugins del: urust_notation) ...\<close>.

Note that \<^verbatim>\<open>Name::Ci\<close> is a \<^verbatim>\<open>::\<close>-path, which the \<open>\<mu>Rust\<close> frontend's grammar already parses, so
no bespoke grammar production is needed --- the dispatch-table entry alone suffices. A
\<^verbatim>\<open>urust:\<close> name that is not a plain identifier is therefore rejected up front, rather than
producing a registration whose use sites could never parse.\<close>

ML \<open>
(* Shared by both plugins below: the `urust:` name, validated, or NONE when the declaration
   gave none (in which case both plugins are no-ops). *)
structure Simple_Word_Enum_uRust = struct

(* The name has to be a plain identifier: it becomes the head of a ::-path, and anything else
   (turbofish, `!`, ...) would need a bespoke grammar production that neither plugin emits.
   Rejecting here gives a message pointing at the declaration rather than at a later,
   mysterious parse failure. *)
fun urust_name_of (info: Simple_Word_Enum.enum_info) =
  case #urust_name info of
    NONE => NONE
  | SOME name =>
      if Symbol_Pos.is_identifier name then SOME name
      else error ("simple_word_enum " ^ #type_name info ^ ": urust name " ^ quote name ^
        " is not a plain identifier, so " ^ quote (name ^ "::<item>") ^
        " would not parse as a uRust path")

(* Register `rust_name` as a uRust notation for the term `t`, in the given kind. This is what
   `micro_rust_notation (<kind>) <term> ("<rust_name>")` does; `Name::item` is a ::-path, which
   the frontend grammar already parses, so no bespoke grammar production is needed. The term
   goes through the declaration's morphism, so it is correct in whatever target the enum was
   declared in. *)
fun register_notation kind rust_name t =
  Local_Theory.declaration {pervasive = false, syntax = true, pos = \<^here>}
    (fn phi => Micro_Rust_Names.register kind rust_name (Morphism.term phi t) \<^here>)

end
\<close>

ML \<open>
local

(* `Name::Ci` for variant Ci. The enum's own variant binding supplies Ci, so the uRust name
   tracks whatever the declaration called the variant. *)
fun urust_variant_name enum_name binding = enum_name ^ "::" ^ Binding.name_of binding

fun generate_urust_notation (info: Simple_Word_Enum.enum_info) lthy =
  case Simple_Word_Enum_uRust.urust_name_of info of
    (* No `urust:` clause: nothing to do. This is the common case. *)
    NONE => lthy
  | SOME enum_name =>
      let
        val { variant_bindings, variant_consts, timer, ... } = info
        fun phase name f = Simple_Word_Enum.phase timer name f
        val pairs = variant_bindings ~~ variant_consts

        val lthy = phase "urust_notation" (fn () =>
          fold (fn (binding, c) =>
            Simple_Word_Enum_uRust.register_notation Micro_Rust_Names.NLiteral
              (urust_variant_name enum_name binding) c) pairs lthy)

        val _ = if not (#report info) then () else
          writeln ("  plugin urust_notation:\n" ^ cat_lines (map (prefix "    ")
            (map (fn (b, _) => "notation    " ^ urust_variant_name enum_name b ^
               " \<longmapsto> " ^ Binding.name_of b) pairs)))
      in lthy end

in

val urust_notation_plugin = Plugin_Name.declare_setup \<^binding>\<open>urust_notation\<close>

val _ = Theory.setup
  (Simple_Word_Enum.interpretation urust_notation_plugin generate_urust_notation)

end
\<close>

subsection\<open>\<open>\<mu>Rust\<close> conversion functions\<close>

text\<open>The \<^verbatim>\<open>urust_conversion\<close> plugin lifts the two conversion functions the \<^verbatim>\<open>word_conversion\<close>
plugin generates into \<open>\<mu>Rust\<close> \<^const>\<open>function_body\<close> form with \<^const>\<open>lift_fun1\<close>, and registers each
under a \<^verbatim>\<open>Name::\<close> path:

  \<^item> \<^verbatim>\<open>T_to_uN :: T \<Rightarrow> (_, N word, _, _, _) function_body\<close> \<open>\<equiv> lift_fun1 T_to_uN_pure\<close>,
    as \<^verbatim>\<open>Name::to_uN\<close>;
  \<^item> \<^verbatim>\<open>T_try_from_uN :: N word \<Rightarrow> (_, (T, unit) result, _, _, _) function_body\<close>
    \<open>\<equiv> lift_fun1 T_try_from_uN_pure\<close>, as \<^verbatim>\<open>Name::try_from\<close>.

This mirrors \<^const>\<open>word_try_from_fun\<close> in \<^theory>\<open>Shallow_Micro_Rust.Numeric_Types\<close>, which lifts
\<^const>\<open>word_try_from_pure\<close> exactly this way.

The \<^verbatim>\<open>_def\<close> facts are \<^emph>\<open>not\<close> tagged \<^verbatim>\<open>[micro_rust_simps]\<close>: whether a call unfolds to its pure
function during \<open>\<mu>Rust\<close> reasoning is left to the caller, who names \<^verbatim>\<open>T_to_uN_def\<close> explicitly (or
declares it \<^verbatim>\<open>[micro_rust_simps]\<close> locally). Once unfolded, the \<^verbatim>\<open>_alt\<close> characterisations the
\<^verbatim>\<open>word_conversion\<close> plugin proves apply as usual --- see the tests below.

This is a \<^emph>\<open>separate\<close> plugin from \<^verbatim>\<open>urust_notation\<close> so the two can be chosen independently: an
enum may want its variants nameable from \<open>\<mu>Rust\<close> without the conversion functions, or the reverse.
It does need \<^verbatim>\<open>word_conversion\<close>, though --- that is where the pure functions come from --- so it
errors if that plugin was suppressed, rather than silently doing nothing.\<close>

ML \<open>
local

fun generate_urust_conversion (info: Simple_Word_Enum.enum_info) lthy =
  case Simple_Word_Enum_uRust.urust_name_of info of
    NONE => lthy
  | SOME enum_name =>
      let
        val { type_name, absT, wordT, width, timer, ... } = info
        fun phase name f = Simple_Word_Enum.phase timer name f
        val uN = "u" ^ string_of_int width

        (* The pure functions come from the word_conversion plugin. They are looked up by name
           because that plugin cannot hand them over directly: plugins receive the same
           enum_info and there is no ordering or channel between them. A missing constant means
           word_conversion did not run, which is a declaration error rather than something to
           paper over --- the two plugins are independent, but this one genuinely depends on
           that one. *)
        fun pure_const base result_ty =
          let val name = type_name ^ "_" ^ base
          in
            case try (Proof_Context.read_const {proper = true, strict = false} lthy) name of
              SOME (Const (c, _)) => Const (c, result_ty)
            | _ => error (cat_lines
                ["simple_word_enum " ^ type_name ^ ": the urust_conversion plugin cannot find " ^
                   quote name ^ ",",
                 "so the word_conversion plugin apparently did not run --- that is where the pure",
                 "conversion functions come from, and urust_conversion has nothing to lift without",
                 "them.",
                 "",
                 "If suppressing word_conversion was deliberate, disable urust_conversion",
                 "explicitly as well:",
                 "",
                 "  simple_word_enum (plugins del: word_conversion urust_conversion) ...",
                 "",
                 "Ordering is not the cause: word_conversion is registered in\
                 \ Misc.Simple_Word_Enums,",
                 "which this theory depends on, so it always runs first when both are enabled."])
          end

        val unitT = HOLogic.unitT
        val resultT = Type (\<^type_name>\<open>result\<close>, [absT, unitT])
        val to_pure = pure_const ("to_" ^ uN ^ "_pure") (absT --> wordT)
        val from_pure = pure_const ("try_from_" ^ uN ^ "_pure") (wordT --> resultT)

        (* lift_fun1 f, at the function_body type. The four remaining tvars ('s, 'abort, 'i,
           'o) stay schematic, exactly as in a hand-written `definition ... = lift_fun1 f`. *)
        fun lift f =
          let
            val (dom, rng) = Term.dest_funT (fastype_of f)
            fun v n = TFree (n, \<^sort>\<open>type\<close>)
            val bodyT = Type (\<^type_name>\<open>function_body\<close>,
              [v "'s", rng, v "'abort", v "'i", v "'o"])
            val lift_fun1T = (dom --> rng) --> (dom --> bodyT)
          in Const (\<^const_name>\<open>lift_fun1\<close>, lift_fun1T) $ f end

        (* `definition T_to_uN: T_to_uN \<equiv> lift_fun1 T_to_uN_pure`, and the same for try_from.
           Deliberately *not* tagged [micro_rust_simps]: whether these unfold during uRust
           reasoning is the caller's choice, so the `_def` facts have to be named explicitly
           (or declared [micro_rust_simps] downstream) to fire.

           They are defined via Specification.definition, which attaches a default code
           equation --- orthogonal to the simp bundle, and what makes them code-exportable. *)
        fun define base rhs lthy =
          let
            val name = type_name ^ "_" ^ base
            val binding = Binding.name name
            val (_, lthy) = Specification.definition {verbose = false}
              (SOME (binding, NONE, NoSyn)) [] []
              ((Binding.name (name ^ "_def"), []),
               Logic.mk_equals (Free (name, fastype_of rhs), rhs)) lthy
            val const = Const (Local_Theory.full_name lthy binding, fastype_of rhs)
          in ((name, const), lthy) end

        val ((to_name, to_const), lthy) = phase "urust_to_fun" (fn () =>
          define ("to_" ^ uN) (lift to_pure) lthy)
        val ((from_name, from_const), lthy) = phase "urust_try_from_fun" (fn () =>
          define ("try_from_" ^ uN) (lift from_pure) lthy)

        (* Registered as `call`: these are function_body-valued, which is what the function
           kind is for. Rust spells them `T::to_uN()` / `T::try_from()`. *)
        val registrations =
          [(enum_name ^ "::to_" ^ uN, to_const, to_name),
           (enum_name ^ "::try_from", from_const, from_name)]
        val lthy = phase "urust_conversion_notation" (fn () =>
          fold (fn (rust_name, c, _) =>
            Simple_Word_Enum_uRust.register_notation Micro_Rust_Names.NFunction rust_name c)
            registrations lthy)

        val _ = if not (#report info) then () else
          writeln ("  plugin urust_conversion:\n" ^ cat_lines (map (prefix "    ")
            (maps (fn (rust_name, _, hol_name) =>
               ["definition  " ^ hol_name,
                "notation    " ^ rust_name ^ " \<longmapsto> " ^ hol_name]) registrations)))
      in lthy end

in

val urust_conversion_plugin = Plugin_Name.declare_setup \<^binding>\<open>urust_conversion\<close>

val _ = Theory.setup
  (Simple_Word_Enum.interpretation urust_conversion_plugin generate_urust_conversion)

end
\<close>

subsection\<open>Tests\<close>

text\<open>A declaration with a \<^verbatim>\<open>urust:\<close> clause. Kept global (not inside an \<^verbatim>\<open>experiment\<close>) because
notation registration is a global effect.\<close>

simple_word_enum (32) message_kind urust: "MessageKind" =
    MK_Ping = \<open>0x1\<close>
  | MK_Pong = \<open>0x2\<close>
  | MK_Data = \<open>0xff\<close>

text\<open>The registrations are in place, and each \<open>\<mu>Rust\<close> path resolves to its HOL variant.\<close>

ML \<open>
  let
    fun lookup n =
      Micro_Rust_Names.lookups @{context} Micro_Rust_Names.NLiteral ("MessageKind::" ^ n)
    fun the_backend n =
      case lookup n of
        [{ hol_term, ... }] => hol_term
      | es => error ("expected exactly one backend for MessageKind::" ^ n ^
          ", got " ^ string_of_int (length es))
    val _ = @{assert} (the_backend "MK_Ping" aconv @{term MK_Ping})
    val _ = @{assert} (the_backend "MK_Pong" aconv @{term MK_Pong})
    val _ = @{assert} (the_backend "MK_Data" aconv @{term MK_Data})
    (* The HOL type name is not itself a registered prefix --- only the uRust name is. *)
    val _ = @{assert} (null (lookup "MK_Nope"))
    val _ = @{assert} (null
      (Micro_Rust_Names.lookups @{context} Micro_Rust_Names.NLiteral "message_kind::MK_Ping"))
  in writeln "MessageKind::* registered, resolving to the HOL variants" end
\<close>

text\<open>The acceptance test: the \<open>\<mu>Rust\<close> path really does resolve, so the embedding is syntactically
equal to the \<^const>\<open>literal\<close> of the HOL variant --- \<^emph>\<open>not\<close> a free variable named
\<^verbatim>\<open>MessageKind::MK_Ping\<close>.\<close>

term \<open>\<lbrakk> MessageKind::MK_Ping \<rbrakk>\<close>

lemma
  shows \<open>\<lbrakk> MessageKind::MK_Ping \<rbrakk> = literal MK_Ping\<close>
    and \<open>\<lbrakk> MessageKind::MK_Pong \<rbrakk> = literal MK_Pong\<close>
    and \<open>\<lbrakk> MessageKind::MK_Data \<rbrakk> = literal MK_Data\<close>
  by (rule refl)+

text\<open>The lifted conversion functions exist and are \<^const>\<open>lift_fun1\<close> of the pure ones.\<close>

lemma
  shows \<open>message_kind_to_u32 = lift_fun1 message_kind_to_u32_pure\<close>
    and \<open>message_kind_try_from_u32 = lift_fun1 message_kind_try_from_u32_pure\<close>
  by (simp_all add: message_kind_to_u32_def message_kind_try_from_u32_def)

text\<open>They are code-exportable, along with the pure functions they lift. This comes from
\<^verbatim>\<open>Specification.definition\<close>'s default code equation --- the plugin adds no \<^verbatim>\<open>[code]\<close> of its own,
and \<^verbatim>\<open>Local_Theory.define\<close> (which the plugin used at first) would have attached none, leaving
\<^verbatim>\<open>export_code\<close> to fail with "No code equations".\<close>

export_code message_kind_to_u32_pure message_kind_try_from_u32_pure
  in OCaml module_name MessageKindPure

export_code message_kind_to_u32 message_kind_try_from_u32
  in OCaml module_name MessageKindFun

export_code message_kind_to_u32 message_kind_try_from_u32
  in SML module_name MessageKindFun

value \<open>message_kind_to_u32_pure MK_Data\<close>
value \<open>message_kind_try_from_u32_pure 2\<close>
value \<open>message_kind_try_from_u32_pure 7\<close>

text\<open>Their \<open>\<mu>Rust\<close> paths resolve as function calls --- these type-check, which is the point: an
unregistered path would leave a free variable and fail to elaborate at the \<^const>\<open>function_body\<close>
type the call position demands.\<close>

term \<open>\<lbrakk> MessageKind::to_u32(e) \<rbrakk>\<close>
term \<open>\<lbrakk> MessageKind::try_from(w) \<rbrakk>\<close>

text\<open>Naming the \<^verbatim>\<open>_def\<close> fact unfolds a call to its pure function --- which is what makes the
\<^verbatim>\<open>_alt\<close> characterisations from \<^verbatim>\<open>word_conversion\<close> usable on \<open>\<mu>Rust\<close> code. Evaluated on a concrete
variant, a call then reduces to a literal:\<close>

lemma
  shows \<open>\<lbrakk> MessageKind::to_u32(MK_Data) \<rbrakk> = \<up>(0xff :: 32 word)\<close>
  by (simp add: micro_rust_simps message_kind_to_u32_def message_kind_to_u32_pure_def)

text\<open>Since the \<^verbatim>\<open>_def\<close>s are not \<^verbatim>\<open>[micro_rust_simps]\<close>, \<^emph>\<open>not\<close> naming them leaves the call
unreduced --- the caller decides when to unfold.\<close>

lemma
  shows \<open>\<lbrakk> MessageKind::to_u32(MK_Data) \<rbrakk> = message_kind_to_u32 \<langle>\<up>MK_Data\<rangle>\<close>
  by (simp add: micro_rust_simps)

text\<open>End to end: a \<open>\<mu>Rust\<close> round trip on a variant named the \<open>\<mu>Rust\<close> way, discharged by the round-trip
lemma \<^verbatim>\<open>word_conversion\<close> proves.\<close>

lemma
  shows \<open>\<lbrakk> MessageKind::try_from(MessageKind::to_u32(MK_Data)) \<rbrakk> = \<up>(Ok MK_Data)\<close>
  by (simp add: micro_rust_simps message_kind_to_u32_def message_kind_try_from_u32_def
        message_kind_to_u32_pure_then_try_from)

text\<open>\<^verbatim>\<open>print_micro_rust_notations\<close> lists them alongside the hand-written ones.\<close>

print_micro_rust_notations

text\<open>Without a \<^verbatim>\<open>urust:\<close> clause both plugins are no-ops --- nothing is registered under the type's
own name, and no lifted functions appear.\<close>

simple_word_enum (8) unnamed_kind = UK_A = 1 | UK_B = 2

ML \<open>
  let
    val all = Micro_Rust_Names.dump @{context}
    val bad = filter (fn (_, n, _) => String.isSubstring "UK_" n
                                      orelse String.isSubstring "unnamed_kind" n) all
    val no_const = not (can (Proof_Context.read_const {proper = true, strict = false}
      @{context}) "unnamed_kind_to_u8")
  in
    @{assert} (null bad); @{assert} no_const;
    writeln "no urust: clause: no notations, no lifted functions"
  end
\<close>

text\<open>The two plugins are independent. \<^verbatim>\<open>plugins del: urust_conversion\<close> keeps the variant names but
drops the lifted functions.\<close>

simple_word_enum (plugins del: urust_conversion) (8) names_only urust: "NamesOnly" =
    NO_A = 1 | NO_B = 2

ML \<open>
  let
    val lit = Micro_Rust_Names.lookups @{context} Micro_Rust_Names.NLiteral "NamesOnly::NO_A"
    val fn_ = Micro_Rust_Names.lookups @{context} Micro_Rust_Names.NFunction "NamesOnly::try_from"
    val no_const = not (can (Proof_Context.read_const {proper = true, strict = false}
      @{context}) "names_only_to_u8")
  in
    @{assert} (length lit = 1); @{assert} (null fn_); @{assert} no_const;
    writeln "del: urust_conversion --- variant names kept, lifted functions dropped"
  end
\<close>

text\<open>And the reverse: \<^verbatim>\<open>plugins del: urust_notation\<close> keeps the lifted conversion functions but
drops the variant names.\<close>

simple_word_enum (plugins del: urust_notation) (8) convs_only urust: "ConvsOnly" =
    CO_A = 1 | CO_B = 2

ML \<open>
  let
    val lit = Micro_Rust_Names.lookups @{context} Micro_Rust_Names.NLiteral "ConvsOnly::CO_A"
    val fn_ = Micro_Rust_Names.lookups @{context} Micro_Rust_Names.NFunction "ConvsOnly::try_from"
  in
    @{assert} (null lit); @{assert} (length fn_ = 1);
    writeln "del: urust_notation --- lifted functions kept, variant names dropped"
  end
\<close>

text\<open>The variant has to be spelled the HOL way here, since \<^verbatim>\<open>urust_notation\<close> was suppressed ---
but the \<^emph>\<open>function\<close> path still resolves, which is the independence being tested.\<close>

lemma
  shows \<open>\<lbrakk> ConvsOnly::try_from(w) \<rbrakk> = \<up>(convs_only_try_from_u8_pure w)\<close>
  by (simp add: micro_rust_simps convs_only_try_from_u8_def)

text\<open>Both suppressed at once.\<close>

simple_word_enum (plugins del: urust_notation urust_conversion) (8) quiet_kind
    urust: "QuietKind" =
    QK_A = 1 | QK_B = 2

ML \<open>
  let
    val all = Micro_Rust_Names.dump @{context}
    val bad = filter (fn (_, n, _) => String.isSubstring "QuietKind" n) all
  in
    @{assert} (null bad);
    writeln "both uRust plugins suppressed"
  end
\<close>

lemma
  shows \<open>quiet_kind_try_from_u8_pure 1 = Ok QK_A\<close>
  by (simp add: quiet_kind_try_from_u8_pure_alt quiet_kind_variants_def quiet_kind_defs)

text\<open>Suppressing \<^verbatim>\<open>word_conversion\<close> while leaving \<^verbatim>\<open>urust_conversion\<close> on is the one combination
that cannot work: the pure conversion functions never get defined, so there is nothing to lift.
That is an \<^emph>\<open>error\<close> rather than a silent no-op, since it can only arise from an explicit and
contradictory pair of plugin choices.

Run for real below --- inside \<^ML>\<open>Exn.capture\<close>, so the failure is observed without failing this
theory. The declaration is driven through \<^verbatim>\<open>simple_word_enum_core\<close> on a throwaway local theory
which is then discarded, exactly as \<^verbatim>\<open>simple_word_enum_benchmark\<close> does.\<close>

ML \<open>
  let
    (* `(plugins del: word_conversion)`, with urust_conversion left enabled. *)
    fun filter_del_word_conversion _ = fn name => name <> "word_conversion"
    val attempt = Exn.capture (fn () =>
      Simple_Word_Enum.simple_word_enum_core
        { timer = Simple_Word_Enum.new_timer false, report = false }
        (filter_del_word_conversion, 8, Binding.name "broken_kind", SOME "BrokenKind",
         [(Binding.name "BK_A", "1"), (Binding.name "BK_B", "2")])
        (Named_Target.theory_init @{theory})) ()
    val msg =
      case attempt of
        Exn.Res _ => error "expected urust_conversion to fail without word_conversion, \
                           \but the declaration succeeded"
      | Exn.Exn e => Runtime.exn_message e
    (* The message must name the missing constant, blame word_conversion not running, and say
       what to do about it. *)
    fun must s = @{assert} (String.isSubstring s msg)
    val _ = must "broken_kind_to_u8_pure"
    val _ = must "word_conversion plugin apparently did not run"
    val _ = must "disable urust_conversion"
    val _ = must "plugins del: word_conversion urust_conversion"
  in
    writeln ("del: word_conversion alone correctly rejected. Message:\n" ^ msg)
  end
\<close>

(*<*)
end
(*>*)
