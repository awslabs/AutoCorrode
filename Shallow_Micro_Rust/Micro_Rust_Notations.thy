(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Table-backed registry of uRust name notations + a typed dispatcher.

   This is the sole mechanism for registering a uRust name with a HOL
   backend, via the `micro_rust_notation` command. It replaces an older
   approach based on per-name `translations` and per-operator
   `adhoc_overloading` consts emitted by a family of per-kind commands. The
   registry is a single string-indexed `Generic_Data` table; dispatch is a single
   `String.literal`-parametrized const `urust_dispatch` whose markers are
   resolved in a typed `term_check` phase, in adhoc-overloading style. *)

theory Micro_Rust_Notations
  imports
    Main
  keywords
    "micro_rust_notation" :: thy_decl and
    "print_micro_rust_notations" :: diag
begin

(* ===================================================================== *)
(* uRust-name -> HOL-term registry, consulted by the dispatch term_check  *)
(* phase on identifier resolution.  Three contexts (literal/field/        *)
(* function); a name registered only as `field` must still fall back to   *)
(* identity in value position, so we key by (context, name).              *)
(* ===================================================================== *)

ML\<open>
structure Micro_Rust_Names = struct

\<comment>\<open>The three registration contexts (\<open>"literal"\<close> / \<open>"field"\<close> /
  \<open>"function"\<close>), selected by the optional \<open>micro_rust_notation\<close> kind
  modifier (\<open>(literal)\<close> / \<open>(field)\<close> / \<open>(call)\<close>) or inferred from the
  term's type when the modifier is omitted.\<close>
datatype ctxt_kind = NLiteral | NFunction | NField;

fun kind_to_string NLiteral = "literal"
  | kind_to_string NFunction = "function"
  | kind_to_string NField = "field";

fun string_to_kind "literal" = NLiteral
  | string_to_kind "function" = NFunction
  | string_to_kind "field" = NField
  | string_to_kind s = error ("unknown micro_rust_notation context: " ^ s);

\<comment>\<open>Sniff the registration kind from a HOL term's type --- a function call
  iff the type is \<open>_ \<Rightarrow> _ function_body\<close>, a field iff the type is \<open>_ lens\<close>,
  otherwise a literal. Shared by the auto-inferred-kind path of
  \<open>micro_rust_notation\<close> and by the shadow check (which only flags
  call-/field-shaped HOL constants as ambiguous shadows).\<close>
\<comment>\<open>Recognise the type by looking at its outermost shape:
   - any \<open>_ \<Rightarrow> ... \<Rightarrow> _ function_body\<close> chain (uncurried calls have a
     binary or higher \<open>function_body\<close> result) is a function backend;
   - any \<open>_ lens\<close> is a field backend;
   - everything else is a literal.

  The \<open>fun\<close>-walk handles multi-argument functions like
  \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, nat, _, _, _) function_body\<close> --- without it the
  binary signature would collapse to literal at auto-infer time and a
  use site \<open>foo(x, y)\<close> would never reach the function-kind table.\<close>
fun infer_kind_of_type (Type ("Core_Expression.function_body", _)) = NFunction
  | infer_kind_of_type (Type ("fun", [_, T])) = infer_kind_of_type T
  | infer_kind_of_type (Type ("Lens.lens", _)) = NField
  | infer_kind_of_type _ = NLiteral;

\<comment>\<open>A registered entry: the resolved HOL \<^emph>\<open>term\<close> the notation stands for,
  the position of the registering command (so leaf markup can hyperlink to
  the declaration site), and a unique \<open>serial\<close> that pairs the def-side
  markup at the registration site with ref-side markup at every use site
  (mirrors the \<open>def\<close>/\<open>ref\<close> protocol of \<^ML>\<open>Position.make_entity_markup\<close>;
  see e.g. \<open>Pure/Isar/calculation.ML\<close> for a textbook use). Storing a TERM
  (not just a constant name) is what lets a notation target an arbitrary
  expression --- in particular a locale-fixed parameter (a \<open>Free\<close>) or a
  local definition --- not only a global constant. The declaration
  morphism is applied to this term at registration (see \<open>do_register\<close>),
  so under locale interpretation / derivation the stored term tracks the
  parameter substitution.\<close>
type entry = { hol_term : term, reg_pos : Position.T, serial : serial };

\<comment>\<open>MULTIPLE BACKENDS PER NAME (adhoc-overloading-style dispatch). A single
  uRust name may have several HOL backends differing only by type, just as
  the existing code base does manually via an uninterpreted const +
  \<open>adhoc_overloading\<close>. We therefore store a LIST of entries per
  \<open>(kind, name)\<close>, and merge tables by UNION (\<open>Symtab.merge_list\<close>) ---
  exactly as \<open>adhoc_overloading.ML\<close>'s variant table does. This makes the
  registry MERGE-STABLE: if two theories independently register a backend
  for the same name, importing both yields the union of backends, no
  collision and no "last-write-wins" loss. (Resolution to a single backend
  happens later, in a typed \<open>term_check\<close> phase --- see \<open>urust_dispatch\<close>
  below --- because the parse phase runs pre-type and cannot itself choose
  by type.)

  \<open>reg_eq\<close> dedupes entries by their term (position-erased), so
  re-registering the same backend is idempotent (e.g. when a syntax
  declaration is replayed on context-open).\<close>
fun reg_eq (e1 : entry, e2 : entry) =
  Term.aconv_untyped (#hol_term e1, #hol_term e2);

\<comment>\<open>Table keyed by (context, rust_name) \<rightarrow> list of entries. The key is the
  pair of strings (Position.T is not an ord type); entries (term + reg
  position) ride in the value.\<close>
structure Data = Generic_Data
(
  type T = entry list Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge_list reg_eq;
);

fun mk_key kind name = kind_to_string kind ^ "\000" ^ name;

\<comment>\<open>Markup kind for uRust notation entities (def/ref protocol).\<close>
val notationN = "micro_rust_notation";

\<comment>\<open>Shadow-check opt-out state. \<open>shadow_opts\<close> records two independent
  bits; the table tracks a \<^emph>\<open>default\<close> (concrete, applies to every name)
  plus per-(kind, name) overrides whose bits are \<open>bool option\<close>: a
  \<open>SOME\<close>-bit replaces the default for that bit, a \<open>NONE\<close>-bit inherits.
  The four user-facing modes each set exactly one override bit
  (see \<open>set_shadow_bit\<close> below).\<close>
type shadow_opts = { suppress_warning : bool, suppress_error : bool };
type shadow_opts_override =
  { suppress_warning : bool option, suppress_error : bool option };

\<comment>\<open>Default: errors are suppressed; the check still fires as a warning
  unless \<open>suppress_warning\<close> is also on.\<close>
val default_shadow_opts : shadow_opts =
  { suppress_warning = false, suppress_error = true };

val no_override : shadow_opts_override =
  { suppress_warning = NONE, suppress_error = NONE };

\<comment>\<open>Combine two defaults (OR each bit) for merging tables across imports:
  if either source said "suppress this bit", the merged default
  preserves the suppression.\<close>
fun merge_shadow_opts ({ suppress_warning = a1, suppress_error = b1 },
                       { suppress_warning = a2, suppress_error = b2 })
      : shadow_opts =
  { suppress_warning = a1 orelse a2, suppress_error = b1 orelse b2 };

\<comment>\<open>Combine two overrides per bit: \<open>NONE\<close> is identity; two \<open>SOME\<close>s OR
  (the more-suppressing setting wins, mirroring \<open>merge_shadow_opts\<close>).\<close>
fun merge_opt (NONE, x) = x
  | merge_opt (x, NONE) = x
  | merge_opt (SOME a, SOME b) = SOME (a orelse b);

fun merge_shadow_overrides ({ suppress_warning = a1, suppress_error = b1 },
                            { suppress_warning = a2, suppress_error = b2 })
      : shadow_opts_override =
  { suppress_warning = merge_opt (a1, a2),
    suppress_error = merge_opt (b1, b2) };

\<comment>\<open>The four single-bit setters: each updates one field of an existing
  override and leaves the other untouched.\<close>
datatype shadow_bit =
    Set_Suppress_Warning of bool
  | Set_Suppress_Error of bool;

fun apply_shadow_bit (Set_Suppress_Warning b)
                     ({ suppress_error, ... } : shadow_opts_override) =
      { suppress_warning = SOME b, suppress_error = suppress_error }
  | apply_shadow_bit (Set_Suppress_Error b)
                     ({ suppress_warning, ... } : shadow_opts_override) =
      { suppress_warning = suppress_warning, suppress_error = SOME b };

\<comment>\<open>Same setter, but applied to a concrete (non-optional) default
  \<open>shadow_opts\<close>: the bit value is forced (the override is collapsed
  into the default).\<close>
fun apply_shadow_bit_default (Set_Suppress_Warning b)
                             ({ suppress_error, ... } : shadow_opts) =
      { suppress_warning = b, suppress_error = suppress_error }
  | apply_shadow_bit_default (Set_Suppress_Error b)
                             ({ suppress_warning, ... } : shadow_opts) =
      { suppress_warning = suppress_warning, suppress_error = b };

\<comment>\<open>Storage: a concrete default plus a per-(kind, name) override table.
  Default-merge ORs each bit; per-name override merge ORs each \<open>SOME\<close>
  bit and treats \<open>NONE\<close> as identity.\<close>
type shadow_opts_state =
  { default : shadow_opts, per_name : shadow_opts_override Symtab.table };

val empty_shadow_opts_state : shadow_opts_state =
  { default = default_shadow_opts, per_name = Symtab.empty };

fun merge_shadow_opts_state
      ({ default = d1, per_name = p1 },
       { default = d2, per_name = p2 }) : shadow_opts_state =
  { default = merge_shadow_opts (d1, d2),
    per_name = Symtab.join (K merge_shadow_overrides) (p1, p2) };

structure ShadowOpts = Generic_Data
(
  type T = shadow_opts_state;
  val empty = empty_shadow_opts_state;
  val merge = merge_shadow_opts_state;
);

\<comment>\<open>Effective opts for a given \<open>(kind, name)\<close>: per-bit, the override's
  \<open>SOME\<close> value replaces the default, \<open>NONE\<close> inherits. So a default of
  \<open>suppress_error = true\<close> can be re-opened per name via
  \<open>[shadow_err] "foo"\<close>, and vice versa.\<close>
fun shadow_opts ctxt kind name =
  let
    val { default, per_name } = ShadowOpts.get (Context.Proof ctxt)
    fun resolve (NONE, d) = d | resolve (SOME b, _) = b
  in
    case Symtab.lookup per_name (mk_key kind name) of
      NONE => default
    | SOME ov =>
        { suppress_warning =
            resolve (#suppress_warning ov, #suppress_warning default),
          suppress_error =
            resolve (#suppress_error ov, #suppress_error default) }
  end;

\<comment>\<open>Set one shadow bit on the default opts (when \<open>names = []\<close>) or on
  each \<open>(kind, name)\<close> override (when \<open>names\<close> is non-empty).
  Only the named bit is changed; the other bit is preserved.\<close>
fun set_shadow_bit kind names bit =
  if null names then
    ShadowOpts.map (fn { default, per_name } =>
      { default = apply_shadow_bit_default bit default, per_name = per_name })
  else
    let
      fun update_entry (state as { default, per_name }) name =
        let
          val key = mk_key kind name
          val old = the_default no_override (Symtab.lookup per_name key)
          val new = apply_shadow_bit bit old
        in
          { default = default, per_name = Symtab.update (key, new) per_name }
        end
    in
      ShadowOpts.map (fn state => fold (fn n => fn s => update_entry s n) names state)
    end;

\<comment>\<open>Register \<open>rust_name\<close> (in context \<open>kind\<close>) as a notation backend for
  \<open>hol_term\<close>, recording \<open>reg_pos\<close>. CONSes onto the name's backend list
  (deduped by \<open>reg_eq\<close>), so distinct backends accumulate while identical
  re-registration is a no-op.

  Allocates a fresh \<open>serial\<close> per \<^emph>\<open>declaration\<close> (not per merge-replay) and
  emits a \<open>def\<close>-side entity markup at \<open>reg_pos\<close>. Use sites later emit
  matching \<open>ref\<close>-side markup pointing back here, so jEdit's
  jump-to-definition lands on the registering command.\<close>
fun register kind name hol_term reg_pos context =
  let
    val s = serial ();
    val entry = { hol_term = hol_term, reg_pos = reg_pos, serial = s };
    val ctxt = Context.proof_of context;
    val _ = Context_Position.report ctxt reg_pos
      (Position.make_entity_markup {def = true} s notationN (name, reg_pos));
  in
    context |> Data.map (Symtab.insert_list reg_eq (mk_key kind name, entry))
  end;

\<comment>\<open>All backends registered for a \<open>(kind, name)\<close>, or \<open>[]\<close> if none.\<close>
fun lookups ctxt kind name =
  the_default [] (Symtab.lookup (Data.get (Context.Proof ctxt)) (mk_key kind name));

\<comment>\<open>All registered entries, as (kind, rust_name, entry) triples (for the
  query command). Splits the composite key back into kind + name; one row
  per backend.\<close>
fun dump ctxt =
  Data.get (Context.Proof ctxt)
  |> Symtab.dest
  |> maps (fn (key, es) =>
       (case String.fields (fn ch => ch = #"\000") key of
          [k, n] => map (fn e => (string_to_kind k, n, e)) es
        | _ => error "malformed micro_rust_notation key"));

end
\<close>

(* ===================================================================== *)
(* Type-directed dispatch for multi-backend notations.                    *)
(*                                                                        *)
(* When a uRust name has >1 backend, the parse phase cannot choose       *)
(* (types are not yet known).  Instead it emits a marker                  *)
(* `urust_dispatch (STR ''<kind>:<name>'')`; a `term_check` phase runs   *)
(* AFTER type inference and resolves the marker to the unique backend    *)
(* whose type unifies with the occurrence.                                *)
(*                                                                        *)
(*   0 candidates  \<rightarrow>  "no backend at type"                              *)
(*   1 candidate   \<rightarrow>  splice it                                         *)
(*   \<ge>2 candidates \<rightarrow>  ambiguous (loud, listing all candidates)          *)
(*                                                                        *)
(* Same loud-on-ambiguity discipline as `adhoc_overloading` (never        *)
(* "last wins").  `urust_dispatch` is one global anchor (merge-stable);   *)
(* per-name identities are STRING tags reconciled by the union-merged     *)
(* `Micro_Rust_Names` table.                                              *)
(* ===================================================================== *)

\<comment>\<open>Plain-identifier dispatch carries a \<^emph>\<open>witness\<close> --- the bare \<^verbatim>\<open>Free name\<close>
  that the source identifier would have been if no notation registration
  existed. The witness travels through HOL's normal binding pipeline, so
  by term_check time it has been resolved by Isabelle the same way an
  unmarked occurrence would be (\<^verbatim>\<open>Bound\<close> for \<open>\<lambda>\<close>-bound, \<^verbatim>\<open>Const\<close> for an
  in-scope HOL constant of the same name, \<^verbatim>\<open>Free\<close> for a truly-free
  occurrence). The dispatcher's resolver then prefers the witness over
  the table whenever the witness has bound or constant shape --- this is
  what stops a registered \<^verbatim>\<open>("mask")\<close> from hijacking a
  \<^verbatim>\<open>\<lambda>mask. \<dots> mask \<dots>\<close> use site.

  Path identifiers (\<^verbatim>\<open>Foo::Bar\<close>) cannot be HOL binders, so they have
  no useful witness and use a separate marker.\<close>
\<comment>\<open>Bespoke witness wrapper: a private datatype with two constructors,
  used solely to carry the optional witness inside the dispatch marker.
  Going through a dedicated wrapper rather than HOL's \<^typ>\<open>'a option\<close>
  prevents accidental collision with notation registrations of \<open>Some\<close>,
  \<open>None\<close>, etc. (\<open>Some(x)\<close> at function position has the witness
  \<open>Some\<close> --- which would itself be elaborated by HOL to
  \<^const>\<open>Option.Some\<close> if we used \<^typ>\<open>'a option\<close> as the wrapper, and
  HOL's type inference would then conflate the wrapper-\<open>Some\<close> with the
  witness-\<open>Some\<close>.)\<close>
datatype 'a urust_witness = Witness 'a | NoWitness

\<comment>\<open>The dispatch marker carries a payload term \<open>'x\<close> (an opaque
  carrier for kind/name/source-pos metadata, built in ML by
  \<open>Micro_Rust_Dispatch.mk_payload\<close>) and an optional witness
  \<open>'y urust_witness\<close>. The result type \<open>'z\<close> is independent so
  the marker's elaboration doesn't get pinned by the witness or
  payload types.\<close>
consts urust_dispatch :: \<open>'x \<Rightarrow> 'y urust_witness \<Rightarrow> 'z\<close>

ML\<open>
structure Micro_Rust_Dispatch = struct

\<comment>\<open>The marker's payload encodes \<open>(kind, name, source_pos)\<close> as a
  bare \<^verbatim>\<open>Const\<close> with the data packed into the constant's name.
  Using a \<^verbatim>\<open>Const\<close> rather than a HOL \<^typ>\<open>String.literal\<close> avoids the
  ~7n nested-constructor blowup of bit-list literal strings; the
  payload is two heap cells regardless of name length. The sentinel
  prefix keeps the encoded name out of any real namespace.\<close>
val payload_prefix = "_urust_dispatch_payload___";
val payload_sep = String.str (Char.chr 0);

\<comment>\<open>Drop the \<^verbatim>\<open>file\<close> property of a position. CRITICAL: the encoded
  position is spliced into the payload \<^verbatim>\<open>Free\<close>'s \<^emph>\<open>name\<close> (see
  \<open>mk_payload\<close>), and a file path contains \<open>.\<close> characters. A \<open>.\<close> in a
  name makes \<^ML>\<open>Long_Name.is_qualified\<close> true, which makes
  \<^ML>\<open>Proof_Context.lookup_free\<close> return \<^verbatim>\<open>NONE\<close>, which makes
  \<^ML>\<open>Syntax_Phases.decode_term\<close> promote the \<^verbatim>\<open>Free\<close> to a constant
  lookup --- raising "Undefined constant" at parse time. This bites
  \<^emph>\<open>only\<close> in batch builds: interactive PIDE term evaluation yields
  positions without a \<open>file\<close> property, so the bug stays latent in jEdit
  and surfaces under \<^verbatim>\<open>isabelle build\<close>. Markup keys on \<open>offset\<close>+\<open>id\<close>
  (see \<^ML>\<open>Position.is_reported\<close>), which survive, so dropping the file
  is invisible to the use-site report.\<close>
fun strip_file pos =
  let val {line, offset, end_offset, props = {label, id, ...}} = Position.dest pos
  in Position.make {line = line, offset = offset, end_offset = end_offset,
       props = {label = label, file = "", id = id}} end;

fun encode_payload kind name pos =
  let
    val tag = Micro_Rust_Names.kind_to_string kind ^ payload_sep ^ name
  in
    if Position.is_reported pos
    then tag ^ payload_sep ^ Term_Position.encode_no_syntax [strip_file pos]
    else tag
  end;

fun decode_payload s =
  let
    val parts = String.fields (fn ch => ch = Char.chr 0) s
    val (kind_str, name, pos) =
      (case parts of
         [k, n] => (k, n, Position.none)
       | [k, n, enc] =>
           (k, n,
            case Term_Position.decode enc of
              {pos, ...} :: _ => pos
            | [] => Position.none)
       | _ => error "malformed urust_dispatch payload")
  in (Micro_Rust_Names.string_to_kind kind_str, name, pos) end;

\<comment>\<open>Build the payload \<^verbatim>\<open>Free\<close> with the encoded data in its name.

  Using \<^verbatim>\<open>Free\<close> rather than \<^verbatim>\<open>Const\<close> matters: the preterm decoder runs
  a namespace lookup on \<^verbatim>\<open>Const\<close> names and raises "Undefined constant"
  when the name doesn't resolve. \<^verbatim>\<open>Free\<close> variables aren't subject to
  that lookup; the decoder accepts the free variable verbatim. The
  sentinel prefix is reserved enough that no user identifier could
  collide with it.\<close>
fun mk_payload kind name pos =
  Free (payload_prefix ^ encode_payload kind name pos, dummyT);

\<comment>\<open>Recognise the payload \<^verbatim>\<open>Free\<close> and recover \<open>(kind, name, pos)\<close>.\<close>
fun dest_payload (Free (s, _)) =
      if String.isPrefix payload_prefix s
      then SOME (decode_payload (String.extract (s, size payload_prefix, NONE)))
      else NONE
  | dest_payload _ = NONE;

\<comment>\<open>Construct a marker \<open>urust_dispatch (STR ''<tag>'') opt\<close>:

   - Plain id: \<open>opt = SOME witness\<close>, where \<open>witness\<close> is the bare
     \<open>Free name\<close> the source identifier would have parsed to. HOL
     elaboration resolves the witness through normal binding (so a
     \<lambda>-bound \<open>name\<close> becomes \<open>Bound n\<close>, an in-scope HOL constant becomes
     \<open>Const\<close>, etc.); the term_check resolver inspects the elaborated
     witness and prefers it over a table lookup whenever the witness
     resolved to a binder or a HOL constant.

   - Path id: \<open>opt = NONE\<close>. Path names cannot be HOL binders, so there
     is no useful witness to carry.

  The two type variables \<open>'a\<close> (witness) and \<open>'b\<close> (result) are
  independent --- this is essential. If they were collapsed, the
  witness's elaborated type would force the marker's result type, and a
  registered name like \<open>Some\<close> (which HOL elaborates to
  \<^const>\<open>Option.Some\<close>) at function position would fail type unification
  before the term_check resolver had a chance to pick the registered
  function-kind backend.\<close>
fun mk_marker_term opt_witness =
  let
    val opt_term =
      (case opt_witness of
         SOME w => Const (\<^const_name>\<open>Witness\<close>, dummyT) $ w
       | NONE => Const (\<^const_name>\<open>NoWitness\<close>, dummyT))
  in fn payload =>
       Const (\<^const_name>\<open>urust_dispatch\<close>, dummyT) $ payload $ opt_term
  end;

\<comment>\<open>Build the marker with the witness term unmodified --- positions
  on the witness are preserved. After \<^ML>\<open>Syntax_Trans.abs_tr\<close>
  binds an enclosing same-named binder, the witness becomes
  \<^verbatim>\<open>_constrain $ Bound n $ <pos>\<close>, and \<^verbatim>\<open>decode_term\<close> emits paired
  binder def/use markup automatically.

  The trade-off: when the witness elaborates to a HOL constant
  (e.g. \<^verbatim>\<open>Free "Some"\<close> \<rightsquigarrow> \<^const>\<open>Option.Some\<close>), the decoder ALSO
  emits \<^verbatim>\<open>Markup.const\<close> at the user's source token, which can stack
  visibly with the \<open>micro_rust_notation\<close> entity ref \<open>resolve\<close> emits.\<close>
fun mk_marker kind name pos witness =
  mk_marker_term (SOME witness) (mk_payload kind name pos);

\<comment>\<open>Recognise a marker. Returns \<open>SOME ((kind, name, src_pos),
  opt_witness, T)\<close> where \<open>opt_witness\<close> is \<open>SOME witness\<close> for plain ids
  (the elaborated witness term) and \<open>NONE\<close> for paths, and \<open>T\<close> is the
  marker's inferred result type at this occurrence.\<close>
\<comment>\<open>Type-aware destructure: requires the marker's outer type to be a
  proper function chain so we can extract the result type. Returns
  \<open>NONE\<close> on a malformed payload, on a non-witness opt-payload, or
  when the marker's type is still \<open>dummyT\<close>-shaped (i.e. before type
  inference); callers in early phases should use
  \<^verbatim>\<open>dest_marker_untyped\<close> instead.\<close>
fun dest_marker (Const (\<^const_name>\<open>urust_dispatch\<close>, T) $ payload $ opt) =
      ((case dest_payload payload of
          NONE => NONE
        | SOME tag =>
            let
              val result_T = Term.range_type (Term.range_type T)
              val witness =
                (case opt of
                   Const (\<^const_name>\<open>Witness\<close>, _) $ w => SOME w
                 | Const (\<^const_name>\<open>NoWitness\<close>, _) => NONE
                 | _ => raise Match)
            in SOME (tag, witness, result_T) end)
       handle Match => NONE | TYPE _ => NONE)
  | dest_marker _ = NONE;

\<comment>\<open>Type-blind destructure: only inspects the term skeleton (payload
  and witness shape). Used in the early \<^verbatim>\<open>~1\<close> phase, before type
  inference, where the marker's type is still \<open>dummyT\<close> and
  \<^verbatim>\<open>dest_marker\<close> would bail out.\<close>
fun dest_marker_untyped (Const (\<^const_name>\<open>urust_dispatch\<close>, _) $ payload $ opt) =
      ((case dest_payload payload of
          NONE => NONE
        | SOME tag =>
            let
              val witness =
                (case opt of
                   Const (\<^const_name>\<open>Witness\<close>, _) $ w => SOME w
                 | Const (\<^const_name>\<open>NoWitness\<close>, _) => NONE
                 | _ => raise Match)
            in SOME (tag, witness) end)
       handle Match => NONE)
  | dest_marker_untyped _ = NONE;

\<comment>\<open>Can backend type \<open>T'\<close> serve an occurrence of type \<open>T\<close>?
  (Mirrors \<open>adhoc_overloading.ML\<close>: rename the backend's tvars away
  from the occurrence and try \<open>typ_unify\<close>.)\<close>
fun unifiable_types ctxt (T, T') =
  let
    val thy = Proof_Context.theory_of ctxt;
    val maxidx1 = Term.maxidx_of_typ T;
    val T'' = Logic.incr_tvar (maxidx1 + 1) T';
    val maxidx2 = Term.maxidx_typ T'' maxidx1;
  in can (Sign.typ_unify thy (T, T'')) (Vartab.empty, maxidx2) end;

\<comment>\<open>Try to unify a backend term against an occurrence type \<open>T\<close>; on
  success, return the backend term with its schematic TVars
  instantiated by the unifier. Mirrors the shift-and-unify dance of
  \<open>unifiable_types\<close> but also \<^emph>\<open>applies the substitution\<close> so the
  resulting term has no orphan schematics --- otherwise \<open>check_term\<close>'s
  later "Illegal schematic type variable" guard fires.\<close>
fun unify_and_instantiate ctxt T t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val T' = fastype_of t;
    val maxidx1 = Term.maxidx_of_typ T;
    val shift = maxidx1 + 1;
    val T'' = Logic.incr_tvar shift T';
    val t' = Term.map_types (Logic.incr_tvar shift) t;
    val maxidx2 = Term.maxidx_typ T'' maxidx1;
  in
    case try (Sign.typ_unify thy (T, T'')) (Vartab.empty, maxidx2) of
      NONE => NONE
    | SOME (tyenv, _) =>
        let
          val subst = Term.map_types (Envir.subst_type tyenv)
        in SOME (subst t') end
  end;

\<comment>\<open>Candidate backends for \<open>(kind, name)\<close> whose type unifies with \<open>T\<close>.
  Each backend term is freshly \<^emph>\<open>polymorphised\<close> (its \<open>TFree\<close>s are generalised
  to schematic \<open>TVar\<close>s) and then imported with fresh schematic indices ---
  this is the same dance \<open>adhoc_overloading\<close>'s variant table does, and is
  what lets a registered term whose declared type is \<open>'a \<Rightarrow> 'a option\<close>
  match an occurrence whose inferred type is \<open>nat \<Rightarrow> nat option\<close>.
  Skipping the polymorphisation leaves \<open>TFree\<close>s in the backend, which
  do not unify with the occurrence's schematic Vars and cause spurious
  "no backend matches type" errors.\<close>
\<comment>\<open>Generalise a backend's free type variables to schematics, leaving
  any pre-existing schematics untouched. Distinct from
  \<open>Logic.varify_types_global\<close>, which raises on pre-existing schematics
  --- the registered backend may legitimately contain both
  (e.g. \<open>lift_fun1 Some\<close>: \<open>lift_fun1\<close>'s tvars are TFree but the inlined
  \<open>Some\<close> has TVar from its declared signature).\<close>
fun varify_tfrees_in_term t =
  Term.map_types (Term.map_atyps
    (fn TFree (a, S) => TVar ((a, 0), S) | T => T)) t;

fun candidates ctxt kind name T =
  Micro_Rust_Names.lookups ctxt kind name
  |> map_filter (fn { hol_term, ... } =>
       \<comment>\<open>Mirror \<open>adhoc_overloading.ML\<close>: keep the backend's type for
         the unifiability check, but splice the term with all internal
         types erased to \<open>dummyT\<close> --- subsequent type inference re-checks
         the spliced term against \<open>T\<close> and fills in dummies, which lets
         residual polymorphism flow naturally and avoids "Illegal
         schematic type variable" reports for tvars that the surrounding
         context can still pin.\<close>
       let val varified = varify_tfrees_in_term hol_term
       in
         if unifiable_types ctxt (T, fastype_of varified)
         then SOME (Type.constraint T (Term.map_types (K dummyT) varified))
         else NONE
       end);

\<comment>\<open>Look up a HOL constant by user-visible name. Returns
  \<open>SOME (full_name, declared_type)\<close> if the name resolves to a proper
  constant in \<open>ctxt\<close>, \<open>NONE\<close> otherwise (free variable, abbreviation,
  unknown name, etc.). Used by \<open>shadow_check\<close> below.\<close>
fun lookup_hol_const ctxt name =
  (case try (Proof_Context.read_const {proper = true, strict = false} ctxt) name of
     SOME (Const (full_name, T)) => SOME (full_name, T)
   | _ => NONE);

\<comment>\<open>If a \<^emph>\<open>registered\<close> uRust notation \<open>name\<close> shares its name with an
  \<^emph>\<open>unregistered\<close> HOL constant in scope whose type has matching kind
  (call-position vs \<open>_ \<Rightarrow> _ function_body\<close>, or field-position vs
  \<open>_ lens\<close>), surface it as a shadow:

   - by default, errors are suppressed (\<open>suppress_error\<close>) and the
     shadow is reported at warning level only;
   - per-name \<open>[shadow_err]\<close> re-enables the error;
   - per-name \<open>[shadow_no_warn]\<close> silences the warning too.

  Literal-position uses are never shadow-checked --- shadowing on bare
  values produces too much noise (e.g. \<^const>\<open>Some\<close> at \<open>'a \<Rightarrow> 'a option\<close>
  would shadow every uRust \<^verbatim>\<open>Some\<close> use without any real ambiguity).
  Cross-kind clashes are likewise ignored (a call-shaped HOL constant
  is unrelated to a field-position uRust use of the same name, and
  vice versa).

  Only fires when there is at least one registered backend that unifies;
  if dispatch has nothing to say, shadowing is irrelevant.\<close>
fun shadow_check ctxt kind name T pos have_backend =
  if not have_backend then () else
  if kind = Micro_Rust_Names.NLiteral then () else
  let val { suppress_warning, suppress_error } =
        Micro_Rust_Names.shadow_opts ctxt kind name
  in
  (case lookup_hol_const ctxt name of
    NONE => ()
  | SOME (full_name, const_T) =>
      if Micro_Rust_Names.infer_kind_of_type const_T <> kind then ()
      else
        let
          \<comment>\<open>Render the constant via \<^ML>\<open>Syntax.pretty_term\<close> so name-space markup
            (\<^verbatim>\<open>Name_Space.markup\<close> + \<^verbatim>\<open>Markup.const\<close>) is attached and ctrl-click
            jumps to the defining \<^verbatim>\<open>definition\<close>/\<^verbatim>\<open>fun\<close>/\<^verbatim>\<open>primrec\<close> command.\<close>
          val pretty_const = Syntax.pretty_term ctxt (Const (full_name, const_T))
          val msg = Pretty.string_of (Pretty.chunks
            [Pretty.str ("Ambiguous uRust notation \<open>" ^ name ^
               "\<close>: a registered backend matches type"),
             Pretty.block [Pretty.str "  ", Syntax.pretty_typ ctxt T],
             Pretty.block
               [Pretty.str "but the HOL constant ", pretty_const,
                Pretty.str " of type"],
             Pretty.block [Pretty.str "  ", Syntax.pretty_typ ctxt const_T],
             Pretty.str "also matches.",
             Pretty.str ("Either rename the registered backend or pick a different rust_name,"),
             Pretty.str ((if suppress_error then
                            "or run \<open>micro_rust_notation (config) [shadow_no_warn] \""
                              ^ name ^ "\"\<close> to silence."
                          else
                            "or run \<open>micro_rust_notation (config) [shadow_no_err] \""
                              ^ name ^ "\"\<close>.")
                         ^ Position.here pos)])
        in
          if not suppress_error then error msg
          else if not suppress_warning then warning msg
          else ()
        end)
  end;

\<comment>\<open>Should the elaborated witness shadow the table registration? Only in
  one case: a \<^bold>\<open>literal\<close>-position occurrence (bare \<open>x\<close>) whose witness is a
  \<^verbatim>\<open>Bound\<close> --- i.e. a \<open>let\<close>/\<lambda>-bound local, which correctly wins, mirroring
  Rust's lexical scoping (\<open>let x = \<dots>; x\<close>).

  In \<^bold>\<open>field\<close> (\<open>x.f\<close>) and \<^bold>\<open>function\<close> (\<open>f(\<dots>)\<close> / \<open>x.f(\<dots>)\<close>) positions the name
  is a selector/callee that can never be a local binder, so a registered
  notation \<^emph>\<open>always\<close> wins: e.g. the field selector \<open>.f\<close> in \<open>x.f\<close> must not be
  shadowed by a same-named closure parameter \<open>|f| \<dots>\<close>, and a method call
  \<open>x.f(f)\<close> must invoke the \<open>.f\<close> method even when the argument \<open>f\<close> is a
  same-named local binder. (Trade-off: a locally-bound callable
  \<open>let f = \<dots>; f(\<dots>)\<close> can no longer shadow a registered function notation;
  uRust does not rely on that.)

  \<^verbatim>\<open>Const\<close> witnesses never win either, since a backend is often registered
  precisely to override a same-named HOL constant (e.g. \<^verbatim>\<open>("Some")\<close> for
  \<^verbatim>\<open>lift_fun1 Some\<close>, where the witness \<^verbatim>\<open>Free "Some"\<close> elaborates to
  \<^const>\<open>Option.Some\<close>).\<close>
fun witness_takes_precedence Micro_Rust_Names.NLiteral (Bound _) = true
  | witness_takes_precedence _ _ = false;

\<comment>\<open>Resolve all dispatch markers in a term, in the typed check phase.
  The marker has shape \<open>urust_dispatch (STR ''<tag>'') opt\<close> where \<open>opt\<close>
  is either \<open>Some witness\<close> (plain id; HOL elaboration has resolved the
  witness to \<open>Bound\<close>/\<open>Const\<close>/\<open>Free\<close> through normal binding) or \<open>None\<close>
  (path id; no witness available).

  Resolution rules (\<lambda>-binders already consumed at stage \<^verbatim>\<open>~1\<close> by
  \<open>resolve_bound\<close>, so any surviving witness here is \<open>Free\<close>/\<open>Const\<close>):
   - exactly 1 type-compatible candidate \<Rightarrow> splice it in (+ use-site markup);
   - \<ge>2 candidates \<Rightarrow> ambiguous: leave the marker for \<open>reject_unresolved\<close>;
   - 0 candidates \<Rightarrow> the name IS registered (a marker would not exist
     otherwise) but no backend type-unifies with the occurrence \<Rightarrow>
     \<open>no_match_error\<close> (a hard error; see there). We do NOT silently demote
     to the witness free variable --- that would mask genuine arity/type
     mismatches like \<open>Foo::mk()\<close> against a binary backend.\<close>
\<comment>\<open>Early phase, runs at stage \<^verbatim>\<open>~1\<close> before type inference. Replaces a
  marker with its witness ONLY if the witness is a \<^verbatim>\<open>Bound\<close> --- meaning
  the surrounding \<open>_abs\<close> machinery has already resolved a \<lambda>-binder of
  the same name. This must happen before \<open>adhoc_overloading\<close> runs (at
  stage 0), so that \<lambda>-bound uses don't leave a polymorphic marker
  behind that breaks operator resolution.

  Uses \<^verbatim>\<open>dest_marker_untyped\<close> --- at this stage the marker's outer
  type is still \<open>dummyT\<close>, so \<^verbatim>\<open>dest_marker\<close> would silently fail.\<close>
\<comment>\<open>When the witness wins (the marker resolves to a \<^verbatim>\<open>Bound\<close>), we
  also need to emit \<^verbatim>\<open>Markup.bound\<close> at the user's source position.
  Without this the use site has no markup at all --- the position
  carried by the user's source token went into the marker's payload
  string (not into a \<open>_constrain\<close> wrapper around the witness, because
  we strip those to suppress the const-promotion leak), so the
  decoder never sees a position-tagged \<open>Bound\<close> to attach binder-use
  markup to. We emit it ourselves from the recovered tag position.\<close>
fun resolve_bound ctxt =
  let
    fun go t =
      (case dest_marker_untyped t of
         SOME ((kind, _, pos), SOME w) =>
           if witness_takes_precedence kind w then
             let val _ = Context_Position.report ctxt pos Markup.bound
             in w end
           else t
       | _ =>
           (case t of
              u $ v => go u $ go v
            | Abs (x, S, b) => Abs (x, S, go b)
            | _ => t));
  in map go end;

\<comment>\<open>Late phase, runs at stage \<^verbatim>\<open>1\<close> after type inference. Markers that
  survived \<^verbatim>\<open>resolve_bound\<close> here have a witness that's NOT a \<lambda>-binder
  (so \<^verbatim>\<open>Free\<close> or \<^verbatim>\<open>Const\<close>), or are path markers (no witness). Now we
  have full types and can do the typed table lookup.\<close>
\<comment>\<open>Emit use-site markup at \<open>pos\<close> for every registered backend under
  \<open>(kind, name)\<close>: an entity ref to the registration site (so ctrl-click
  jumps back to \<open>micro_rust_notation\<close>), plus a \<^verbatim>\<open>Name_Space.markup\<close> +
  \<^verbatim>\<open>Markup.keyword3\<close> chain when the backend itself is a bare constant
  (ctrl-click to its definition, coloured as a keyword). Called by \<open>resolve\<close>
  ONLY when a marker is actually replaced by a registered backend ---
  never when the witness wins. This is what stops the markup from
  leaking onto an identifier whose witness ends up being a \<lambda>-binder
  (e.g. \<open>let x = \<dots>; x\<close> where \<open>x\<close> is also a registered notation: the
  trailing \<open>x\<close> resolves to the let-binder, so no notation markup
  should be attached).\<close>
fun emit_use_markup_at_pos ctxt kind name pos =
  if not (Position.is_reported pos) then ()
  else
    let
      val entries = Micro_Rust_Names.lookups ctxt kind name
      fun report_one ({serial, reg_pos, hol_term} : Micro_Rust_Names.entry) =
        let
          val notation_markup =
            [Position.make_entity_markup {def = false} serial
               Micro_Rust_Names.notationN (name, reg_pos)]
          \<comment>\<open>Walk to the head \<^verbatim>\<open>Const\<close> of the backend so wrapper
            forms like \<^verbatim>\<open>lift_fun1 Some\<close> still get const-styling
            (color + ctrl-click) attached at the use site, not just the
            \<open>micro_rust_notation\<close> entity ref. We use the standard
            \<^verbatim>\<open>Name_Space.markup\<close> (an entity-style markup keyed by the
            constant's def-site serial) for the click target, plus the
            \<^verbatim>\<open>Markup.keyword3\<close> kind tag for the colour face (so
            notation-resolved constants are coloured as keywords rather than
            as ordinary constants).\<close>
          fun head_const t =
            (case Term_Position.strip_positions t of
               Const (c, _) => SOME c
             | u $ _ => head_const u
             | _ => NONE)
          val const_markup =
            (case head_const hol_term of
               SOME c =>
                 [Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) c,
                  Markup.keyword3]
             | NONE => [])
        in
          app (Context_Position.report ctxt pos) (notation_markup @ const_markup)
        end
    in
      app report_one entries
    end;

\<comment>\<open>A marker only exists because \<open>lookup_id_tr\<close> found a registration for
  \<open>(kind, name)\<close> (it emits nothing otherwise). So by the time \<open>resolve\<close>
  runs --- with \<lambda>-binders already consumed by \<open>resolve_bound\<close> at stage
  \<^verbatim>\<open>~1\<close> --- an empty candidate set means the name \<^emph>\<open>is\<close> registered but
  \<^bold>\<open>no backend's type unifies\<close> with the occurrence type \<open>T\<close>. That is a
  genuine error (e.g. \<open>Foo::mk()\<close> --- a no-arg call ---
  against a backend of type \<open>'a \<Rightarrow> 'b \<Rightarrow> _ function_body\<close>),
  not a reason to silently demote the name to a free variable. We report
  it loudly, showing the occurrence type and every registered backend
  with its type, so the arity/type mismatch is obvious.\<close>
fun no_match_error ctxt kind name pos T =
  error (Pretty.string_of (Pretty.chunks
    [Pretty.block [Pretty.str ("uRust notation \<open>" ^ name ^
       "\<close> is registered, but no backend matches the use-site type "),
       Syntax.pretty_typ ctxt T, Pretty.str (Position.here pos)],
     Pretty.big_list "registered backends (none type-compatible here):"
       (map (fn { hol_term, ... } : Micro_Rust_Names.entry =>
               Pretty.block [Syntax.pretty_term ctxt hol_term, Pretty.str " :: ",
                             Syntax.pretty_typ ctxt (fastype_of hol_term)])
          (Micro_Rust_Names.lookups ctxt kind name))]));

fun resolve ctxt =
  let
    fun go t =
      (case dest_marker t of
         SOME ((kind, name, pos), opt_witness, T) =>
           let
             val cands = candidates ctxt kind name T
             val _ = shadow_check ctxt kind name T pos (not (null cands))
             fun emit () = emit_use_markup_at_pos ctxt kind name pos
           in
             (case (opt_witness, cands) of
                (SOME w, _) =>
                  if witness_takes_precedence kind w then w \<comment>\<open>binder wins, no markup\<close>
                  else
                    (case cands of
                       [single] => (emit (); single)
                     | [] => no_match_error ctxt kind name pos T
                     | _ => t \<comment>\<open>ambiguous: leave for reject_unresolved\<close>)
              | (NONE, [single]) => (emit (); single)
              | (NONE, []) => no_match_error ctxt kind name pos T
              | (NONE, _) => t)
           end
       | NONE =>
           (case t of
              u $ v => go u $ go v
            | Abs (x, S, b) => Abs (x, S, go b)
            | _ => t));
  in map go end;

\<comment>\<open>After resolution, any surviving marker is genuinely ambiguous (\<ge>2
  unifying backends); report it loudly, listing the candidates.\<close>
fun reject_unresolved ctxt =
  let
    fun check t =
      (case dest_marker t of
         SOME ((kind, name, pos), _, T) =>
           error (Pretty.string_of (Pretty.chunks
             [Pretty.block [Pretty.str ("Ambiguous uRust notation \<open>" ^ name ^
                "\<close> at type "), Syntax.pretty_typ ctxt T,
                Pretty.str (Position.here pos)],
              Pretty.big_list "candidate backends:"
                (map (Syntax.pretty_term ctxt o #hol_term)
                   (Micro_Rust_Names.lookups ctxt kind name))]))
       | NONE =>
           (case t of u $ v => (check u; check v) | Abs (_, _, b) => check b | _ => ()));
  in app check end;

\<comment>\<open>Install the two check phases (only fire when at least one marker is
  present, so this is free for marker-less terms). Phase 0 resolves; phase
  1 rejects leftover/ambiguous.\<close>
\<comment>\<open>Run at negative priority so we resolve markers \<^emph>\<open>before\<close>
  \<^verbatim>\<open>adhoc_overloading\<close>'s check (which lives at priority 0). Otherwise
  a use site like \<open>shdw + mask\<close> --- where \<open>+\<close> is adhoc-overloaded
  \<^verbatim>\<open>urust_add\<close> --- would fail adhoc resolution before our marker had a
  chance to splice in the registered backend (or fall back to the
  \<lambda>-bound witness), because the marker carries a polymorphic result
  type that adhoc-overloading cannot disambiguate.\<close>
val _ = Context.>>
  (Syntax_Phases.term_check ~1 "urust_dispatch_bind"
     (fn ctxt => resolve_bound ctxt)
   #> Syntax_Phases.term_check 0 "urust_dispatch"
        (fn ctxt => resolve ctxt)
   #> Syntax_Phases.term_check 1 "urust_dispatch_unresolved"
        (fn ctxt => fn ts => (reject_unresolved ctxt ts; ts)));

end
\<close>

(* ===================================================================== *)
(* Outer-syntax command for registering and configuring uRust notations.  *)
(*                                                                        *)
(* Single command, three modifier flavours:                               *)
(*                                                                        *)
(*   micro_rust_notation                <hol_term> ("<rust_name>")        *)
(*     -- kind auto-inferred from the HOL term's type                     *)
(*                                                                        *)
(*   micro_rust_notation (literal)      <hol_term> ("<rust_name>")        *)
(*   micro_rust_notation (call)         <hol_term> ("<rust_name>")        *)
(*   micro_rust_notation (field)        <hol_term> ("<rust_name>")        *)
(*     -- forces the kind; validates the HOL term's type and errors      *)
(*        out if it doesn't fit (call: needs `_ \<Rightarrow> _ function_body`,     *)
(*        field: needs `_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ focus`).                            *)
(*                                                                        *)
(*   micro_rust_notation (config) [<mode>] "name1" "name2" ...            *)
(*     -- shadow-check configuration. Modes:                              *)
(*          shadow_warn / shadow_no_warn / shadow_err / shadow_no_err     *)
(*        (each toggles one bit; the orthogonal bit is preserved.)       *)
(*        Empty name list applies to the global default.                  *)
(*                                                                        *)
(* `print_micro_rust_notations` (separate diag command) lists every       *)
(* registered notation.                                                   *)
(* ===================================================================== *)

ML\<open>
structure Micro_Rust_Notation_Cmd = struct

\<comment>\<open>Validate that a forced kind is consistent with the term's type. Fail
  loudly if not. (Auto-inferred kind never fails this check by
  construction.)\<close>
fun check_forced_kind kind ctxt t =
  let
    val T = fastype_of t
    val inferred = Micro_Rust_Names.infer_kind_of_type T
  in
    if kind = Micro_Rust_Names.NLiteral
      orelse kind = inferred
    then ()
    else
      error (Pretty.string_of (Pretty.chunks
        [Pretty.block [Pretty.str ("micro_rust_notation (" ^
           Micro_Rust_Names.kind_to_string kind ^ "): forced kind does not match\
           \ the registered term's type."),
         Pretty.brk 1, Pretty.str "Term: ", Syntax.pretty_term ctxt t],
         Pretty.block [Pretty.str "Type: ", Syntax.pretty_typ ctxt T]]))
  end;

\<comment>\<open>A rust name is \<^emph>\<open>grammatical\<close> if the µRust frontend's grammar can
  already parse it as a \<^verbatim>\<open>urust_identifier\<close>: either a plain identifier
  (\<open>foo_bar\<close>) or a \<^verbatim>\<open>::\<close>-style path (\<open>Foo::bar::baz\<close>, which the path-AST
  translation flattens). Anything else --- turbofish forms like
  \<open>Address::<IPA>::new\<close>, or macro names like \<open>fatal!\<close> --- contains
  characters (\<open><\<close>, \<open>>\<close>, \<open>!\<close>, \<dots>) that no grammar production covers, so
  the token cannot be parsed at all. For those we must additionally emit
  a bespoke grammar production + AST translation (see
  \<open>emit_bespoke_syntax\<close>): the dispatch-table entry alone is useless if the
  use site never parses.\<close>
fun is_grammatical_name name =
  let val remove_colons = String.translate (fn #":" => "" | c => String.str c)
  in Symbol_Pos.is_identifier name
       orelse Symbol_Pos.is_identifier (remove_colons name)
  end;

\<comment>\<open>For a non-grammatical rust name (turbofish/macro), emit a bespoke
  grammar production so the surface token parses, then funnel it back into
  the \<^emph>\<open>ordinary\<close> identifier pipeline --- exactly as the path frontend does
  for \<open>Foo::bar\<close>. We declare a fresh nullary \<^verbatim>\<open>urust_identifier\<close> constant
  whose mixfix template IS the rust name (so the exact token sequence
  becomes one grammar atom), plus a \<^verbatim>\<open>parse_ast_translation\<close> hook
  rewriting it to \<open>_urust_identifier_id (Ast.Variable <rust_name>)\<close> --- the
  SAME AST node a plain/path identifier yields. From there it flows through
  \<open>lookup_id_tr\<close> and the dispatch table uniformly; the turbofish-ness is
  confined to the AST frontend. The syntax-constant name is a sanitised
  (alphanumeric-only) form of the rust name.

  \<^bold>\<open>Clickability + no overloading.\<close> A \<^verbatim>\<open>syntax_consts\<close> dependency binds
  the bespoke constant to its backend constant, which (a) makes the use
  site ctrl-clickable --- \<^verbatim>\<open>parsetree_to_ast\<close> reports the binding before
  the parse translation fires --- and (b) forces \<^emph>\<open>at most one\<close> backend per
  name (the single production has one \<^verbatim>\<open>syntax_consts\<close> target), so we reject
  a second registration in any kind.

  We therefore need a single backend constant \<open>c\<close>. \<open>Term.head_of t0\<close> gives
  it for a definition/raw constant; for an \<^theory_text>\<open>abbreviation\<close>
  \<^verbatim>\<open>read_term\<close> returns the \<^emph>\<open>expansion\<close> (head \<^verbatim>\<open>Abs\<close>), so we recover \<open>c\<close>
  from the source string via \<^ML>\<open>Proof_Context.read_const\<close> (no unfolding).
  Error only if neither yields a constant.\<close>
fun emit_bespoke_syntax hol_src rust_name t0 lthy =
  if is_grammatical_name rust_name then lthy
  else
    let
      val c =
        (case Term.head_of t0 of
           Const (c, _) => c
         | _ =>
           (case try (Proof_Context.read_const {proper = true, strict = false} lthy) hol_src of
              SOME (Const (c, _)) => c
            | _ =>
             error (Pretty.string_of (Pretty.chunks
               [Pretty.str ("micro_rust_notation: the rust name " ^ quote rust_name ^
                  " is not a plain identifier or ::-path, so it needs a bespoke"),
                Pretty.str "grammar production whose markup binds to a single backend\
                  \ constant --- but the registered term is not a constant or abbreviation:",
                Pretty.block [Pretty.str "  ", Syntax.pretty_term lthy t0]]))))
      \<comment>\<open>Reject overloading: at most one backend per non-grammatical name,
        across all kinds (the single grammar production has a single
        \<^verbatim>\<open>syntax_consts\<close> target).\<close>
      val existing =
        maps (fn k => Micro_Rust_Names.lookups lthy k rust_name)
          [Micro_Rust_Names.NLiteral, Micro_Rust_Names.NFunction,
           Micro_Rust_Names.NField]
      val _ =
        if null existing then ()
        else error (Pretty.string_of (Pretty.chunks
          [Pretty.str ("micro_rust_notation: the non-grammatical name " ^
             quote rust_name ^ " is already registered and cannot be"),
           Pretty.str "overloaded --- its bespoke grammar production binds to a single\
             \ backend. Pick a distinct name, or use a plain/::-path name",
           Pretty.str "(those support type-directed multi-backend dispatch)."]))
      val sanitise =
        String.translate (fn ch =>
          if Char.isAlphaNum ch then String.str ch else "")
      val syntax_constant = "_urust_identifier_bespoke_" ^ sanitise rust_name
      \<comment>\<open>The nullary template parses to \<open>Ast.Constant syntax_constant\<close> with
        no arguments, so the hook recovers the name from its closure (not
        from the AST args). We name \<open>_urust_identifier_id\<close> by string rather
        than \<^verbatim>\<open>\<^syntax_const>\<close>: this theory imports only \<open>Main\<close>, so that
        frontend syntax constant is not in scope at ML-compile time --- but
        it always is at the downstream use sites where the command runs.
        (The existing \<open>urust_const_ast_tr\<close> in \<open>Micro_Rust_Shallow_Embedding\<close>
        names it the same way, for the same reason.)\<close>
      fun hook _ _ =
        Ast.Appl [Ast.Constant "_urust_identifier_id",
                  Ast.Variable rust_name]
    in
      lthy
      |> Local_Theory.syntax_cmd true Syntax.mode_default
           [(syntax_constant, "urust_identifier", Mixfix.mixfix rust_name)]
      |> Local_Theory.background_theory
           (Sign.parse_ast_translation [(syntax_constant, hook)])
      \<comment>\<open>Bind the bespoke syntax constant to its backend so use sites are
        ctrl-clickable to the backend's definition (see above). The RHS
        must be the \<^emph>\<open>marked\<close> constant name (\<^ML>\<open>Lexicon.mark_const\<close>):
        \<^ML>\<open>Syntax.get_consts\<close> feeds it to \<^ML>\<open>Lexicon.unmark_entity\<close>,
        which only recognises marked names --- an unmarked name falls
        through to the default case, yielding no markup. (The
        \<^theory_text>\<open>syntax_consts\<close> command applies the same marking.)\<close>
      |> Local_Theory.syntax_deps [(syntax_constant, [Lexicon.mark_const c])]
    end;

fun do_register kind_opt (hol_src, (rust_name, rust_pos)) lthy =
  let
    val t0 = Syntax.read_term lthy hol_src
    val kind =
      case kind_opt of
        SOME k => (check_forced_kind k lthy t0; k)
      | NONE => Micro_Rust_Names.infer_kind_of_type (fastype_of t0)
  in
    lthy
    |> emit_bespoke_syntax hol_src rust_name t0
    |> Local_Theory.declaration {pervasive=false, syntax=true, pos=Position.none}
      (fn phi =>
        Micro_Rust_Names.register kind rust_name (Morphism.term phi t0) rust_pos)
  end;

\<comment>\<open>Config sub-command: parse \<open>[mode] "name"+\<close> and update the
  shadow-opt-out table. Empty name list \<Rightarrow> touch the default.\<close>
val parse_shadow_mode : Micro_Rust_Names.shadow_bit parser =
  Parse.$$$ "[" |--
    (   Args.$$$ "shadow_warn"    >> K (Micro_Rust_Names.Set_Suppress_Warning false)
     || Args.$$$ "shadow_no_warn" >> K (Micro_Rust_Names.Set_Suppress_Warning true)
     || Args.$$$ "shadow_err"     >> K (Micro_Rust_Names.Set_Suppress_Error false)
     || Args.$$$ "shadow_no_err"  >> K (Micro_Rust_Names.Set_Suppress_Error true))
    --| Parse.$$$ "]";

val parse_names : string list parser =
  Scan.repeat (Parse.position Parse.string >> #1);

val all_kinds =
  [Micro_Rust_Names.NLiteral, Micro_Rust_Names.NFunction, Micro_Rust_Names.NField];

fun do_config (bit, names) lthy =
  lthy |> Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none}
    (fn _ => fold (fn k => Micro_Rust_Names.set_shadow_bit k names bit) all_kinds);

\<comment>\<open>Payload for the registration sub-commands: a HOL term followed by
  the rust-side name (positional, for markup).\<close>
val parse_payload =
  Parse.term -- Parse.position (Parse.$$$ "(" |-- Parse.string --| Parse.$$$ ")");

\<comment>\<open>Top-level dispatch on the optional \<open>(\<dots>)\<close> modifier:
     absent     \<longrightarrow> auto-inferred registration
     \<open>(literal)\<close> \<longrightarrow> forced literal
     \<open>(call)\<close>    \<longrightarrow> forced function (the keyword \<open>function\<close> is taken
                    by HOL globally, so we use \<open>call\<close>)
     \<open>(field)\<close>   \<longrightarrow> forced field
     \<open>(config)\<close>  \<longrightarrow> shadow-check configuration sub-command
  Each branch parses its own remainder of the line.\<close>
val parse_cmd : (local_theory -> local_theory) parser =
  let
    val parse_register_with_kind =
      parse_payload >> (fn p => fn k => do_register (SOME k) p)
  in
       (Parse.$$$ "(" |-- Args.$$$ "literal" --| Parse.$$$ ")"
          |-- parse_register_with_kind
          >> (fn f => f Micro_Rust_Names.NLiteral))
    || (Parse.$$$ "(" |-- Args.$$$ "call" --| Parse.$$$ ")"
          |-- parse_register_with_kind
          >> (fn f => f Micro_Rust_Names.NFunction))
    || (Parse.$$$ "(" |-- Args.$$$ "field" --| Parse.$$$ ")"
          |-- parse_register_with_kind
          >> (fn f => f Micro_Rust_Names.NField))
    || (Parse.$$$ "(" |-- Args.$$$ "config" --| Parse.$$$ ")"
          |-- parse_shadow_mode -- parse_names
          >> do_config)
    || (parse_payload >> do_register NONE)
  end;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>micro_rust_notation\<close>
    "register a uRust notation (auto / forced kind) or configure shadow checks"
    parse_cmd;

end
\<close>


ML\<open>
\<comment>\<open>Query command: prints every registered notation as
  \<open><rust> \<longmapsto> <hol> (context)\<close>, with the HOL term printed via
  \<open>Syntax.pretty_term\<close>.\<close>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_micro_rust_notations\<close>
    "list all registered uRust name notations"
    (Scan.succeed (Toplevel.keep (fn st =>
      let
        val ctxt = Toplevel.context_of st;
        val entries = Micro_Rust_Names.dump ctxt;
        fun pretty (kind, rust, { hol_term, ... } : Micro_Rust_Names.entry) =
          Pretty.block
            [Pretty.str rust, Pretty.str " \<longmapsto> ",
             Syntax.pretty_term ctxt hol_term,
             Pretty.str ("  (" ^ Micro_Rust_Names.kind_to_string kind ^ ")")];
      in
        if null entries then writeln "no uRust name notations registered"
        else Pretty.writeln
          (Pretty.big_list "uRust name notations:" (map pretty entries))
      end)));
\<close>


(* ===================================================================== *)
(* Smoke tests                                                            *)
(* ===================================================================== *)

experiment
begin

definition test_my_some_a :: \<open>nat \<Rightarrow> nat option\<close> where
  \<open>test_my_some_a x = Some x\<close>

definition test_my_some_b :: \<open>bool \<Rightarrow> bool option\<close> where
  \<open>test_my_some_b b = Some b\<close>

\<comment>\<open>Single backend, kind forced via \<open>(literal)\<close>. The HOL constant's
  type is \<open>nat \<Rightarrow> nat option\<close> (no \<open>function_body\<close>, no \<open>lens\<close>) so the
  auto-inferred kind would also be \<open>literal\<close>; the modifier here is
  purely to exercise the parser branch.\<close>
micro_rust_notation (literal) test_my_some_a ("MySome")

\<comment>\<open>Multi-backend, no modifier: kind auto-inferred from the term's
  type. Same name as above; the typed term_check phase picks exactly
  one per occurrence (or reports ambiguity if both unify).\<close>
micro_rust_notation test_my_some_b ("MySome")

\<comment>\<open>Field-position registration: as a smoke test we don't have a real
  lens fixture in this experiment, so we register the same
  \<open>literal\<close>-shaped \<open>test_my_some_a\<close> under a field name with no kind
  modifier (auto-infer falls back to \<open>literal\<close>). For a real
  field-typed backend, see \<^verbatim>\<open>register_lens_with_micro_rust\<close> in
  Micro_Rust_Shallow_Embedding.thy.\<close>
micro_rust_notation test_my_some_a ("a_field")

print_micro_rust_notations

\<comment>\<open>Direct exercise of the dispatch term_check phase: a marker constrained
  at type \<open>nat \<Rightarrow> nat option\<close> resolves to \<open>test_my_some_a\<close>; constrained
  at \<open>bool \<Rightarrow> bool option\<close> resolves to \<open>test_my_some_b\<close>. The check fires
  only when the marker survives type inference, so we use \<open>typ\<close>
  ascriptions.\<close>
term \<open>(urust_dispatch (STR ''literal:MySome'') NoWitness :: nat \<Rightarrow> nat option)\<close>
term \<open>(urust_dispatch (STR ''literal:MySome'') NoWitness :: bool \<Rightarrow> bool option)\<close>

\<comment>\<open>Ambiguity: register two same-typed backends under the same name and
  show the loud error.  We use a comment-only assertion --- attempting
  the lookup at \<open>id\<close>'s shared schematic type would unify with both.\<close>
definition test_id_a :: \<open>nat \<Rightarrow> nat\<close> where \<open>test_id_a x = x\<close>
definition test_id_b :: \<open>nat \<Rightarrow> nat\<close> where \<open>test_id_b x = x\<close>

micro_rust_notation test_id_a ("Ambig")
micro_rust_notation test_id_b ("Ambig")

\<comment>\<open>Both backends have type \<open>nat \<Rightarrow> nat\<close>; an occurrence at \<open>nat \<Rightarrow> nat\<close>
  unifies with both, so resolution errors loudly listing candidates:

    Ambiguous uRust notation \<open>Ambig\<close> at type nat \<Rightarrow> nat
    candidate backends:
      test_id_b
      test_id_a

  Uncomment the line below to reproduce; left commented so the file
  builds clean.\<close>
\<comment>\<open>term \<open>(urust_dispatch (STR ''function:Ambig'') :: nat \<Rightarrow> nat)\<close>\<close>

end

end
