(*<*)
theory Simple_Word_Enums
  imports
    Case_for_Typedefs
    Misc.SetAdditional
    Misc.ListAdditional
    Misc.Result
    Misc.Debug_Logging
  keywords "simple_word_enum" :: thy_decl
    and "simple_word_enum_benchmark" :: thy_decl
begin
(*>*)

section\<open>Simple word enums\<close>

text\<open>A \<^emph>\<open>simple word enum\<close> is a type whose inhabitants correspond one-to-one to a fixed list of
distinct machine words. The \<^verbatim>\<open>simple_word_enum\<close> command defined below takes care of the
boilerplate: it builds the \<^verbatim>\<open>typedef\<close>, lifts one constant per variant, and hands the result to
\<^verbatim>\<open>setup_case_for_typedef\<close> so that \<^verbatim>\<open>case _ of _ \<Rightarrow> _\<close> works on the new type.

For a declaration

\<^verbatim>\<open>simple_word_enum (32) my_enum =
    Answer = \<open>0x42\<close>
  | Best   = \<open>0x72\<close>\<close>

where \<^verbatim>\<open>(32)\<close> is the width of the representing word type. Each value is an ordinary term, so it
may be any expression of that type; note that hexadecimal literals must be given in a cartouche,
as the outer syntax lexes \<^verbatim>\<open>0x42\<close> as two tokens. Plain decimal numerals need no cartouche.

An optional \<^verbatim>\<open>urust: "Name"\<close> clause may follow the type name:

\<^verbatim>\<open>simple_word_enum (32) my_enum urust: "MyEnum" = Answer = \<open>0x42\<close> | ...\<close>

This theory does \<^emph>\<open>nothing\<close> with that name --- it is recorded on the \<^verbatim>\<open>enum_info\<close> handed to
plugins, for a plugin to act on. The \<^verbatim>\<open>urust_notation\<close> plugin in
\<^verbatim>\<open>Shallow_Micro_Rust.Simple_Word_Enum_uRust\<close> uses it to register \<^verbatim>\<open>MyEnum::Answer\<close> as \<open>\<mu>Rust\<close>
notation for \<^verbatim>\<open>Answer\<close>; that plugin cannot live here, since \<^verbatim>\<open>micro_rust_notation\<close> belongs to a
session depending on this one.

The command generates, for the type \<^verbatim>\<open>T = my_enum\<close> and each variant \<^verbatim>\<open>Ci\<close>:

  \<^item> \<^verbatim>\<open>T_variants :: 32 word list\<close> --- the underlying word list, and
    \<^verbatim>\<open>T_variants_distinct\<close>, stating that its \<^verbatim>\<open>unat\<close> images are distinct;
  \<^item> the type \<^verbatim>\<open>T\<close> itself, as a \<^verbatim>\<open>typedef\<close> over \<^verbatim>\<open>set (map unat T_variants)\<close>, with
    \<^verbatim>\<open>setup_lifting\<close> applied;
  \<^item> one constant \<^verbatim>\<open>Ci :: T\<close> per variant, by \<^verbatim>\<open>lift_definition\<close>, with the transfer rules
    collected in the named theorem bundles \<^verbatim>\<open>T_rep_defs\<close> (the \<^verbatim>\<open>rep_eq\<close>s) and \<^verbatim>\<open>T_defs\<close>
    (the \<^verbatim>\<open>abs_eq\<close>s). Each is aliased under \<^verbatim>\<open>T.Ci\<close> as well, so variants can be named either
    bare or type-qualified, as \<^verbatim>\<open>datatype\<close> constructors can;
  \<^item> \<^verbatim>\<open>T_all :: T list\<close>, the list of all inhabitants, together with \<^verbatim>\<open>T_all_concrete\<close> (a
    \<^verbatim>\<open>[code]\<close> equation presenting it as the literal list \<^verbatim>\<open>[C1, ..., Cn]\<close>),
    \<^verbatim>\<open>T_all_distinct\<close> and \<^verbatim>\<open>T_all_total\<close>;
  \<^item> everything \<^verbatim>\<open>setup_case_for_typedef\<close> provides: \<^verbatim>\<open>T_index\<close>, \<^verbatim>\<open>T_indices_concrete\<close>,
    \<^verbatim>\<open>match_T\<close>, \<^verbatim>\<open>case_T\<close> and the case-reducing simproc.

Conversion functions between \<^verbatim>\<open>T\<close> and its representation word type are \<^emph>\<open>not\<close> generated; see
the tests at the end of this theory for how they are built on top.\<close>

subsection\<open>Supporting lemmas\<close>

text\<open>Simp set for reducing \<^verbatim>\<open>list.map f [x\<^sub>1, ..., x\<^sub>n]\<close> on a literal list of word numerals
without invoking the full simplifier on the numerals themselves. This keeps the generated
\<^verbatim>\<open>T_all_concrete\<close> proof fast for long variant lists.\<close>
lemmas map_simplifier_base = list.map simp_thms if_True if_False
    eq_numeral_simps one_neq_zero old.nat.distinct eq_numeral_Suc pred_numeral_simps num.distinct
    num.inject

text\<open>The two facts the generated \<^verbatim>\<open>T_all_distinct\<close> and \<^verbatim>\<open>T_all_total\<close> proofs rest on, stated
once here so that the per-enum proofs are a single \<^verbatim>\<open>rule\<close> application rather than a search.
Both are phrased over an abstract \<^term>\<open>type_definition Rep Abs (set (list.map unat ws))\<close>, which
is exactly what the generated \<^verbatim>\<open>typedef\<close> provides.\<close>

lemma simple_word_enum_distinct:
  assumes \<open>type_definition Rep Abs (set (list.map unat ws))\<close>
      and \<open>distinct (list.map unat ws)\<close>
    shows \<open>distinct (list.map (Abs \<circ> unat) ws)\<close>
  using assms(2) unfolding map_map[symmetric]
  apply (subst distinct_map; intro conjI)
   apply assumption
  apply (intro inj_onI)
  by (metis (no_types, lifting) assms(1) type_definition.Abs_eqD)

lemma map_id_ext:
  assumes \<open>\<And> x. x \<in> set xs \<Longrightarrow> f x = x\<close>
  shows \<open>xs = map f xs\<close>
  apply (subst list.map_id[of xs, symmetric])
  apply (intro map_ext strip)
  using assms by simp

lemma simple_word_enum_variants_alt:
  assumes \<open>type_definition Rep Abs (set (list.map unat ws))\<close>
      and \<open>my_enum_all \<equiv> list.map (Abs \<circ> unat) ws\<close>
  shows \<open>ws = map (of_nat \<circ> Rep) my_enum_all\<close>
  apply (simp add: assms(2))
  apply (intro map_id_ext)
  by (simp add: type_definition.Abs_inverse[OF assms(1)])

lemma simple_word_enum_total:
  assumes \<open>type_definition Rep Abs (set (list.map unat ws))\<close>
  shows \<open>x \<in> set (list.map (Abs \<circ> unat) ws)\<close>
  by (rule type_definition.Abs_cases[OF assms, of x]) force

subsection\<open>Supporting lemmas for the \<^verbatim>\<open>word_conversion\<close> plugin\<close>

text\<open>The \<^verbatim>\<open>word_conversion\<close> plugin (below) defines its \<^verbatim>\<open>try_from\<close> function as an \<^verbatim>\<open>ncase\<close>
expression over the variant words, and needs to relate that to the closed form
\<^verbatim>\<open>if w \<in> set T_variants then Some (Abs (unat w)) else None\<close>. The following lemmas do the work
generically, so that the generated proof is a single \<^verbatim>\<open>rule\<close> application.

First, rewriting rules to fold the literal \<^verbatim>\<open>ncase\<close> clause list --- which is a chain of
\<^term>\<open>Cons\<close> cells ending in a \<^term>\<open>(None, v)\<close> catch-all --- into
\<^term>\<open>zip (list.map Some ws) vs @ [(None, v)]\<close>, which the lemmas after it can reason about.\<close>

lemma into_Some_None_snoc_map:
  shows \<open>(Some w1, v1) # (zip (list.map Some ws) vs @ [(None, v)]) =
          zip (list.map Some (w1 # ws)) (v1 # vs) @ [(None, v)]\<close>
    and \<open>(Some w1, v1) # (None, v) # Nil =
          (zip (list.map Some [w1]) [v1]) @ [(None, v)]\<close>
  by simp+

lemma into_map:
  shows \<open>f x # Nil = list.map f (x # Nil)\<close>
    and \<open>f x # list.map f xs = list.map f (x # xs)\<close>
  by simp_all

text\<open>An \<^verbatim>\<open>ncase\<close> over a \<^term>\<open>zip\<close> of keys and values splits on whether the scrutinee is one of
the keys: if it is, the catch-all is unreachable; if not, only the catch-all remains.\<close>

lemma ncase_selector_raw_append:
  assumes \<open>length ks \<le> length vs\<close>
  shows \<open>ncase_selector_raw (zip (list.map Some ks) vs @ ys) x =
    (if x \<in> set ks then
      ncase_selector_raw (zip (list.map Some ks) vs) x
    else
      ncase_selector_raw ys x)\<close>
proof (cases \<open>x \<in> set ks\<close>)
  case True
  with assms have \<open>find (\<lambda>(ma, b). case ma of None \<Rightarrow> True | Some a \<Rightarrow> a = x)
                (zip (map Some ks) vs) \<noteq> None\<close>
    by (intro notI) (force simp add: set_zip in_set_conv_nth find_None_iff)
  with True show ?thesis
    by (auto simp add: ncase_selector_raw_def list_find_append
        split: option.splits)
next
  case False
  with assms have \<open>find (\<lambda>(ma, b). case ma of None \<Rightarrow> True | Some a \<Rightarrow> a = x)
                (zip (map Some ks) vs) = None\<close>
    by (force simp add: set_zip find_None_iff)
  with False show ?thesis
    by (simp add: ncase_selector_raw_def list_find_append)
qed

text\<open>When the values are themselves the image of the keys under some \<^term>\<open>f\<close>, an \<^verbatim>\<open>ncase\<close> hit
returns \<^term>\<open>f x\<close> --- which is what makes the plugin's \<^verbatim>\<open>try_from\<close> collapse to
\<^term>\<open>Some (Abs (unat w))\<close> without a per-variant case split.\<close>

lemma ncase_selector_raw_map:
  assumes \<open>x \<in> set xs\<close>
  shows \<open>ncase_selector_raw (zip (list.map Some xs) (list.map f xs)) x = f x\<close>
  using assms
  apply (clarsimp simp add: ncase_selector_raw_def split: option.splits)
  apply (intro conjI strip)
   apply (force simp add: set_zip in_set_conv_nth find_None_iff)
  by (clarsimp simp add: find_Some_iff)

text\<open>Putting those together: the whole \<^verbatim>\<open>try_from_alt\<close> statement, over an abstract variant list.
The plugin folds its generated \<^verbatim>\<open>ncase\<close> into the \<^term>\<open>zip\<close> shape on the left and then discharges
the goal with this single rule, so nothing in the generated proof grows with the variant count.\<close>

lemma simple_word_enum_ncase_alt:
  shows \<open>ncase_selector
            (zip (list.map Some ws) (list.map Ok (list.map f ws)) @ [(None, Err ())]) w
          = (if w \<in> set ws then Ok (f w) else Err ())\<close>
proof -
  have len: \<open>length ws \<le> length (list.map Ok (list.map f ws))\<close>
    by simp
  show ?thesis
  proof (cases \<open>w \<in> set ws\<close>)
    case True
    then show ?thesis
      by (simp only: ncase_selector_def ncase_selector_raw_append[OF len] if_True)
         (simp only: map_map ncase_selector_raw_map[OF True] comp_def)
  next
    case False
    then show ?thesis
      by (simp only: ncase_selector_def ncase_selector_raw_append[OF len] if_False)
         (simp add: ncase_selector_raw_def)
  qed
qed

subsection\<open>The \<^verbatim>\<open>simple_word_enum\<close> command\<close>

ML \<open>
signature SIMPLE_WORD_ENUM =
sig
  (* A per-invocation phase timer. Each generation step is wrapped in `phase`, which records
     its elapsed time under a name; the accumulated log is printed as a breakdown when timing
     is on. The timer is carried explicitly (in enum_info) rather than through global state,
     so a plugin records into the same log the command prints, and parallel runs stay
     independent. Modelled on Crush's Crush_Time (Crush/time.ML), pared down: the phases run
     once each, so per-name statistics/percentiles are unnecessary here. *)
  type timer

  (* Timing is off unless this config is set, so a bare declaration is silent as before. *)
  val timing_enabled: bool Config.T

  (* phase timer name f: run f (), recording its elapsed time under `name` when the timer is
     live. Returns f's result. Timing calls nest --- an inner phase's time is also counted in
     any enclosing phase --- which is what lets the command time a plugin as one line while
     the plugin times its own sub-phases. *)
  val phase: timer -> string -> (unit -> 'a) -> 'a

  (* A fresh timer; `live` controls whether it records at all. *)
  val new_timer: bool -> timer
  (* The recorded phases, outermost first, as (depth, name, elapsed). *)
  val timer_entries: timer -> (int * string * Timing.timing) list
  (* Sum of the top-level (depth 0) phases --- the total wall time across the whole command. *)
  val timer_total: timer -> Timing.timing
  (* Render a timer's log as an indented, human-readable breakdown under `title`. *)
  val format_timer_report: string -> timer -> string

  (* Everything a plugin needs to know about a freshly-declared enum. All of it is computed
     by the command anyway; this record just hands it on. Constants and theorems have been
     transported along the target morphism, so they are usable as they stand. *)
  type enum_info = {
    type_name: string,                 (* base name, e.g. "my_enum" *)
    (* The optional \<^verbatim>\<open>urust: "Name"\<close> given at declaration time. The command itself does
       nothing with this --- it is carried here purely so that a plugin can pick it up; see
       the \<^verbatim>\<open>urust_notation\<close> plugin in \<^theory>\<open>Shallow_Micro_Rust.Simple_Word_Enum_uRust\<close>,
       which cannot live in this theory because the \<^verbatim>\<open>micro_rust_notation\<close> command sits in a
       session that depends on this one. *)
    urust_name: string option,
    absT: typ,                         (* the enum type *)
    wordT: typ,                        (* representation word type *)
    width: int,                        (* its bit width *)
    variant_bindings: binding list,    (* C1..Cn, as declared *)
    variant_consts: term list,         (* C1..Cn *)
    words: term list,                  (* w1..wn, in the same order *)
    variants_const: term,              (* T_variants *)
    variants_def: thm,
    variants_distinct: thm,            (* distinct (map unat T_variants) *)
    variants_alt: thm,                 (* variants = list.map (of_nat \<circ> Rep) T_all *)
    all_const: term,                   (* T_all *)
    all_def: thm,
    all_concrete: thm,                 (* T_all = [C1, ..., Cn] *)
    all_distinct: thm,
    all_total: thm,
    type_definition: thm,
    Abs_name: string,
    Rep_name: string,
    case_result: Case_For_Typedef.case_result,   (* case_T and its rewrite chain *)
    rep_defs: string,                  (* the T_rep_defs named-theorems bundle *)
    defs: string,                      (* the T_defs bundle *)
    timer: timer,                      (* record plugin sub-phases here *)
    report: bool                       (* false when the caller wants no per-enum output *)
  }

  (* Register a generator to run for every enum whose plugin filter admits `name`. *)
  val interpretation: string -> (enum_info -> local_theory -> local_theory) ->
    theory -> theory

  (* The command's implementation, minus outer syntax. `timer` records the phase breakdown;
     `report` prints the human-readable summary of generated items. The tuple is
     (plugin filter, word width, type binding, optional uRust name,
      (variant binding, value term string) list), where the filter is the still-unevaluated
     form Plugin_Name.parse_filter yields. The benchmark command reuses this to drive many
     enums under one timer. *)
  val simple_word_enum_core:
    { timer: timer, report: bool } ->
    (Proof.context -> Plugin_Name.filter) * int * binding * string option *
      (binding * string) list ->
    local_theory -> local_theory
end

structure Simple_Word_Enum : SIMPLE_WORD_ENUM =
struct

val timing_enabled =
  Attrib.setup_config_bool \<^binding>\<open>simple_word_enum_timing\<close> (K false)

(* A timer collects (name, elapsed) pairs into a ref, newest first, and tracks nesting depth
   so the printed report can indent sub-phases under their parent. `live = false` disables all
   recording (a bare declaration with timing off), so `phase` is then just `f ()`. *)
type timer = { live: bool, log: (int * string * Timing.timing) list Unsynchronized.ref,
               depth: int Unsynchronized.ref }

fun new_timer live : timer =
  { live = live, log = Unsynchronized.ref [], depth = Unsynchronized.ref 0 }

fun phase ({ live, log, depth }: timer) name f =
  if not live then f ()
  else
    let
      val d = ! depth
      val _ = depth := d + 1
      val start = Timing.start ()
      val result = Exn.result f ()
      val elapsed = Timing.result start
      val _ = depth := d
      val _ = log := (d, name, elapsed) :: ! log
    in Exn.release result end

fun timer_entries ({ log, ... }: timer) = rev (! log)

fun timer_total (timer: timer) =
  timer_entries timer
  |> filter (fn (d, _, _) => d = 0)
  |> List.foldl (fn ((_, _, t), acc) =>
       { elapsed = #elapsed acc + #elapsed t, cpu = #cpu acc + #cpu t,
         gc = #gc acc + #gc t } : Timing.timing)
     { elapsed = Time.zeroTime, cpu = Time.zeroTime, gc = Time.zeroTime }

(* Format a timer's log as an indented breakdown, outermost phase first. *)
fun format_timer_report (title: string) (timer: timer) =
  let
    fun fmt (d, name, t) =
      replicate_string (2 * (d + 1)) " " ^ name ^ ": " ^ Timing.message t
  in title :: map fmt (timer_entries timer) |> cat_lines end

type enum_info = {
  type_name: string,
  urust_name: string option,
  absT: typ,
  wordT: typ,
  width: int,
  variant_bindings: binding list,
  variant_consts: term list,
  words: term list,
  variants_const: term,
  variants_def: thm,
  variants_distinct: thm,
  variants_alt: thm,
  all_const: term,
  all_def: thm,
  all_concrete: thm,
  all_distinct: thm,
  all_total: thm,
  type_definition: thm,
  Abs_name: string,
  Rep_name: string,
  case_result: Case_For_Typedef.case_result,
  rep_defs: string,
  defs: string,
  timer: timer,
  report: bool
}

(* The plugin mechanism is Isabelle's own (Pure/Tools/plugin.ML), as used by datatype,
   typedef and bnf_lfp_size: registered plugins run by default and are selected per
   declaration with the `(plugins only:/del: ...)` group. *)
structure Enum_Plugin = Plugin(type T = enum_info)

(* Plugins run in whatever target the declaration appeared in, so that the names they
   introduce sit beside the enum's own. Note we deliberately do *not* re-root the background
   naming the way Typedef.interpretation does: that would discard an enclosing local target
   (e.g. an `experiment`), and the enum's own constants --- `case_T` in particular --- live
   inside it. *)
fun interpretation name f = Enum_Plugin.interpretation name f

(* Naming conventions for the generated constants and facts. *)
fun variants_name type_name = type_name ^ "_variants"
fun variants_distinct_name type_name = variants_name type_name ^ "_distinct"
fun all_name type_name = type_name ^ "_all"
fun all_concrete_name type_name = all_name type_name ^ "_concrete"
fun all_distinct_name type_name = all_name type_name ^ "_distinct"
fun all_variants_alt_name type_name = variants_name type_name ^ "_alt"
fun all_total_name type_name = all_name type_name ^ "_total"
fun rep_defs_name type_name = type_name ^ "_rep_defs"
fun defs_name type_name = type_name ^ "_defs"

fun note_thm name attrs thm lthy =
  Local_Theory.note ((Binding.name name, attrs), [thm]) lthy |> apfst (the_single o snd)

(* Define a constant \<^verbatim>\<open>name \<equiv> rhs\<close>, returning the constant and its definitional theorem
   already transported along the target morphism, so that both are usable in the proofs
   that follow even when the command runs inside a local target.

   Uses \<^verbatim>\<open>Specification.definition\<close> rather than the lower-level \<^verbatim>\<open>Local_Theory.define\<close>: the former
   attaches a \<^emph>\<open>default\<close> code equation to the \<^verbatim>\<open>_def\<close> fact it notes, which is what makes the
   generated constants code-exportable without any \<^verbatim>\<open>[code]\<close> declarations. Being a default, it is
   superseded by an explicit \<^verbatim>\<open>[code]\<close> elsewhere --- so \<^verbatim>\<open>T_all\<close>, whose definition goes through
   \<^verbatim>\<open>Abs\<close>/\<^verbatim>\<open>unat\<close>, still generates from \<^verbatim>\<open>T_all_concrete\<close>'s literal list. *)
fun define_const name rhs lthy =
  let
    val binding = Binding.name name
    val ((_, (_, def_thm)), lthy) = Specification.definition
      (SOME (binding, NONE, NoSyn)) [] []
      ((Binding.name (name ^ "_def"), []), Logic.mk_equals (Free (name, fastype_of rhs), rhs))
      lthy
    val const = Const (Local_Theory.full_name lthy binding, fastype_of rhs)
    val phi = Local_Theory.target_morphism lthy
  in ((const, Morphism.thm phi def_thm), lthy) end

(* Simp set for the small membership goals discharged along the way. Deliberately a
   [simp only:]-style set: the variants are word numerals, and letting the default simp set
   loose on them is what makes the hand-written version slow for long lists. *)
fun member_simps ctxt =
  clear_simpset ctxt addsimps
    @{thms eq_onp_same_args list.map comp_def snd_conv in_set_cons simp_thms}

(* Step 1: define T_variants = [w1, ..., wn] and prove distinct (map unat T_variants). *)
fun define_variants type_name wordT words lthy =
  let
    val ((const, def_thm), lthy) =
      define_const (variants_name type_name) (HOLogic.mk_list wordT words) lthy

    (* distinct (list.map unat T_variants).

       This is the most expensive generated proof --- the goal is quadratic in the number of
       variants --- and it does use the default simp set, deliberately: reducing \<^verbatim>\<open>unat\<close> of a
       numeral needs the word simp rules, and a hand-picked [simp only:] set that discharges
       it could not be found. \<^verbatim>\<open>code_simp\<close> is dramatically worse (it does not terminate on a
       few dozen variants). Measured on 120 variants: ~2s. *)
    val unatT = wordT --> HOLogic.natT
    val unat = Const (\<^const_name>\<open>unsigned\<close>, unatT)
    val mapped = \<^Const>\<open>map wordT HOLogic.natT\<close> $ unat $ const
    val goal = HOLogic.mk_Trueprop (\<^Const>\<open>distinct HOLogic.natT\<close> $ mapped)
    val distinct_thm = Goal.prove lthy [] [] goal (fn { context = ctxt, ... } =>
      Local_Defs.unfold_tac ctxt [def_thm] THEN simp_tac ctxt 1)
    val (distinct_thm, lthy) =
      note_thm (variants_distinct_name type_name) [] distinct_thm lthy
  in ((const, def_thm, distinct_thm, mapped), lthy) end

(* Step 2: typedef T = set (map unat T_variants), then setup_lifting. *)
fun define_typedef type_binding mapped_variants variants_def lthy =
  let
    val typedef_set = \<^Const>\<open>set HOLogic.natT\<close> $ mapped_variants
    val ((_, (typ_info, typedef_info)), lthy) = lthy
      |> Typedef.add_typedef { overloaded = false } (type_binding, [], NoSyn) typedef_set NONE
           (* Nonemptiness: the first variant inhabits the set. Kept to a fixed number of
              rule applications so that the cost does not grow with the variant list. *)
           (fn ctxt =>
              Local_Defs.unfold_tac ctxt [variants_def] THEN
              simp_tac (clear_simpset ctxt addsimps @{thms list.map list.set}) 1 THEN
              resolve_tac ctxt @{thms exI} 1 THEN
              resolve_tac ctxt @{thms insertI1} 1)
    val (_, lthy) =
      Lifting_Setup.setup_by_typedef_thm Lifting_Setup.default_config
        (#type_definition typedef_info) lthy
  in ((typ_info, typedef_info), lthy) end

(* Step 3: one lift_definition per variant, tagging rep_eq/abs_eq into the two bundles. *)
fun define_variant_consts type_name absT variants_def (rep_defs, defs) variant_specs lthy =
  let
    fun define (binding, word) lthy =
      let
        val rhs = Const (\<^const_name>\<open>unsigned\<close>, fastype_of word --> HOLogic.natT) $ word
        val (ld, lthy) = Lifting_Def.lift_def
          { notes = true } (binding, NoSyn) absT rhs
          (fn ctxt =>
             Local_Defs.unfold_tac ctxt [variants_def] THEN
             simp_tac (member_simps ctxt) 1) [] lthy
        fun add_to bundle thm =
          Local_Theory.note ((Binding.empty,
            [Attrib.internal \<^here> (K (Named_Theorems.add bundle))]), [thm]) #> snd
        val lthy = lthy
          |> add_to defs (Lifting_Def.abs_eq_of_lift_def ld)
          |> (case Lifting_Def.rep_eq_of_lift_def ld of
                SOME rep_eq => add_to rep_defs rep_eq
              | NONE => I)
        (* Also reachable as `T.Ci`, the way datatype constructors are: alias the constant
           under the type-qualified name. Non-mandatory qualification, so the bare `Ci` keeps
           working and `T.Ci` becomes available for disambiguation --- exactly what
           `Binding.qualify false` gives datatype's constructors (ctr_sugar.ML). *)
        val c = Lifting_Def.lift_const_of_lift_def ld
        val lthy = Local_Theory.const_alias
          (Binding.qualify false type_name binding) (dest_Const_name c) lthy
      in (c, lthy) end
    val (consts, lthy) = fold_map define variant_specs lthy
    (* The constants come back as they were at definition time; re-resolve against the
       target so that later steps see proper Consts rather than Frees. *)
    val consts = map (fn c => Const (dest_Const_name c, absT)) consts
  in (consts, lthy) end

(* Step 4: define T_all = map (Abs o unat) T_variants and derive its properties. *)
fun define_all type_name wordT absT Abs_name Rep_name defs variants_const variants_def variants_distinct
      type_definition_thm variant_consts lthy =
  let
    val unat = Const (\<^const_name>\<open>unsigned\<close>, wordT --> HOLogic.natT)
    val abs_const = Const (Abs_name, HOLogic.natT --> absT)
    val compT = (HOLogic.natT --> absT) --> (wordT --> HOLogic.natT) --> (wordT --> absT)
    val abs_o_unat = Const (\<^const_name>\<open>comp\<close>, compT) $ abs_const $ unat
    val rhs = \<^Const>\<open>map wordT absT\<close> $ abs_o_unat $ variants_const

    val ((all_const, all_def), lthy) = define_const (all_name type_name) rhs lthy

    (* T_all_concrete [code]: T_all = [C1, ..., Cn].
       Proved by rewriting the definition with the variant abs_eqs backwards, exactly as
       the hand-written version did, so that only the cheap map_simplifier_base set runs. *)
    val concrete_goal = HOLogic.mk_Trueprop
      (HOLogic.mk_eq (all_const, HOLogic.mk_list absT variant_consts))
    val concrete_thm = Goal.prove lthy [] [] concrete_goal (fn { context = ctxt, ... } =>
      Local_Defs.unfold_tac ctxt [all_def, variants_def] THEN
      simp_tac (clear_simpset ctxt addsimps
        (@{thms map_simplifier_base comp_def}
         @ map (Thm.symmetric o Simpdata.mk_eq) (Named_Theorems.get ctxt defs))) 1)
    val (concrete_thm, lthy) =
      note_thm (all_concrete_name type_name) @{attributes [code]} concrete_thm lthy

    (* T_all_distinct / T_all_total, both a single rule application against the
       supporting lemmas above. *)
    val distinct_goal = HOLogic.mk_Trueprop (\<^Const>\<open>distinct absT\<close> $ all_const)
    val distinct_thm = Goal.prove lthy [] [] distinct_goal (fn { context = ctxt, ... } =>
      Local_Defs.unfold_tac ctxt [all_def] THEN
      resolve_tac ctxt [@{thm simple_word_enum_distinct} OF
        [type_definition_thm, variants_distinct]] 1)
    val (_, lthy) = note_thm (all_distinct_name type_name) [] distinct_thm lthy

    (* variants_alt: T_variants = map (of_nat \<circ> Rep) T_all *)
    val rep_const = Const (Rep_name, absT --> HOLogic.natT)
    val of_nat = Const (\<^const_name>\<open>of_nat\<close>, HOLogic.natT --> wordT)
    val compT = (HOLogic.natT --> wordT) --> (absT --> HOLogic.natT) --> (absT --> wordT)
    val of_nat_o_rep = Const (\<^const_name>\<open>comp\<close>, compT) $ of_nat $ rep_const
    val variants_alt_goal = HOLogic.mk_Trueprop
      (HOLogic.mk_eq (variants_const, \<^Const>\<open>map absT wordT\<close> $ of_nat_o_rep $ all_const))
    val variants_alt_thm = Goal.prove lthy [] [] variants_alt_goal (fn { context = ctxt, ...} =>
      resolve_tac ctxt [@{thm simple_word_enum_variants_alt} OF
        [type_definition_thm, all_def]] 1
    )
    val (_, lthy) = note_thm (all_variants_alt_name type_name) [] variants_alt_thm lthy

    (* \<^verbatim>\<open>x\<close> is generalized, so that the fact reads \<^verbatim>\<open>?x \<in> set T_all\<close> and can be
       instantiated freely by its users. *)
    val x = Free ("x", absT)
    val total_goal = HOLogic.mk_Trueprop
      (\<^Const>\<open>Set.member absT\<close> $ x $ (\<^Const>\<open>set absT\<close> $ all_const))
    val total_thm = Goal.prove lthy ["x"] [] total_goal (fn { context = ctxt, ... } =>
      Local_Defs.unfold_tac ctxt [all_def] THEN
      resolve_tac ctxt [@{thm simple_word_enum_total} OF [type_definition_thm]] 1)
    val (total_thm, lthy) = note_thm (all_total_name type_name) [] total_thm lthy
  in ((all_const, all_def, concrete_thm, distinct_thm, total_thm, variants_alt_thm), lthy) end

(* The core of the command, parameterised by a timer so the benchmark command can reuse it.
   Each generation step is wrapped in `phase`; `report` controls whether the human-readable
   summary of what was generated is printed (the benchmark prints its own tables instead). *)
fun simple_word_enum_core { timer, report }
      (raw_filter, width, type_binding, urust_name, variant_specs) lthy =
  let
    val type_name = Binding.name_of type_binding
    val n = length variant_specs
    val _ = if n = 0 then error "simple_word_enum: no variants given" else ()
    val plugin_filter = Plugin_Name.make_filter lthy raw_filter

    val ((wordT, words, bindings), lthy) = phase timer "parse" (fn () =>
      let
        (* The word type is built through the type-numeral syntax: there is no ML-level
           constructor for turning a width into the bit0/bit1/num1 tree. *)
        val wordT = Syntax.read_typ lthy (string_of_int width ^ " word")
        val words = variant_specs |> map (fn (_, raw) =>
          Syntax.parse_term lthy raw
          |> Type.constraint wordT
          |> Syntax.check_term lthy)
        val bindings = map fst variant_specs
        (* Syntactically equal values are rejected up front: the generated distinctness proof
           would fail on them, but with a goal that says nothing about the cause. Values that
           differ syntactically but are equal as words are still caught by that proof. *)
        val _ = case duplicates (op aconv) words of
            [] => ()
          | dups => error ("simple_word_enum " ^ type_name ^ ": repeated variant value(s): " ^
              commas (map (Syntax.string_of_term lthy) dups))
      in ((wordT, words, bindings), lthy) end)

    (* named_theorems T_rep_defs / T_defs, before the lift_definitions that populate them *)
    val (rep_defs, lthy) = Named_Theorems.declare (Binding.name (rep_defs_name type_name)) "" lthy
    val (defs, lthy) = Named_Theorems.declare (Binding.name (defs_name type_name)) "" lthy

    val ((variants_const, variants_def, variants_distinct, mapped_variants), lthy) =
      phase timer "variants" (fn () => define_variants type_name wordT words lthy)

    val ((typ_info, typedef_info), lthy) =
      phase timer "typedef+lifting" (fn () =>
        define_typedef type_binding mapped_variants variants_def lthy)
    val { abs_type = absT, Abs_name, Rep_name, ... } = typ_info
    val type_definition_thm = #type_definition typedef_info

    val (variant_consts, lthy) =
      phase timer "variant_consts" (fn () =>
        define_variant_consts type_name absT variants_def (rep_defs, defs)
          (bindings ~~ words) lthy)

    val ((all_const, all_def, concrete_thm, distinct_thm, total_thm, variants_alt_thm), lthy) =
      phase timer "all" (fn () =>
        define_all type_name wordT absT Abs_name Rep_name defs variants_const variants_def
          variants_distinct type_definition_thm variant_consts lthy)

    (* Reuse the existing case setup, silencing its own report in favour of ours. *)
    val (case_result, lthy) = phase timer "case_setup" (fn () =>
      Case_For_Typedef.setup_case_for_typedef { verbose = false }
        type_name concrete_thm distinct_thm lthy)

    (* Hand the finished enum to whichever plugins the declaration admits. Any definitions
       and theorems they add are reported by the plugins themselves. *)
    val info : enum_info = {
      type_name = type_name, urust_name = urust_name,
      absT = absT, wordT = wordT, width = width,
      variant_bindings = bindings, variant_consts = variant_consts, words = words,
      variants_const = variants_const, variants_def = variants_def,
      variants_distinct = variants_distinct, variants_alt = variants_alt_thm,
      all_const = all_const, all_def = all_def, all_concrete = concrete_thm,
      all_distinct = distinct_thm, all_total = total_thm,
      type_definition = type_definition_thm,
      Abs_name = Abs_name, Rep_name = #Rep_name typ_info,
      case_result = case_result,
      rep_defs = rep_defs, defs = defs, timer = timer, report = report }
    val lthy = phase timer "plugins" (fn () => Enum_Plugin.data plugin_filter info lthy)

    val _ = if not report then () else
      writeln ("simple_word_enum " ^ type_name ^ " (" ^ string_of_int n ^ " variants):\n" ^
      cat_lines (map (prefix "  ")
        (["type        " ^ type_name,
          "definition  " ^ variants_name type_name,
          "lemma       " ^ variants_distinct_name type_name,
          "constants   " ^ commas (map Binding.name_of bindings),
          "facts       " ^ rep_defs_name type_name ^ ", " ^ defs_name type_name,
          "definition  " ^ all_name type_name,
          "lemmas      " ^ commas [all_concrete_name type_name ^ " [code]",
              all_distinct_name type_name, all_total_name type_name]]
         @ Case_For_Typedef.generated_summary type_name n)))
  in lthy end

fun simple_word_enum_cmd (((((raw_filter, width), type_binding), urust_name), variant_specs))
      lthy =
  let
    val timer = new_timer (Config.get lthy timing_enabled)
    val lthy = simple_word_enum_core { timer = timer, report = true }
      (raw_filter, width, type_binding, urust_name, variant_specs) lthy
    val _ = if not (Config.get lthy timing_enabled) then () else
      writeln (format_timer_report
        ("simple_word_enum " ^ Binding.name_of type_binding ^ " timings ("
         ^ Timing.message (timer_total timer) ^ " total):") timer)
  in lthy end

(* The optional leading `(plugins only: ...)` / `(plugins del: ...)` group, mirroring
   datatype's option group (see ctr_sugar.ML). Absent, every registered plugin runs.
   Both this group and the width are parenthesised, so the lookahead has to see past the
   opening paren to tell them apart --- hence Scan.ahead on the `plugins` keyword rather
   than a plain Scan.optional, which would commit to `(` and then fail on the width. *)
val parse_plugins =
  Scan.optional
    (Scan.ahead (Parse.$$$ "(" -- Parse.reserved "plugins") |--
      (Parse.$$$ "(" |-- Plugin_Name.parse_filter --| Parse.$$$ ")"))
    (K Plugin_Name.default_filter)

(* The optional `urust: "Name"` clause, between the type name and the `=`. Purely recorded
   on enum_info; this theory never acts on it. *)
val parse_urust_name =
  Scan.option (Parse.reserved "urust" |-- Parse.$$$ ":" |-- Parse.string)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>simple_word_enum\<close>
    "define a type whose inhabitants are a fixed list of distinct machine words"
    (parse_plugins --
      (Parse.$$$ "(" |-- Parse.nat --| Parse.$$$ ")") --
      Parse.binding -- parse_urust_name --| Parse.$$$ "=" --
      Parse.enum1 "|" (Parse.binding --| Parse.$$$ "=" -- Parse.term)
     >> simple_word_enum_cmd)

end
\<close>

subsection\<open>Tests without plugins\<close>
experiment
begin

\<comment>\<open>Explicitly setting no plugins: declaring a plugin afterward will rerun it
on existing defined enums that are no longer accessible and fail..? \<close>
simple_word_enum (plugins only:) (32) my_enum =
    Answer = \<open>0x42\<close>
  | Best   = \<open>0x72\<close>
  | Leet   = \<open>0x1337\<close>
  | Angry  = \<open>0x1066601\<close>

text\<open>The generated facts are as advertised.\<close>

lemma
  shows \<open>my_enum_variants = [0x42, 0x72, 0x1337, 0x1066601]\<close>
    and \<open>my_enum_all = [Answer, Best, Leet, Angry]\<close>
  by (simp_all add: my_enum_variants_def my_enum_all_concrete)

lemma
  shows \<open>distinct my_enum_all\<close> and \<open>x \<in> set my_enum_all\<close>
  by (rule my_enum_all_distinct, rule my_enum_all_total)

text\<open>\<^verbatim>\<open>case\<close> expressions work, and the simproc reduces them on concrete variants.\<close>

definition my_enum_is_odd :: \<open>my_enum \<Rightarrow> bool\<close> where
  \<open>my_enum_is_odd e \<equiv> case e of
      Answer \<Rightarrow> False
    | Best    \<Rightarrow> False
    | Leet    \<Rightarrow> True
    | Angry   \<Rightarrow> True\<close>

lemma
  shows \<open>\<not> my_enum_is_odd Answer\<close> and \<open>\<not> my_enum_is_odd Best\<close>
    and \<open>my_enum_is_odd Leet\<close> and \<open>my_enum_is_odd Angry\<close>
  by (simp_all add: my_enum_is_odd_def)

text\<open>A \<^verbatim>\<open>case\<close> on a variable is \<^emph>\<open>not\<close> reduced prematurely.\<close>

lemma
  assumes \<open>case e of Answer \<Rightarrow> False | Best \<Rightarrow> False | _ \<Rightarrow> True\<close>
  shows \<open>my_enum_is_odd e\<close>
  by (simp add: my_enum_is_odd_def) (rule assms)

text\<open>Variants are distinct, and the representation is the expected \<^const>\<open>unat\<close> image.\<close>

lemma
  shows \<open>Answer \<noteq> Best\<close> and \<open>Leet \<noteq> Angry\<close>
  using my_enum_all_distinct by (simp_all add: my_enum_all_concrete)

lemma
  shows \<open>Rep_my_enum Leet = unat (0x1337 :: 32 word)\<close>
  by (simp add: my_enum_rep_defs)

text\<open>Variants are reachable both bare and type-qualified, as \<^verbatim>\<open>datatype\<close> constructors are.\<close>

lemma
  shows \<open>my_enum.Answer = Answer\<close> and \<open>my_enum.Leet = Leet\<close>
  by (rule refl)+

definition my_enum_qualified_use :: \<open>my_enum\<close> where
  \<open>my_enum_qualified_use \<equiv> my_enum.Best\<close>

end

subsection\<open>The \<^verbatim>\<open>word_conversion\<close> plugin\<close>

text\<open>Generates conversions between the enum and its representation word type:

  \<^item> \<^verbatim>\<open>T_to_uN_pure :: T \<Rightarrow> N word\<close>, a \<^verbatim>\<open>case\<close> expression over the variants, with
    \<^verbatim>\<open>T_to_uN_pure_alt\<close> characterising it as \<^term>\<open>of_nat (Rep e)\<close>;
  \<^item> \<^verbatim>\<open>T_try_from_uN_pure :: N word \<Rightarrow> T option\<close>, an \<^verbatim>\<open>ncase\<close> over the variant words, with
    \<^verbatim>\<open>T_try_from_uN_pure_alt\<close> characterising it as
    \<^term>\<open>if w \<in> set T_variants then Some (Abs (unat w)) else None\<close>;
  \<^item> \<^verbatim>\<open>T_to_uN_pure_then_try_from\<close>, the round trip.

The plugin is registered under the name \<^verbatim>\<open>word_conversion\<close> and runs by default; suppress it
with \<^verbatim>\<open>simple_word_enum (plugins del: word_conversion) ...\<close>.\<close>

lemma map_nth_find_index:
  assumes \<open>x \<in> set xs\<close>
  shows \<open>list.map f xs ! find_index xs x = f x\<close>
  using assms find_index_bounded_if_in_list[OF assms]
  by (simp add: lookup_at_find_index)

ML \<open>
local

(* Build `ncase w of w1 => Some C1 | ... | wn => Some Cn | _ => None`, i.e.
   ncase_selector [(Some w1, Some C1), ..., (Some wn, Some Cn), (None, None)] w. *)
fun mk_ncase wordT absT words variant_consts w =
  let
    val unitT = Type (\<^type_name>\<open>unit\<close>, [])
    val resultT = Type (\<^type_name>\<open>result\<close>, [absT, unitT])
    val wordOptT = Type (\<^type_name>\<open>option\<close>, [wordT])
    val clauseT = HOLogic.mk_prodT (wordOptT, resultT)
    fun some T t = Const (\<^const_name>\<open>Some\<close>, T --> Type (\<^type_name>\<open>option\<close>, [T])) $ t
    fun ok A B a = Const (\<^const_name>\<open>Ok\<close>, A --> Type (\<^type_name>\<open>result\<close>, [A, B])) $ a
    fun err A B b = Const (\<^const_name>\<open>Err\<close>, B --> Type (\<^type_name>\<open>result\<close>, [A, B])) $ b
    fun none T = Const (\<^const_name>\<open>None\<close>, Type (\<^type_name>\<open>option\<close>, [T]))
    val unit_el = Const (\<^const_name>\<open>Unity\<close>, unitT)
    val clauses = map2 (fn wd => fn c =>
        HOLogic.mk_prod (some wordT wd, ok absT unitT c)) words variant_consts
      @ [HOLogic.mk_prod (none wordT, err absT unitT unit_el)]
    val selT = HOLogic.listT clauseT --> wordT --> resultT
  in Const (\<^const_name>\<open>ncase_selector\<close>, selT) $ HOLogic.mk_list clauseT clauses $ w end

fun generate_word_conversion (info: Simple_Word_Enum.enum_info) lthy =
  let
    val { type_name, absT, wordT, width, variant_consts, words, variants_const, variants_def,
          all_concrete, all_total, all_def, Abs_name, Rep_name, case_result, defs, timer,
          variants_alt, ... } = info
    val phase = Simple_Word_Enum.phase timer
    val { case_const, case_def, match_def, index_def, ... } = case_result
    val uN = "u" ^ string_of_int width
    val to_name = type_name ^ "_to_" ^ uN ^ "_pure"
    val from_name = type_name ^ "_try_from_" ^ uN ^ "_pure"

    (* Specification.definition, as in define_const above, so that these conversions come out
       code-exportable without needing [code]. *)
    fun define name rhs lthy =
      let
        val binding = Binding.name name
        val ((_, (_, def_thm)), lthy) = Specification.definition
          (SOME (binding, NONE, NoSyn)) [] []
          ((Binding.name (name ^ "_def"), []),
           Logic.mk_equals (Free (name, fastype_of rhs), rhs)) lthy
        val const = Const (Local_Theory.full_name lthy binding, fastype_of rhs)
        val phi = Local_Theory.target_morphism lthy
      in ((const, Morphism.thm phi def_thm), lthy) end
    fun note name thm lthy =
      Local_Theory.note ((Binding.name name, []), [thm]) lthy |> apfst (the_single o snd)

    (* T_to_uN_pure e = case e of C1 => w1 | ... | Cn => wn.
       case_T comes in on the record, already at the right name; only its schematic result
       type needs instantiating to the word type. *)
    val e = Free ("e", absT)
    val case_const = Const (dest_Const_name case_const,
      funpow (length words) (fn T => wordT --> T) (absT --> wordT))
    val ((to_const, to_def), lthy) =
      define to_name (lambda e (list_comb (case_const, words @ [e]))) lthy

    (* T_to_uN_pure_alt: = of_nat (Rep e). Proved uniformly rather than by cases: unfolding the
       case chain turns the goal into `T_variants ! T_index e = of_nat (Rep e)`, and
       `variants_alt` rewrites T_variants to `map (of_nat o Rep) T_all`, at which point
       map_nth_find_index discharges it in one step given `e \<in> set T_all` (all_total). No case
       split, so the proof stays cheap: ~9ms at 64 variants, ~45ms at 256, i.e. the cost is
       just the term traversal.

       An earlier version did split on T_all_concrete into one goal per variant and reduced
       each with that variant's rep_eq. That was inherently linear and, worse, easy to make
       accidentally quadratic --- it needed the index equation and rep_eq selected per goal
       *and* nth-reduction rules, and got much slower if either was dropped (at 120 variants:
       5.4s with both, ~10s with neither, 22.9s with only the nth rules). The uniform proof
       makes all of that moot. *)
    val rep = Const (Rep_name, absT --> HOLogic.natT)
    val of_nat = Const (\<^const_name>\<open>of_nat\<close>, HOLogic.natT --> wordT)
    val alt_goal = HOLogic.mk_Trueprop
      (HOLogic.mk_eq (to_const $ e, of_nat $ (rep $ e)))
    val (to_alt, lthy) = phase (to_name ^ "_alt") (fn () =>
      let
        val to_alt = Goal.prove lthy ["e"] [] alt_goal (fn { context = ctxt, ... } =>
          simp_tac (ctxt addsimps [@{thm map_nth_find_index},
                  (* the case rewrite chain, from setup_case_for_typedef *)
                  case_def, match_def, index_def,
                  (* fold T_variants away in favour of T_all, which all_total is about *)
                  variants_alt, symmetric_thm OF [variants_def],
                  all_total, to_def]) 1)
      in note (to_name ^ "_alt") to_alt lthy end)

    (* T_try_from_uN_pure w = ncase w of w1 => Some C1 | ... | _ => None *)
    val w = Free ("w", wordT)
    val ((from_const, from_def), lthy) =
      define from_name (lambda w (mk_ncase wordT absT words variant_consts w)) lthy

    (* T_try_from_uN_pure_alt, via the generic simple_word_enum_ncase_alt: fold the literal
       clause list into the zip shape, then one rule application. Constant-size script. *)
    val abs = Const (Abs_name, HOLogic.natT --> absT)
    val unat = Const (\<^const_name>\<open>unsigned\<close>, wordT --> HOLogic.natT)
    val unitT = Type (\<^type_name>\<open>unit\<close>, [])
    val unit_el = Const (\<^const_name>\<open>Unity\<close>, unitT)
    val resultT = Type (\<^type_name>\<open>result\<close>, [absT, unitT])
    val ok_abs_unat = Const (\<^const_name>\<open>Ok\<close>, absT --> resultT) $ (abs $ (unat $ w))
    val from_alt_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (from_const $ w,
      \<^Const>\<open>If resultT\<close>
        $ (\<^Const>\<open>Set.member wordT\<close> $ w $ (\<^Const>\<open>set wordT\<close> $ variants_const))
        $ ok_abs_unat
        $ (Const (\<^const_name>\<open>Err\<close>, unitT --> resultT) $ unit_el)))
    val (from_alt, lthy) = phase (from_name ^ "_alt") (fn () =>
      let
        val from_alt = Goal.prove lthy ["w"] [] from_alt_goal (fn { context = ctxt, ... } =>
          let
            val enum_defs = Named_Theorems.get ctxt defs
            fun only thms = simp_tac (clear_simpset ctxt addsimps thms) 1
          in
            only ([from_def] @ enum_defs @ @{thms into_Some_None_snoc_map into_map[of Ok]})
            THEN only ([Thm.symmetric (Simpdata.mk_eq variants_def),
                        Thm.symmetric (Simpdata.mk_eq all_concrete)] @ enum_defs)
            THEN only (map (Thm.symmetric o Simpdata.mk_eq) enum_defs
                       @ [Thm.symmetric (Simpdata.mk_eq all_concrete), all_def])
            THEN only @{thms simple_word_enum_ncase_alt comp_apply}
          end)
      in note (from_name ^ "_alt") from_alt lthy end)

    (* Round trip: try_from (to e) = Ok e *)
    val round_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq
      (from_const $ (to_const $ e), Const (\<^const_name>\<open>Ok\<close>, absT --> resultT) $ e))
    (* Round trip. After rewriting by the two _alt lemmas the goal is about Abs/Rep of a
       variant word, so it needs Abs_inverse (from the typedef) and the fact that unat is
       injective on words --- both taken from the type_definition theorem we were handed
       rather than looked up by name. *)
    val type_definition = #type_definition info
    val (_, lthy) = phase (to_name ^ "_then_try_from") (fn () =>
      let
        val round = Goal.prove lthy ["e"] [] round_goal (fn { context = ctxt, ... } =>
          simp_tac (ctxt addsimps [to_alt, from_alt]) 1
          THEN (Method.insert_tac ctxt
                 [Thm.instantiate' [] [SOME (Thm.cterm_of ctxt e)] all_total] 1)
          THEN clarsimp_tac (ctxt addsimps
            (@{thms image_iff}
             @ [all_def, type_definition RS @{thm type_definition.Abs_inverse},
                type_definition RS @{thm type_definition.Rep}])) 1)
      in note (to_name ^ "_then_try_from") round lthy end)

    val _ = if not (#report info) then () else
      writeln ("  plugin word_conversion:\n" ^ cat_lines (map (prefix "    ")
        ["definition  " ^ to_name, "lemma       " ^ to_name ^ "_alt",
         "definition  " ^ from_name, "lemma       " ^ from_name ^ "_alt",
         "lemma       " ^ to_name ^ "_then_try_from"]))
  in lthy end

in

val word_conversion_plugin = Plugin_Name.declare_setup \<^binding>\<open>word_conversion\<close>

val _ = Theory.setup
  (Simple_Word_Enum.interpretation word_conversion_plugin generate_word_conversion)

end
\<close>

subsection\<open>Tests\<close>

experiment
begin

simple_word_enum (32) my_enum =
    Answer = \<open>0x42\<close>
  | Best   = \<open>0x72\<close>
  | Leet   = \<open>0x1337\<close>
  | Angry  = \<open>0x1066601\<close>

text\<open>The \<^verbatim>\<open>word_conversion\<close> plugin ran (it is on by default), so the conversion functions and
their characterisations are present without being asked for.\<close>

lemma
  shows \<open>my_enum_to_u32_pure Leet = 0x1337\<close>
    and \<open>my_enum_to_u32_pure e = of_nat (Rep_my_enum e)\<close>
  by (simp add: my_enum_to_u32_pure_def, rule my_enum_to_u32_pure_alt)

\<comment>\<open> TODO:
- make sure \<^theory>\<open>Misc.Case_for_Typedefs\<close> exports
  \<^term>\<open>case_my_enum\<close> and \<^term>\<open>match_my_enum\<close> with \<^verbatim>\<open>[code]\<close>
- emit an instantiation of \<^class>\<open>equal\<close>... as a plugin for
  simple words?
- emit a Rust variant of these as another plugin. initially,
  just use \<^verbatim>\<open>lift_fun1\<close>, can be replaced later. These should
  also allow a syntactic, constant time equality proof
\<close>

lemma
  shows \<open>my_enum_try_from_u32_pure 0x42 = Ok Answer\<close>
    and \<open>my_enum_try_from_u32_pure 0x99 = Err ()\<close>
  by (simp_all add: my_enum_try_from_u32_pure_alt my_enum_variants_def my_enum_defs)

lemma
  shows \<open>my_enum_try_from_u32_pure (my_enum_to_u32_pure e) = Ok e\<close>
  by (rule my_enum_to_u32_pure_then_try_from)

end

text\<open>The generated \<^verbatim>\<open>T_all_concrete [code]\<close> equation makes \<^verbatim>\<open>T_all\<close> executable. Checked outside
an \<^verbatim>\<open>experiment\<close>, as code generation needs the constants to be global.

Note that \<^verbatim>\<open>case_T\<close> itself is \<^emph>\<open>not\<close> executable: it goes through \<^const>\<open>find_index\<close>, which needs
equality on \<^verbatim>\<open>T\<close>, and neither this command nor \<^verbatim>\<open>setup_case_for_typedef\<close> provides an
\<^class>\<open>equal\<close> instance. Evaluating a \<^verbatim>\<open>case\<close> gives a wellsortedness error until one is
supplied. Reasoning about \<^verbatim>\<open>case\<close> is unaffected --- that goes through the simproc.\<close>

simple_word_enum (8) code_test_enum =
    CT_Zero = 0
  | CT_One  = 1
  | CT_Big  = \<open>0xff\<close>

value \<open>code_test_enum_all\<close>
value \<open>length code_test_enum_all\<close>

text\<open>A larger enum, to keep an eye on the cost of the generated proofs.\<close>

simple_word_enum (64) big_enum =
    B00 = 0    | B01 = 1    | B02 = 2    | B03 = 3    | B04 = 4
  | B05 = 5    | B06 = 6    | B07 = 7    | B08 = 8    | B09 = 9
  | B10 = 10   | B11 = 11   | B12 = 12   | B13 = 13   | B14 = 14
  | B15 = 15   | B16 = 16   | B17 = 17   | B18 = 18   | B19 = 19
  | B20 = 20   | B21 = 21   | B22 = 22   | B23 = 23   | B24 = 24
  | B25 = \<open>0xdeadbeef\<close> | B26 = \<open>0xcafe\<close> | B27 = \<open>0x1337\<close>
  | B28 = 10006660001 | B29 = 4294967296

text\<open>\<^verbatim>\<open>case\<close> reduction on a large enum goes through the simproc, so it costs a fixed number of
rewrites rather than a search over the 30 variants.\<close>

lemma
  shows \<open>(case B29 of B00 \<Rightarrow> 0 :: nat | B29 \<Rightarrow> 29 | _ \<Rightarrow> 1) = 29\<close>
    and \<open>(case B25 of B25 \<Rightarrow> True | _ \<Rightarrow> False)\<close>
  by simp_all

text\<open>Distinctness of two particular variants, via the generated index facts.\<close>

lemma
  shows \<open>B27 \<noteq> B25\<close>
  by (rule notI, drule arg_cong[where f=big_enum_index])
     (simp add: big_enum_indices_concrete)

text\<open>Timings for a single declaration are available by enabling
\<^verbatim>\<open>simple_word_enum_timing\<close>; the command then prints the phase breakdown, with each plugin's
sub-phases nested under \<^verbatim>\<open>plugins\<close>.\<close>

experiment
begin
declare [[simple_word_enum_timing]]

simple_word_enum (16) timed_enum = TE_A = 1 | TE_B = 2 | TE_C = 3

end

subsection\<open>Benchmarking\<close>

text\<open>\<^verbatim>\<open>simple_word_enum_benchmark\<close> declares one throwaway enum per requested size and prints a
comparison, so the cost of the generated definitions and proofs can be tracked as the variant
count grows:

\<^verbatim>\<open>simple_word_enum_benchmark (32) sizes: 1 10 50 100\<close>

Each size \<^verbatim>\<open>n\<close> gets an enum of \<^verbatim>\<open>n\<close> variants with values \<^verbatim>\<open>0, 1, ..., n-1\<close>. The declarations
are \<^emph>\<open>discarded\<close> --- the command times each one and then returns the theory it started from ---
so nothing is added to the enclosing theory, sizes may repeat, and every size is measured
against an identical starting context rather than one already carrying the previous sizes'
constants.

The plugin filter is accepted in the same position as for \<^verbatim>\<open>simple_word_enum\<close>, so
\<^verbatim>\<open>simple_word_enum_benchmark (plugins del: word_conversion) (32) sizes: 10 100\<close> measures the
command on its own.

Output is a per-size phase breakdown followed by a table of totals with the per-variant cost,
which is what shows whether a phase is linear or worse. Benchmarking is a measurement, so it
forces timing on regardless of \<^verbatim>\<open>simple_word_enum_timing\<close>.\<close>

ML \<open>
local

fun time_to_ms t = Time.toMilliseconds (#elapsed t)

(* Right-align in a fixed column, so the table lines up. *)
fun pad w s = if size s >= w then s else replicate_string (w - size s) " " ^ s

(* One synthetic enum of `n` variants: values 0 .. n-1 are distinct in any word type wide
   enough to hold them, which the width check below enforces. *)
fun bench_spec width n =
  let
    val base = "bench_" ^ string_of_int width ^ "_" ^ string_of_int n
    val variants = map (fn i =>
      (Binding.name (base ^ "_V" ^ string_of_int i), string_of_int i)) (0 upto n - 1)
  in (Binding.name base, variants) end

fun benchmark_cmd ((raw_filter, width), sizes) lthy =
  let
    val _ = if null sizes then error "simple_word_enum_benchmark: no sizes given" else ()
    val _ = case filter (fn n => n < 1) sizes of
        [] => ()
      | bad => error ("simple_word_enum_benchmark: sizes must be positive, got " ^
          commas (map string_of_int bad))
    (* The synthetic values are 0 .. n-1, so the word type has to be able to tell them
       apart; otherwise the generated distinctness proof would fail confusingly. *)
    val _ = case filter (fn n => IntInf.pow (2, width) < n) sizes of
        [] => ()
      | bad => error ("simple_word_enum_benchmark: " ^ string_of_int width ^
          " word cannot hold " ^ commas (map string_of_int bad) ^ " distinct values")

    (* Each size is declared into --- and then discarded from --- the *same* starting context:
       we keep the timer and throw the resulting local_theory away. That leaves no trace of the
       throwaway enums (so sizes may repeat, here and across invocations, and nothing pollutes
       the enclosing theory), and it also keeps the measurements comparable, since every size
       is measured against an identical context rather than one already carrying the previous
       sizes' constants. One live timer per size keeps their breakdowns separate. *)
    fun run_size n =
      let
        val timer = Simple_Word_Enum.new_timer true
        val (type_binding, variants) = bench_spec width n
        (* No uRust name: the benchmark enums are throwaway, and a notation registration
           would be a global side effect surviving the discarded local theory. *)
        val _ = Simple_Word_Enum.simple_word_enum_core
          { timer = timer, report = false }
          (raw_filter, width, type_binding, NONE, variants) lthy
      in (n, timer) end
    val results = map run_size sizes

    (* Per-size breakdown, then a totals table. The per-variant column is the interesting
       one: flat means linear in the variant count, growing means worse than linear. *)
    val breakdowns = map (fn (n, timer) =>
      Simple_Word_Enum.format_timer_report
        (string_of_int n ^ " variants (" ^ Timing.message (Simple_Word_Enum.timer_total timer)
         ^ " total):") timer) results
    val header = pad 8 "variants" ^ pad 12 "total (ms)" ^ pad 14 "per variant" ^
      "   slowest phase"
    fun row (n, timer) =
      let
        val total = time_to_ms (Simple_Word_Enum.timer_total timer)
        val per = Real.fmt (StringCvt.FIX (SOME 2))
          (Real.fromInt total / Real.fromInt n)
        val slowest = Simple_Word_Enum.timer_entries timer
          |> filter (fn (d, _, _) => d = 0)
          |> sort (fn ((_, _, a), (_, _, b)) => Time.compare (#elapsed b, #elapsed a))
          |> (fn [] => "-" | (_, name, t) :: _ => name ^ " (" ^
                string_of_int (time_to_ms t) ^ "ms)")
      in pad 8 (string_of_int n) ^ pad 12 (string_of_int total) ^ pad 14 per ^
         "   " ^ slowest end
    val _ = writeln (cat_lines
      ("simple_word_enum_benchmark (" ^ string_of_int width ^ " word), sizes " ^
         commas (map string_of_int sizes) ^ ":"
       :: breakdowns
       @ ["", header] @ map row results))
  in lthy end

in

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>simple_word_enum_benchmark\<close>
    "declare throwaway enums of the given sizes and report their generation timings"
    (Scan.optional
       (Scan.ahead (Parse.$$$ "(" -- Parse.reserved "plugins") |--
         (Parse.$$$ "(" |-- Plugin_Name.parse_filter --| Parse.$$$ ")"))
       (K Plugin_Name.default_filter) --
      (Parse.$$$ "(" |-- Parse.nat --| Parse.$$$ ")") --
      (Parse.reserved "sizes" |-- Parse.$$$ ":" |-- Scan.repeat1 Parse.nat)
     >> benchmark_cmd)

end
\<close>

text\<open>To track how the cost grows with the variant count, \<^verbatim>\<open>simple_word_enum_benchmark\<close> declares
one throwaway enum per size, times it, and discards it. Kept small here so the theory stays
quick to check --- raise the sizes when actually investigating a regression.

The interesting column is the per-variant cost: it should stay roughly flat. It was \<^emph>\<open>not\<close> flat
when this was written --- 31.5ms/variant at 20 rising to 85ms at 120 --- which is how the
quadratic behaviour in the original \<^verbatim>\<open>to_uN_pure_alt\<close> tactic was found; that proof is now
uniform rather than by cases, and costs ~9ms at 64 variants. What dominates instead is
\<^verbatim>\<open>variants\<close> (the \<^verbatim>\<open>distinct\<close> proof, whose goal is quadratic in the variant count) together with
\<^verbatim>\<open>variant_consts\<close> (one \<^verbatim>\<open>lift_definition\<close> per variant). Around 25ms/variant through 64, rising
past that: 33ms at 128 and 49ms at 256.\<close>

simple_word_enum_benchmark (32) sizes: 4 16 32 64 (* 128 should take about 2s*)

subsection\<open>The \<^verbatim>\<open>generate_debug\<close> plugin\<close>

text\<open>Generates the \<^class>\<open>generate_debug\<close> instance for the enum, rendering each variant as its
own name:

\<^verbatim>\<open>generate_debug Leet = [str ''Leet'']\<close>

Concretely, for the type \<^verbatim>\<open>T\<close> with variants \<^verbatim>\<open>C1, ..., Cn\<close> the plugin emits what a hand-written

\<^verbatim>\<open>instantiation T :: generate_debug
begin
  definition generate_debug_T :: \<open>T \<Rightarrow> log_data\<close> where
    \<open>generate_debug_T e \<equiv> [str (case e of C1 \<Rightarrow> ''C1'' | ... | Cn \<Rightarrow> ''Cn'')]\<close>
  instance ..
end\<close>

would. The \<^verbatim>\<open>case\<close> arms carry the names rather than whole \<^verbatim>\<open>log_data\<close> lists, so that the term
holds one \<^const>\<open>str\<close> application instead of \<^verbatim>\<open>n\<close> of them. No per-variant equations are
generated: \<^verbatim>\<open>generate_debug_T_def\<close> plus the case simproc reduces a concrete variant in a fixed
number of rewrites, so a fact per variant would buy nothing.

The instance is added to the \<^emph>\<open>background\<close> theory: type classes are global, so the instance
must be, even when the declaration itself sits in a local target such as an \<^verbatim>\<open>experiment\<close>.

The plugin is registered under the name \<^verbatim>\<open>generate_debug\<close> and runs by default; suppress it
with \<^verbatim>\<open>simple_word_enum (plugins del: generate_debug) ...\<close>.\<close>

ML \<open>
local

val log_entryT = \<^typ>\<open>log_entry\<close>
val log_dataT = HOLogic.listT log_entryT
val str_const = Const (\<^const_name>\<open>str\<close>, HOLogic.stringT --> log_entryT)

fun generate_generate_debug (info: Simple_Word_Enum.enum_info) lthy =
  let
    val { absT, variant_bindings, case_result, timer, ... } = info
    fun phase name f = Simple_Word_Enum.phase timer name f
    val names = map Binding.name_of variant_bindings
    val n = length names
    val tyco = dest_Type_name absT
    (* `generate_debug_T`, the name the class gives the parameter at this type. *)
    val def_name = "generate_debug_" ^ Long_Name.base_name tyco

    (* [str (case_T ''C1'' ... ''Cn'' e)]. case_T arrives on the record already at the right
       name; only its schematic result type needs instantiating, here to `char list`. *)
    val e = Free ("e", absT)
    val case_const = Const (dest_Const_name (#case_const case_result),
      funpow n (fn T => HOLogic.stringT --> T) (absT --> HOLogic.stringT))
    val body = HOLogic.mk_list log_entryT
      [str_const $ list_comb (case_const, map HOLogic.mk_string names @ [e])]

    (* The LHS is written with the overloaded constant; `Syntax.check_term` inside the
       instantiation rewrites it to the local parameter, so the mangled name never has to be
       spelled out here (the Class.instantiation idiom, cf. code_evaluation.ML). *)
    val raw_eq = Logic.mk_equals
      (Const (\<^const_name>\<open>generate_debug\<close>, absT --> log_dataT) $ e, body)

    val lthy = phase "generate_debug_instance" (fn () =>
      let
        (* The instance goes into the background theory, so the fact it declares there is not
           reliably reachable from the target the declaration appeared in --- and which
           namespace it lands in differs between a fresh declaration and the retro-application
           the plugin mechanism performs on already-declared enums when this plugin is
           registered. So the background fact gets a concealed name of its own, and the
           exported theorem is noted into the local target below, the way the other plugins
           note theirs. *)
        val (def_thm, lthy) = Local_Theory.background_theory_result (fn thy =>
          thy
          |> Class.instantiation ([tyco], [], \<^sort>\<open>generate_debug\<close>)
          |> (fn ilthy =>
                Specification.definition NONE [] []
                  ((Binding.concealed (Binding.name (def_name ^ "_raw_def")), []),
                   Syntax.check_term ilthy raw_eq) ilthy
                |> apfst (snd o snd))
          |-> Class.prove_instantiation_exit_result Morphism.thm
                (fn ctxt => fn _ => Class.intro_classes_tac ctxt [])) lthy
      in
        snd (Local_Theory.note ((Binding.name (def_name ^ "_def"), []), [def_thm]) lthy)
      end)

    val _ = if not (#report info) then () else
      writeln ("  plugin generate_debug:\n" ^ cat_lines (map (prefix "    ")
        ["instance    " ^ Long_Name.base_name tyco ^ " :: generate_debug",
         "definition  " ^ def_name,
         "lemma       " ^ def_name ^ "_def"]))
  in lthy end

in

val generate_debug_plugin = Plugin_Name.declare_setup \<^binding>\<open>generate_debug\<close>

val _ = Theory.setup
  (Simple_Word_Enum.interpretation generate_debug_plugin generate_generate_debug)

end
\<close>

subsection\<open>Tests for the \<^verbatim>\<open>generate_debug\<close> plugin\<close>

experiment
begin

simple_word_enum (16) colour =
    Red   = 1
  | Green = 2
  | Blue  = \<open>0xbee\<close>

text\<open>The instance is there, and each variant renders as its own name --- unfolding the
definition leaves a \<^verbatim>\<open>case\<close> on a concrete variant, which the case simproc reduces.\<close>

lemma
  shows \<open>generate_debug Red = [str ''Red'']\<close>
    and \<open>generate_debug Green = [str ''Green'']\<close>
    and \<open>generate_debug Blue = [str ''Blue'']\<close>
  by (simp_all add: generate_debug_colour_def)

text\<open>Being a \<^class>\<open>generate_debug\<close> instance, the type composes with the other instances.\<close>

lemma
  shows \<open>generate_debug [Red, Blue] =
           [str ''['', str ''Red'', str '', '', str ''Blue'', str '']'']\<close>
  by (simp add: generate_debug_list_def generate_debug_colour_def)

lemma
  shows \<open>generate_debug (Green, True) =
           [str ''('', str ''Green'', str '', '', LogBool True, str '')'']\<close>
  by (simp add: generate_debug_prod_def generate_debug_bool_def
        generate_debug_colour_def)

text\<open>\<^verbatim>\<open>plugins del:\<close> suppresses just this plugin, leaving \<^verbatim>\<open>word_conversion\<close> in place.\<close>

simple_word_enum (plugins del: generate_debug) (16) quiet_colour =
    QRed = 1 | QBlue = 2

lemma
  shows \<open>quiet_colour_try_from_u16_pure 1 = Ok QRed\<close>
  by (simp add: quiet_colour_try_from_u16_pure_alt quiet_colour_variants_def
        quiet_colour_defs)

end

subsection\<open>The \<^verbatim>\<open>variant_equality\<close> plugin\<close>

text\<open>Registers a simproc deciding \<^verbatim>\<open>Ci = Cj\<close> on concrete variants: \<^verbatim>\<open>True\<close> when they are the
same variant, \<^verbatim>\<open>False\<close> when they differ. Without it, \<^verbatim>\<open>Red = Blue\<close> is not something \<^verbatim>\<open>simp\<close> can
settle --- the generated \<^verbatim>\<open>T_all_distinct\<close> says the variants are pairwise distinct, but getting
from that to a particular pair takes the \<^verbatim>\<open>T_index\<close> detour spelled out by hand in the tests
above.

The decision procedure is the same trick that detour uses, and the simproc is built the way
the \<^verbatim>\<open>case_T\<close> one in \<^theory>\<open>Misc.Case_for_Typedefs\<close> is: a fixed chain of \<^ML>\<open>Conv.rewr_conv\<close>
steps rather than a recursive simplifier call. \<^verbatim>\<open>T_index\<close> is injective on variants, so applying
it to both sides of \<^verbatim>\<open>Ci = Cj\<close> and reducing by \<^verbatim>\<open>T_indices_concrete\<close> leaves \<^verbatim>\<open>i = j\<close> on
numerals, which decides itself. Cost is independent of the variant count: two index lookups and
one numeral comparison, no search over the \<^verbatim>\<open>n\<close> variants and no \<^verbatim>\<open>n\<^sup>2\<close> distinctness facts.

The plugin is registered under the name \<^verbatim>\<open>variant_equality\<close> and runs by default; suppress it
with \<^verbatim>\<open>simple_word_enum (plugins del: variant_equality) ...\<close>.\<close>

ML \<open>
local

fun mk_variant_eq_simproc absT type_name (info: Simple_Word_Enum.enum_info) =
  let
    (* The `T_index` constant, taken off the index definition rather than resolved by name. *)
    val index_const = #index_def (#case_result info)
      |> Thm.prop_of |> Logic.dest_equals |> fst |> head_of
    val indices_name = type_name ^ "_indices_concrete"
    (* `arg_cong` with its function fixed to `T_index`: from `Ci = Cj` derive
       `T_index Ci = T_index Cj`. arg_cong's schematics are (x, y, f) in order, so only the
       third is instantiated. *)
    fun arg_cong_index ctxt =
      Drule.infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt index_const)]
        @{thm arg_cong}
    (* Pattern for the simplifier's term net: ?x = ?y at the enum type. *)
    val lhs_pattern = HOLogic.mk_eq (Var (("x", 0), absT), Var (("y", 0), absT))
  in
    {passive = false, name = Binding.name (type_name ^ "_eq_simproc"),
     kind = Simplifier.Simproc,
     lhss = [lhs_pattern],
     proc = fn _ => fn ctxt => fn ct =>
       let
         val (lhs, rhs) = HOLogic.dest_eq (Thm.term_of ct)
       in
         (* Only fire on two concrete variant constants of this type: on a variable the
            equality has to stay as it is. *)
         (case (lhs, rhs) of
           (Const (_, T1), Const (_, T2)) =>
             if T1 <> absT orelse T2 <> absT then NONE
             else if lhs aconv rhs then
               (* Same variant: reflexivity, no index reasoning needed. *)
               SOME (Thm.instantiate' [SOME (Thm.ctyp_of ctxt absT)]
                 [SOME (Thm.cterm_of ctxt lhs)] @{thm HOL.refl}
                 RS @{thm Eq_TrueI})
             else
               let
                 val idx_thms = Proof_Context.get_thms ctxt indices_name
                 (* `Ci \<noteq> Cj` the way the by-hand tests prove it: push T_index through the
                    (assumed) equation, reduce both sides by T_indices_concrete, and the
                    resulting `i = j` on numerals is false. Constant work per firing bar the
                    single simp over the index facts. *)
                 val neq = Goal.prove ctxt [] []
                   (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (lhs, rhs))))
                   (fn { context = c, ... } =>
                      resolve_tac c @{thms notI} 1
                      THEN dresolve_tac c [arg_cong_index c] 1
                      THEN asm_full_simp_tac (clear_simpset c addsimps
                        (idx_thms @ @{thms eq_numeral_simps rel_simps simp_thms})) 1)
               in SOME (neq RS @{thm Eq_FalseI}) end
         | _ => NONE)
         handle TERM _ => NONE | THM _ => NONE | CTERM _ => NONE
             | ERROR _ => NONE
       end,
     identifier = []}
     : (term, Morphism.morphism -> Proof.context -> cterm -> thm option, thm list)
       Simplifier.simproc_spec
  end

fun generate_variant_equality (info: Simple_Word_Enum.enum_info) lthy =
  let
    val { absT, type_name, timer, ... } = info
    fun phase name f = Simple_Word_Enum.phase timer name f

    val lthy = phase "variant_equality_simproc" (fn () =>
      snd (Simplifier.define_simproc (mk_variant_eq_simproc absT type_name info) lthy))

    val _ = if not (#report info) then () else
      writeln ("  plugin variant_equality:\n" ^ cat_lines (map (prefix "    ")
        ["simproc     " ^ type_name ^ "_eq_simproc [active]"]))
  in lthy end

in

val variant_equality_plugin = Plugin_Name.declare_setup \<^binding>\<open>variant_equality\<close>

val _ = Theory.setup
  (Simple_Word_Enum.interpretation variant_equality_plugin generate_variant_equality)

end
\<close>

subsection\<open>Tests for the \<^verbatim>\<open>variant_equality\<close> plugin\<close>

experiment
begin

simple_word_enum (16) fruit =
    Apple  = 1
  | Pear   = 2
  | Cherry = \<open>0xf00\<close>

text\<open>Equalities and disequalities between concrete variants are decided by \<^verbatim>\<open>simp\<close> alone ---
compare the \<^verbatim>\<open>big_enum\<close> test above, which had to go through \<^verbatim>\<open>big_enum_index\<close> by hand.\<close>

lemma
  shows \<open>Apple \<noteq> Pear\<close> and \<open>Pear \<noteq> Cherry\<close> and \<open>Apple \<noteq> Cherry\<close>
    and \<open>Apple = Apple\<close> and \<open>Cherry = Cherry\<close>
  by simp_all

text\<open>Both orientations, and under a negation.\<close>

lemma
  shows \<open>(Cherry = Apple) = False\<close> and \<open>\<not> (Pear = Apple)\<close>
    and \<open>(Apple = Pear \<or> Pear = Pear)\<close>
  by simp_all

text\<open>An equality on a \<^emph>\<open>variable\<close> is left alone --- the simproc only fires on two concrete
variants, so nothing is decided prematurely.\<close>

lemma
  assumes \<open>e = Apple\<close>
  shows \<open>e \<noteq> Pear\<close>
  using assms by simp

lemma
  assumes \<open>e \<noteq> Apple\<close>
  shows \<open>\<not> (e = Apple)\<close>
  using assms by simp

text\<open>It composes: deciding variant equality makes \<^const>\<open>distinct\<close> and list membership on
literal variant lists go through by \<^verbatim>\<open>simp\<close> too.\<close>

lemma
  shows \<open>distinct [Apple, Pear, Cherry]\<close>
    and \<open>Pear \<in> set [Apple, Pear]\<close>
    and \<open>Cherry \<notin> set [Apple, Pear]\<close>
  by simp_all

text\<open>\<^verbatim>\<open>plugins del:\<close> suppresses just this plugin. Without it the disequality is not decided by
\<^verbatim>\<open>simp\<close>, and the \<^verbatim>\<open>T_index\<close> detour is needed --- which is exactly what the plugin automates.\<close>

simple_word_enum (plugins del: variant_equality) (16) plain_fruit =
    PApple = 1 | PPear = 2

lemma
  shows \<open>PApple \<noteq> PPear\<close>
  by (rule notI, drule arg_cong[where f=plain_fruit_index])
     (simp add: plain_fruit_indices_concrete)

end

subsection\<open>The \<^verbatim>\<open>equal_instance\<close> plugin\<close>

text\<open>Emits the \<^class>\<open>equal\<close> instance for the enum, defined through the representation:

\<^verbatim>\<open>equal_T x y \<equiv> Rep_T x = Rep_T y\<close>

which is correct by \<^verbatim>\<open>Rep_T_inject\<close>, so the \<^verbatim>\<open>instance\<close> proof is a fixed two steps regardless of
the variant count.

This is what makes \<^verbatim>\<open>case\<close> expressions on the type \<^emph>\<open>code-exportable\<close>. \<^verbatim>\<open>case_T\<close> reduces through
\<^verbatim>\<open>match_T\<close> to \<^const>\<open>find_index\<close>, which needs equality on \<^verbatim>\<open>T\<close>; without an instance,
\<^verbatim>\<open>export_code\<close> on any function containing such a \<^verbatim>\<open>case\<close> fails with

\<^verbatim>\<open>Wellsortedness error (in code equation T_index ?x \<equiv> find_index T_all ?x,
 with dependency "f" -> "case_T" -> "match_T" -> "T_index"):
 Type T not of sort equal\<close>

Note what that message shows: the code generator already has equations for \<^verbatim>\<open>case_T\<close>, \<^verbatim>\<open>match_T\<close>
and \<^verbatim>\<open>T_index\<close> --- \<^verbatim>\<open>Specification.definition\<close> attaches a default code equation to every \<^verbatim>\<open>_def\<close>
fact it notes (\<^verbatim>\<open>Code.singleton_default_equation_attrib\<close>, specification.ML), and
\<^verbatim>\<open>setup_case_for_typedef\<close> defines all three that way. So no \<^verbatim>\<open>[code]\<close> declarations are needed for
them; the missing \<^class>\<open>equal\<close> instance is the only obstacle. (By contrast \<^verbatim>\<open>T_all_concrete\<close> does
carry an explicit \<^verbatim>\<open>[code]\<close>: it is a \<^verbatim>\<open>lemma\<close>, not a definition.)

This is a plugin rather than part of \<^verbatim>\<open>setup_case_for_typedef\<close> because that command runs on an
\<^emph>\<open>existing\<close> \<^verbatim>\<open>typedef\<close>, which may well already be a \<^class>\<open>equal\<close> instance --- and a class instance
is global and unconditional, so emitting one there would hard-fail on such a type.
\<^verbatim>\<open>simple_word_enum\<close> creates the \<^verbatim>\<open>typedef\<close> itself, so it knows the slot is free. Suppress with
\<^verbatim>\<open>simple_word_enum (plugins del: equal_instance) ...\<close> for a type that wants a different
equality.\<close>

ML \<open>
local

fun generate_equal_instance (info: Simple_Word_Enum.enum_info) lthy =
  let
    val { absT, Rep_name, type_definition, timer, ... } = info
    fun phase name f = Simple_Word_Enum.phase timer name f
    val tyco = dest_Type_name absT
    val def_name = "equal_" ^ Long_Name.base_name tyco

    (* equal x y \<equiv> Rep_T x = Rep_T y. As in the generate_debug plugin, the LHS is written with
       the overloaded constant and `Syntax.check_term` inside the instantiation rewrites it to
       the local parameter, so the mangled name is never spelled out here. *)
    val rep = Const (Rep_name, absT --> HOLogic.natT)
    val x = Free ("x", absT)
    val y = Free ("y", absT)
    (* The class parameter is `equal_class.equal`; \<^const_name>\<open>equal\<close> does not resolve from
       here, as the class's own namespace is not open in this theory. *)
    val equal_const = Const ("HOL.equal_class.equal", absT --> absT --> HOLogic.boolT)
    val raw_eq = Logic.mk_equals (equal_const $ x $ y, HOLogic.mk_eq (rep $ x, rep $ y))

    val lthy = phase "equal_instance" (fn () =>
      let
        (* Class instances are global, so this goes into the background theory; the fact it
           declares there is not reliably reachable from the declaration's target, so it gets a
           concealed name and the exported theorem is noted below. Same reasoning as the
           generate_debug plugin --- see the comment there. *)
        val (def_thm, lthy) = Local_Theory.background_theory_result (fn thy =>
          thy
          |> Class.instantiation ([tyco], [], \<^sort>\<open>equal\<close>)
          |> (fn ilthy =>
                Specification.definition NONE [] []
                  ((Binding.concealed (Binding.name (def_name ^ "_raw_def")), []),
                   Syntax.check_term ilthy raw_eq) ilthy
                |> apfst (snd o snd))
          |-> (fn def_thm =>
                Class.prove_instantiation_exit_result Morphism.thm
                  (* equal_eq: equal x y \<longleftrightarrow> x = y. Unfold the definition and close by
                     Rep_T_inject, which the typedef provides. *)
                  (fn ctxt => fn def_thm =>
                     Class.intro_classes_tac ctxt []
                     THEN ALLGOALS (simp_tac (clear_simpset ctxt addsimps
                       [def_thm, type_definition RS @{thm type_definition.Rep_inject}])))
                  def_thm)) lthy
      in
        snd (Local_Theory.note ((Binding.name (def_name ^ "_def"), []), [def_thm]) lthy)
      end)

    val _ = if not (#report info) then () else
      writeln ("  plugin equal_instance:\n" ^ cat_lines (map (prefix "    ")
        ["instance    " ^ Long_Name.base_name tyco ^ " :: equal",
         "definition  " ^ def_name,
         "lemma       " ^ def_name ^ "_def"]))
  in lthy end

in

val equal_instance_plugin = Plugin_Name.declare_setup \<^binding>\<open>equal_instance\<close>

val _ = Theory.setup
  (Simple_Word_Enum.interpretation equal_instance_plugin generate_equal_instance)

end
\<close>

subsection\<open>Tests for the \<^verbatim>\<open>equal_instance\<close> plugin\<close>

text\<open>Kept global rather than in an \<^verbatim>\<open>experiment\<close>: code generation needs the constants to be
global, and a class instance is global anyway.\<close>

simple_word_enum (8) light = Red = 0 | Amber = 1 | Green = 2

text\<open>The instance is there and decides equality by evaluation, not just by the simproc.\<close>

lemma
  shows \<open>equal_class.equal Red Red\<close> and \<open>\<not> equal_class.equal Red Green\<close>
  by (simp_all add: equal_light_def light_rep_defs)

value \<open>Red = Red\<close>
value \<open>Red = Green\<close>

text\<open>The payoff: a \<^verbatim>\<open>case\<close> on the type is now code-exportable. Without the instance this fails
with the wellsortedness error quoted above.\<close>

definition light_delay :: \<open>light \<Rightarrow> nat\<close> where
  \<open>light_delay l \<equiv> case l of Red \<Rightarrow> 30 | Amber \<Rightarrow> 3 | Green \<Rightarrow> 25\<close>

value \<open>light_delay Red\<close>
value \<open>light_delay Amber\<close>
value \<open>light_delay Green\<close>

export_code light_delay in OCaml module_name Light
export_code light_delay in SML module_name Light

text\<open>The other generated constants are exportable too, without any \<^verbatim>\<open>[code]\<close> declaration in the
command: they are defined via \<^verbatim>\<open>Specification.definition\<close>, which attaches a default code
equation.\<close>

export_code light_variants light_all light_to_u8_pure light_try_from_u8_pure
  in OCaml module_name LightAll

value \<open>light_to_u8_pure Amber\<close>
value \<open>light_try_from_u8_pure 2\<close>
value \<open>light_try_from_u8_pure 9\<close>

text\<open>\<^verbatim>\<open>T_all\<close> generates from \<^verbatim>\<open>T_all_concrete\<close>'s literal list, \<^emph>\<open>not\<close> from its own definition: the
default equation \<^verbatim>\<open>Specification.definition\<close> attached would go through \<^const>\<open>Abs_light\<close> and
\<^const>\<open>unat\<close>, and the explicit \<^verbatim>\<open>[code]\<close> supersedes it. \<^verbatim>\<open>T_variants\<close>, which has no better
equation, keeps its default one.\<close>

ML \<open>
  let
    fun eqns_of c =
      Code.equations_of_cert @{theory} (Code.get_cert @{context} [] c)
      |> snd |> the_default []
      |> map (fn ((_, (_, rhs)), _) => Syntax.string_of_term @{context} rhs)
    val all_eqns = eqns_of \<^const_name>\<open>light_all\<close>
    val variants_eqns = eqns_of \<^const_name>\<open>light_variants\<close>
  in
    writeln ("light_all: " ^ commas all_eqns);
    writeln ("light_variants: " ^ commas variants_eqns);
    (* T_all_concrete won: no Abs_light / unat in the equation actually used. *)
    @{assert} (not (exists (String.isSubstring "Abs_light") all_eqns));
    @{assert} (not (exists (String.isSubstring "light_variants") all_eqns));
    writeln "CONFIRMED: T_all_concrete [code] superseded the default equation"
  end
\<close>

text\<open>\<^verbatim>\<open>plugins del: equal_instance\<close> suppresses it, for a type that wants a different equality.
Such a type keeps everything else, but a \<^verbatim>\<open>case\<close> on it is then not exportable.\<close>

simple_word_enum (plugins del: equal_instance) (8) unequal_light =
    UL_Red = 0 | UL_Green = 1

ML \<open>
  let
    val has_instance = Sorts.has_instance (Sign.classes_of @{theory})
      \<^type_name>\<open>unequal_light\<close> \<^sort>\<open>equal\<close>
  in
    @{assert} (not has_instance);
    writeln "plugins del: equal_instance --- no equal instance emitted"
  end
\<close>

lemma
  shows \<open>UL_Red \<noteq> UL_Green\<close>
  by simp

text\<open>All plugins are registered by the time we get here, so this run --- unlike the one above,
which predates them --- covers the full set. \<^verbatim>\<open>generate_debug\<close> is a single \<^verbatim>\<open>instantiation\<close> per
enum, but its defining term carries one \<^verbatim>\<open>case\<close> arm per variant, so it comes out linear at roughly
6ms/variant (29ms at 4 variants, 389ms at 64) --- enough to make \<^verbatim>\<open>plugins\<close> the largest phase on a
small enum. \<^verbatim>\<open>variant_equality\<close> only registers a simproc and \<^verbatim>\<open>equal_instance\<close> is one
\<^verbatim>\<open>instantiation\<close> whose defining term does not mention the variants, so both are constant.\<close>

simple_word_enum_benchmark (32) sizes: 4 16 32 64

end
