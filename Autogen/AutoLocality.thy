(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory AutoLocality
  imports Main
    AutoCommon
    AutoLens
    "HOL-Library.Datatype_Records"
  keywords "locality_lemma" "locality_init"
    "locality_check" "print_locality_data" :: thy_goal
      and "footprint" :: quasi_command
begin

ML_file "AutoLocality_Instrumentation.ML"

section\<open>Implementation guide\<close>

text\<open>
This section documents the implementation of AutoLocality. It assumes that
the reader already knows the user-facing problem and commands; that
motivation is in \<^file>\<open>README.md\<close>. The implementation can be
understood backwards from its runtime entry point:

\<^enum> the simplifier sees a term matching a locality dispatcher simproc;
\<^enum> the simproc looks up footprint metadata in the current proof context;
\<^enum> the lookup finds the footprint declaration whose record type,
  function shape, record-argument position, and applied prefix match the term;
\<^enum> the cancellation planner uses the registration certificates to
  construct the needed intermediate rewrites; and
\<^enum> the simproc returns one kernel-checked equality to the simplifier.

Here, a certificate means an ordinary Isabelle theorem already proved during
registration. It justifies one local fact about the registered function:
field-update equations for an operation, disjoint field-projection equations,
or the theorem that an attribute is unchanged by updates outside its
footprint. The simproc combines these stored theorems to construct and prove
the larger rewrite returned to the simplifier.

The important design choice is that the theory stores footprint metadata and
these per-registration certificate theorems, not a theorem for every possible
pair of operations. Pairwise commutativity and cancellation theorems are
derived only when a concrete simplifier invocation needs them.
\<close>

subsection\<open>Runtime architecture\<close>

text\<open>
An operation changes a record and an attribute observes a record. Both are
registered with a footprint. The registration command is the declaration-time
front end; the cancellation simproc is the runtime back end.

The runtime path is:

\<^enum> A declaration creates a typed \<^verbatim>\<open>locality_entry\<close>. It contains
  the canonical operational key, the constant and record identities, the
  footprint, record-field metadata, and the certificate the declaration
  proved.
\<^enum> The entry is inserted into the proof context. The context also receives
  secondary indexes containing only operational keys, never theorem payloads.
\<^enum> The declaration ensures that the relevant generic dispatcher simproc
  exists in the local simpset. A dispatcher is selected by the head constant
  and its full application arity.
\<^enum> During simplification, Isabelle invokes that dispatcher only for its
  syntactic trigger. The dispatcher receives the current proof context and
  the matched certified term.
\<^enum> The dispatcher ranks and validates candidates, plans hoisting and
  cancellation, proves the resulting equality, and returns the theorem as a
  rewrite. If the term is malformed or no safe rewrite applies, it returns
  \<^verbatim>\<open>NONE\<close>.

Thus the simpset contains small pattern-triggered ML procedures, while the
proof context contains the data those procedures consult. The simpset does
not contain a quadratic table of pre-generated pairwise theorems.
\<close>

subsection\<open>Proof-context storage\<close>

text\<open>
The following are the main persistent storage entities.

\<^enum> \<^verbatim>\<open>RecordLocalityData\<close> is the authoritative
  \<^verbatim>\<open>Generic_Data\<close> table. Its key is a structural
  \<^verbatim>\<open>locality_operational_key\<close>; its value is the complete
  \<^verbatim>\<open>locality_entry\<close>, including certificates.
\<^enum> \<^verbatim>\<open>LocalitySecondaryIndex\<close> is a second
  \<^verbatim>\<open>Generic_Data\<close> value. Its
  \<^verbatim>\<open>locality_secondary_index\<close> contains record indexes,
  constant-name indexes, replay-slot indexes, family paths, and dispatcher
  paths. These tables store key sets only. A selected key is resolved through
  \<^verbatim>\<open>RecordLocalityData\<close>.
\<^enum> \<^verbatim>\<open>LocalityDispatcherInventory\<close> is a third
  \<^verbatim>\<open>Generic_Data\<close> value. It records which local named simproc
  belongs to each dispatcher family. It stores the source name, a canonical
  alias, and an origin stamp, but no theorem payload.
\<^enum> The named theorem bundles created for each record contain the
  declaration-time field facts and certificates used by the proof routines.
  They are ordinary proof-context theorem collections, not a replacement for
  the typed registry.

The operational key records the dimensions needed for safe lookup: record
type, entry kind, canonical typed pattern, flexible-prefix information,
partial-application depth, and record-argument slot. This prevents a
polymorphic or locale-flexible registration from using another registration's
certificates.
\<close>

subsection\<open>Registration and simpset lifecycle\<close>

text\<open>
Registration first proves the footprint claim. A footprint is the list of
record fields that the function may read or change. For an operation, the
registration produces ordinary Isabelle theorem certificates for field
updates, field commutation, and disjoint projection. For an attribute, it
produces the theorem that updates outside the footprint do not change the
attribute's result. If these proofs do not close, the entry is not installed.

After the entry is stored, the declaration computes its dispatcher family.
Attribute dispatchers are keyed by the head constant and full application
arity. The command creates one generic simproc with a generated, stable
name, then records that name in \<^verbatim>\<open>LocalityDispatcherInventory\<close>.
The procedure closes over only its dispatcher key; it reads registrations
from the invocation's proof context.

The default simplifier contains the local dispatchers. The
\<^verbatim>\<open>locality_no_cancel\<close> attribute changes the configuration
flag \<^verbatim>\<open>locality_cancel_enabled\<close> to false. The
\<^verbatim>\<open>locality_cancel\<close> attribute sets it to true and restores any
missing local dispatcher procedures to the current simpset. This restoration
is needed because \<^verbatim>\<open>simp only\<close> starts from a restricted simpset
and removes ambient procedures. The attribute checks that each expected
dispatcher is present exactly once and has the expected trigger family.

Locale interpretation and context merge transport the registry, indexes,
and dispatcher inventory as proof-context data. Merging equal registrations
chooses a deterministic representative. Merging incompatible entries or
independently allocated dispatcher families raises an error. No process-global
simpset or theorem cache is used.
\<close>

subsection\<open>How the simproc derives a cancellation rewrite\<close>

text\<open>
The main callback is
\<^verbatim>\<open>locality_cancellation_simproc_for_dispatch\<close>. Its input is a
term at the simproc's syntactic trigger. The callback performs these steps:

\<^enum> It checks the configuration flag and obtains the invocation-local
  instrumentation/counter handle.
\<^enum> It extracts the term head and arguments and queries the dispatcher
  paths for registrations with the matching record, entry kind, head, arity,
  record slot, and partial-application depth.
\<^enum> It applies the ranking policy: exact typed entries precede
  polymorphic entries, rigid prefixes precede flexible prefixes, and longer
  prefixes precede shorter prefixes. Lower ranks are ignored once a valid
  candidate exists at a higher rank. Incompatible candidates at the winning
  rank are an error.
\<^enum> It decomposes the record argument into the attribute and its nested
  operation telescope. It identifies operations that are disjoint from the
  attribute and can cross every operation between them.
\<^enum> It derives adjacent commutativity rewrites only for the swaps needed
  by that telescope. It then constructs the cancelled right-hand side and
  proves the complete equality with \<^verbatim>\<open>Goal.prove\<close>.
\<^enum> It returns the resulting theorem to the simplifier. A nonmatching or
  malformed term returns \<^verbatim>\<open>NONE\<close>; interrupts and registry
  ambiguity are re-raised.

The operation/operation command follows the same registry and certificate
path, but returns a derived fact without installing it in the ambient
simpset. This is the implementation of
\<^verbatim>\<open>locality_autocommutativity\<close>.
\<close>

subsection\<open>How the core routines stay fast\<close>

text\<open>
The performance strategy is to make the common lookup path narrow and to
avoid persistent pairwise state.

\<^enum> Registration is linear in the number of entries. The authoritative
  table stores one entry per registration, while secondary indexes store
  structural keys and reuse Isabelle's \<^verbatim>\<open>Symtab\<close>,
  \<^verbatim>\<open>Typtab\<close>, \<^verbatim>\<open>Inttab\<close>, and \<^verbatim>\<open>Net\<close>
  structures. Lookup probes the relevant record, name, family, depth, arity,
  slot, and type path instead of scanning all entries.
\<^enum> Ranking is performed on index results before certificate payloads are
  loaded. This makes broad fallback registrations cheap when a more specific
  registration wins.
\<^enum> The planner works on the encountered telescope only. Adjacent swap
  theorems and cancellation theorems are memoized in invocation-local tables
  keyed by the exact typed operational patterns. They disappear when the
  callback returns; no theorem cache is retained in global or proof-context
  state.
\<^enum> Conversion work is bounded. Canonicalization limits exhaustive
  variable-renaming search, telescope traversal is restricted to the current
  term, and the proof uses small local simpsets for record equations and
  generated field facts.
\<^enum> Dispatcher names encode the family identity in stable chunks, avoiding
  name-size limits while keeping one generic simproc per family. Context
  transport merges indexes structurally instead of rebuilding pairwise data.

The resulting trade-off is deliberate: a complex cancellation pays for
targeted proof construction at the point of use, while declarations and
locale replay avoid quadratic theorem generation.
\<close>

subsection\<open>Diagnostics and regression instrumentation\<close>

text\<open>
\<^verbatim>\<open>locality_trace_level\<close> enables progressively verbose
diagnostic traces and \<^verbatim>\<open>locality_timing\<close> reports
declaration-time proof phases. \<^verbatim>\<open>AutoLocality_Instrumentation\<close>
is test support: a test starts a run, executes a controlled operation, freezes
and drains callbacks, then checks counters or resources in an immutable
snapshot. Run identifier zero is the disabled path.

The counters expose index probes, candidate examination, planner work,
certificate construction, lifecycle replay, and fallback avoidance. They are
regression and complexity guards; they are not semantic state and not a
theorem cache.
\<close>

subsection\<open>Regression layout\<close>

text\<open>
The executable regression theories are all under
\<^verbatim>\<open>AutoLocality_Tests\<close>. The B0 theories cover public behavior,
lookup, lifecycle, contexts, and import merging. The focused
\<^verbatim>\<open>AutoLocality_Test_*\<close> theories cover cancellation,
shapes, locales, polymorphism, boundaries, and performance. The C1 theories
cover instrumentation and retention. Crush proofs are included in the same
session so the source tree has one test directory while the session still
declares its Crush dependency.
\<close>

section\<open>Auto-Derivation of Locality Lemmas\<close>

text\<open>This theory provides commands for
- State and prove the record footprint of an operation/attribute on a record,
- Automatically derived all commutativity lemmas which are a consequence of disjoint footprints.

We start by discussing a simple moviating example. Let's say we have a record and operations
and attributes on it which consider different parts of the record:\<close>

experiment
begin
datatype_record foo =
  beef :: nat
  ham :: nat
  cheese :: nat

definition inc_beef :: \<open>foo \<Rightarrow> foo\<close> where \<open>inc_beef f \<equiv> update_beef (\<lambda>x. x+1) f\<close>
definition no_ham :: \<open>foo \<Rightarrow> bool\<close> where \<open>no_ham f \<equiv> ham f = 0\<close>

text\<open>In this context, it is intuitively clear that since \<^term>\<open>inc_beef\<close> and \<^term>\<open>no_ham\<close> only 
depend on different fields of the \<^verbatim>\<open>foo\<close> record, they should commute in the following sense:\<close>

lemma inc_beef_no_ham_commute:
  fixes f
  shows \<open>no_ham (inc_beef f) = no_ham f\<close>

text\<open>Yet, as trivial as this may be, of course it needs a proof:\<close>

unfolding no_ham_def inc_beef_def by simp

end

text\<open>Every individual example of such commutativity relations is obvious and easy to prove, but 
the number of relations grows up to quadratically fast in the number of operations/attributes
considered, which quickly burdensome.\<close>

subsection\<open>Data Structures\<close>

text\<open>The following is the core datastructure that this theory maintains:
A record binding an attribute/operation on a record to its footprint.\<close>

ML\<open>
  datatype locality_entry_kind =
      Locality_Attribute
    | Locality_Operation

  exception Locality_Registry_Ambiguity of string

  fun locality_registry_ambiguity message =
    raise Locality_Registry_Ambiguity message

  fun locality_entry_kind_name Locality_Attribute = "attribute"
    | locality_entry_kind_name Locality_Operation = "operation"

  fun locality_entry_kind_of_string "attribute" = Locality_Attribute
    | locality_entry_kind_of_string "operation" = Locality_Operation
    | locality_entry_kind_of_string kind =
        error ("Unknown autolocality entry kind " ^ quote kind)

  fun locality_entry_kind_ord
        (Locality_Attribute, Locality_Attribute) = EQUAL
    | locality_entry_kind_ord
        (Locality_Attribute, Locality_Operation) = LESS
    | locality_entry_kind_ord
        (Locality_Operation, Locality_Attribute) = GREATER
    | locality_entry_kind_ord
        (Locality_Operation, Locality_Operation) = EQUAL

  type locality_canonical_env =
    ((indexname * sort) * int) list *
    ((indexname * typ) * int) list * int * int

  val locality_empty_canonical_env : locality_canonical_env =
    ([], [], 0, 0)

  fun locality_canonical_typ (Type (name, types)) env =
        let
          val (types', env') =
            fold_map locality_canonical_typ types env
        in
          (Type (name, types'), env')
        end
    | locality_canonical_typ (TFree free) env =
        (TFree free, env)
    | locality_canonical_typ
        (TVar (tvar as (_, sort)))
        (tvars, vars, next_tvar, next_var) =
        (case AList.lookup (op =) tvars tvar of
           SOME index =>
             (TVar (("'_locality", index), sort),
              (tvars, vars, next_tvar, next_var))
         | NONE =>
             (TVar (("'_locality", next_tvar), sort),
              ((tvar, next_tvar) :: tvars, vars,
               next_tvar + 1, next_var)))

  fun locality_canonical_term (Const (name, typ)) env =
        let
          val (typ', env') = locality_canonical_typ typ env
        in
          (Const (name, typ'), env')
        end
    | locality_canonical_term (Free (name, typ)) env =
        let
          val (typ', env') = locality_canonical_typ typ env
        in
          (Free (name, typ'), env')
        end
    | locality_canonical_term
        (Var (var as (_, typ)))
        (env as (tvars, vars, next_tvar, next_var)) =
        let
          val (index, env') =
            (case AList.lookup (op =) vars var of
               SOME index => (index, env)
             | NONE =>
                 (next_var,
                  (tvars, (var, next_var) :: vars,
                   next_tvar, next_var + 1)))
          val (typ', env'') = locality_canonical_typ typ env'
        in
          (Var (("_locality", index), typ'), env'')
        end
    | locality_canonical_term (Bound index) env =
        (Bound index, env)
    | locality_canonical_term (Abs (_, typ, body)) env =
        let
          val (typ', env') = locality_canonical_typ typ env
          val (body', env'') = locality_canonical_term body env'
        in
          (Abs (Name.uu, typ', body'), env'')
        end
    | locality_canonical_term (head $ arg) env =
        let
          val (head', env') = locality_canonical_term head env
          val (arg', env'') = locality_canonical_term arg env'
        in
          (head' $ arg', env'')
        end

  fun locality_canonical_pattern pattern =
    fst (locality_canonical_term pattern locality_empty_canonical_env)

  fun locality_remove_each [] = []
    | locality_remove_each (x :: xs) =
        (x, xs) ::
          map (fn (y, ys) => (y, x :: ys))
            (locality_remove_each xs)

  fun locality_permutations [] = [[]]
    | locality_permutations values =
        maps (fn (value, rest) =>
          map (cons value) (locality_permutations rest))
          (locality_remove_each values)

  fun locality_factorial n =
    fold (fn i => fn result =>
      result * IntInf.fromInt i) (1 upto n) (1 : IntInf.int)

  fun locality_group_sorted ord values =
    let
      fun group [] = []
        | group (value :: values') =
            let
              val (same, rest) =
                chop_prefix (fn value' =>
                  ord (value, value') = EQUAL) values'
            in
              (value :: same) :: group rest
            end
    in
      group (sort ord values)
    end

  fun locality_group_search_count groups =
    fold (fn group => fn count =>
      count * locality_factorial (length group))
      groups (1 : IntInf.int)

  val locality_canonical_backtrack_limit : IntInf.int = 100000

  fun locality_check_canonical_search_bound count =
    if count <= locality_canonical_backtrack_limit then ()
    else
      error ("AutoLocality canonical variable labelling requires "
        ^ IntInf.toString count ^ " alternatives; bounded limit is "
        ^ IntInf.toString locality_canonical_backtrack_limit)

  fun locality_extend_canonical_tvars permutation
        (tvars, vars, next_tvar, next_var) =
    let
      val additions =
        map_index (fn (offset, tvar) =>
          (tvar, next_tvar + offset)) permutation
    in
      (additions @ tvars, vars,
       next_tvar + length permutation, next_var)
    end

  fun locality_extend_canonical_vars permutation
        (tvars, vars, next_tvar, next_var) =
    let
      val additions =
        map_index (fn (offset, var) =>
          (var, next_var + offset)) permutation
    in
      (tvars, additions @ vars,
       next_tvar, next_var + length permutation)
    end

  fun locality_extend_canonical_envs extend groups envs =
    fold (fn group => fn envs' =>
      maps (fn env =>
        map (fn permutation => extend permutation env)
          (locality_permutations group)) envs')
      groups envs

  fun locality_canonical_env_has_tvar (tvars, _, _, _) tvar =
    is_some (AList.lookup (op =) tvars tvar)

  fun locality_canonical_env_has_var (_, vars, _, _) var =
    is_some (AList.lookup (op =) vars var)

  fun locality_canonical_env_size (_, _, next_tvar, next_var) =
    (next_tvar, next_var)

  fun locality_canonical_typ_in_env env typ =
    let
      val (typ', env') = locality_canonical_typ typ env
      val _ =
        if locality_canonical_env_size env' =
             locality_canonical_env_size env
        then ()
        else error "Incomplete AutoLocality canonical type-variable environment"
    in
      typ'
    end

  fun locality_remaining_canonical_envs hidden_terms env0 =
    let
      val remaining_tvars =
        fold Term.add_tvars hidden_terms []
        |> filter_out (locality_canonical_env_has_tvar env0)
      val tvar_groups =
        locality_group_sorted
          (Term_Ord.sort_ord o apply2 snd) remaining_tvars
      val tvar_search_count =
        locality_group_search_count tvar_groups
      val _ =
        locality_check_canonical_search_bound tvar_search_count
      val tvar_envs =
        locality_extend_canonical_envs
          locality_extend_canonical_tvars tvar_groups [env0]
      val remaining_vars =
        fold Term.add_vars hidden_terms []
        |> filter_out (locality_canonical_env_has_var env0)

      fun canonical_var_groups env =
        remaining_vars
        |> map (fn var as (_, typ) =>
             (var, locality_canonical_typ_in_env env typ))
        |> locality_group_sorted
             (Term_Ord.typ_ord o apply2 snd)
        |> map (map fst)

      val var_plans =
        map (fn env =>
          let
            val groups = canonical_var_groups env
          in
            (env, groups, locality_group_search_count groups)
          end) tvar_envs
      val search_count =
        fold (fn (_, _, count) => fn total => total + count)
          var_plans (0 : IntInf.int)
      val _ =
        locality_check_canonical_search_bound search_count
    in
      maps (fn (env, groups, _) =>
        locality_extend_canonical_envs
          locality_extend_canonical_vars groups [env])
        var_plans
    end

  type locality_operational_key = {
    record_name: string,
    kind: locality_entry_kind,
    canonical_head: term,
    canonical_pattern: term,
    flexible_prefix: bool list,
    args: int,
    idx: int
  }

  fun make_locality_operational_key record_name kind pattern
        flexible_prefix args idx : locality_operational_key =
    let
      val canonical_pattern = locality_canonical_pattern pattern
    in
      { record_name = record_name,
        kind = kind,
        canonical_head = Term.head_of canonical_pattern,
        canonical_pattern = canonical_pattern,
        flexible_prefix = flexible_prefix,
        args = args,
        idx = idx }
    end

  fun locality_operational_key_ord
        (key0 : locality_operational_key,
         key1 : locality_operational_key) =
    (fast_string_ord o apply2 #record_name
      ||| locality_entry_kind_ord o apply2 #kind
      ||| Term_Ord.fast_term_ord o apply2 #canonical_head
      ||| Term_Ord.fast_term_ord o apply2 #canonical_pattern
      ||| list_ord bool_ord o apply2 #flexible_prefix
      ||| int_ord o apply2 #args
      ||| int_ord o apply2 #idx) (key0, key1)

  fun locality_operational_key_eq keys =
    locality_operational_key_ord keys = EQUAL

  structure LocalityOperationalKeyTable =
    Table(type key = locality_operational_key
      val ord = locality_operational_key_ord)

  type locality_entry = {
    key: locality_operational_key,
    const_name: string,  \<comment>\<open>The name of the attribute/operation\<close>
    pattern: term,  \<comment>\<open>The exact typed, possibly partially applied registration term\<close>
    footprint: string list,  \<comment>\<open>The list of record fields affecting the attribute/operation\<close>
    field: bool, \<comment>\<open>Whether this entry corresponds to a record field projection\<close>
    core_thms: thm list, \<comment>\<open>Linear field-update commutativity/cancellation certificates\<close>
    disjoint_thms: thm list, \<comment>\<open>Linear field-projection disjointness certificates\<close>
    local_thm: thm option \<comment>\<open>Operation-as-footprint-updates certificate\<close>
  }

  fun make_locality_entry record_name kind const_name pattern
        flexible_prefix footprint args idx field
        core_thms disjoint_thms local_thm : locality_entry =
    { key = make_locality_operational_key record_name kind pattern
        flexible_prefix args idx,
      const_name = const_name,
      pattern = pattern,
      footprint = footprint,
      field = field,
      core_thms = core_thms,
      disjoint_thms = disjoint_thms,
      local_thm = local_thm }

  fun locality_entry_record_name (entry : locality_entry) =
    #record_name (#key entry)

  fun locality_entry_kind (entry : locality_entry) =
    #kind (#key entry)

  fun locality_entry_flexible_prefix (entry : locality_entry) =
    #flexible_prefix (#key entry)

  fun locality_entry_args (entry : locality_entry) =
    #args (#key entry)

  fun locality_entry_idx (entry : locality_entry) =
    #idx (#key entry)

  type locality_counter =
    AutoLocality_Instrumentation.counter -> (unit -> IntInf.int) -> unit

  fun locality_no_count
        (_ : AutoLocality_Instrumentation.counter)
        (_ : unit -> IntInf.int) = ()

  fun locality_make_counter ctxt add_work : locality_counter =
    if AutoLocality_Instrumentation.current_run_id ctxt =
         AutoLocality_Instrumentation.disabled_run_id
    then locality_no_count
    else
      fn counter => fn make_amount =>
        AutoLocality_Instrumentation.record_counters ctxt (fn () =>
          let
            val amount = make_amount ()
            val _ =
              (case add_work of
                NONE => ()
              | SOME add => add amount)
          in [(counter, amount)] end)

  fun locality_direct_counter ctxt =
    locality_make_counter ctxt NONE

  fun locality_count_one count counter =
    count counter (fn () => 1)

  fun locality_count_int count counter make_amount =
    count counter (fn () => IntInf.fromInt (make_amount ()))

  fun locality_count_list count counter values =
    locality_count_int count counter (fn () => length values)

  fun locality_with_callback ctxt callback =
    if AutoLocality_Instrumentation.current_run_id ctxt =
         AutoLocality_Instrumentation.disabled_run_id
    then callback locality_no_count
    else
      let
        val work = Unsynchronized.ref (0 : IntInf.int)
        fun add_work amount = work := ! work + amount
        val count = locality_make_counter ctxt (SOME add_work)
      in
        AutoLocality_Instrumentation.with_callback ctxt
          (fn () => ! work) (fn () => callback count)
      end

  type locality_slot = {
    pattern: term,
    flexible_prefix: bool list,
    kind: locality_entry_kind,
    args: int,
    idx: int
  }

  fun locality_slot_of_entry (entry : locality_entry) : locality_slot =
    { pattern = #pattern entry,
      flexible_prefix = locality_entry_flexible_prefix entry,
      kind = locality_entry_kind entry,
      args = locality_entry_args entry,
      idx = locality_entry_idx entry }

  fun morph_locality_slot phi (slot : locality_slot) : locality_slot =
    { pattern = Morphism.term phi (#pattern slot),
      flexible_prefix = #flexible_prefix slot,
      kind = #kind slot,
      args = #args slot,
      idx = #idx slot }

  fun locality_slot_eq (slot0 : locality_slot, slot1 : locality_slot) =
       #kind slot0 = #kind slot1
    andalso #args slot0 = #args slot1
    andalso #idx slot0 = #idx slot1
    andalso #flexible_prefix slot0 = #flexible_prefix slot1
    andalso Term.aconv
      (locality_canonical_pattern (#pattern slot0),
       locality_canonical_pattern (#pattern slot1))

  fun locality_entry_slot_eq (e0 : locality_entry, e1 : locality_entry) =
    locality_operational_key_eq (#key e0, #key e1)

  fun locality_pattern_flexible_prefix pattern =
    snd (Term.strip_comb pattern)
    |> map (fn arg => not (null (Term.add_frees arg [])))

  \<comment>\<open>Symmetric comparison for exact same-target command replay.\<close>
  fun locality_registration_pattern_eq _
        (pattern0, pattern1) =
    Term.aconv
      (locality_canonical_pattern pattern0,
       locality_canonical_pattern pattern1)

  type locality_thm_fingerprint = term * term list * sort list

  type locality_entry_certificate_fingerprint = {
    pattern: term,
    core: locality_thm_fingerprint list,
    disjoint: locality_thm_fingerprint list,
    local_certificate: locality_thm_fingerprint option
  }

  fun locality_thm_fingerprint env prop thm :
        locality_thm_fingerprint =
    let
      val (hyps, env') =
        fold_map locality_canonical_term (Thm.hyps_of thm) env
      val _ =
        if locality_canonical_env_size env' =
             locality_canonical_env_size env
        then ()
        else error "Incomplete AutoLocality canonical theorem environment"
      val canonical_hyps =
        sort Term_Ord.fast_term_ord hyps
      val shyps = Thm.shyps_of thm |> sort Term_Ord.sort_ord
    in
      (prop, canonical_hyps, shyps)
    end

  fun locality_thm_fingerprint_ord
        (fingerprint0 : locality_thm_fingerprint,
         fingerprint1 : locality_thm_fingerprint) =
    (Term_Ord.fast_term_ord o apply2 #1
      ||| list_ord Term_Ord.fast_term_ord o apply2 #2
      ||| list_ord Term_Ord.sort_ord o apply2 #3)
      (fingerprint0, fingerprint1)

  fun locality_entry_certificate_fingerprint_ord
        (fingerprint0 : locality_entry_certificate_fingerprint,
         fingerprint1 : locality_entry_certificate_fingerprint) =
    (Term_Ord.fast_term_ord o apply2 #pattern
      ||| list_ord locality_thm_fingerprint_ord o apply2 #core
      ||| list_ord locality_thm_fingerprint_ord o apply2 #disjoint
      ||| option_ord locality_thm_fingerprint_ord
            o apply2 #local_certificate)
      (fingerprint0, fingerprint1)

  \<comment>\<open>The pattern and all role-ordered certificate propositions form the ordered roots
     of one occurrence graph. First occurrence fixes labels there. Variables that occur only
     in unordered hidden hypotheses are individualized over name-independent sort/type
     colour classes; bounded exhaustive backtracking chooses the least complete bundle.\<close>
  fun locality_entry_certificate_fingerprint
        (entry : locality_entry) :
        locality_entry_certificate_fingerprint =
    let
      val core_thms = #core_thms entry
      val disjoint_thms = #disjoint_thms entry
      val local_thms = the_list (#local_thm entry)
      val thms = core_thms @ disjoint_thms @ local_thms
      val ordered_roots =
        #pattern entry :: map Thm.full_prop_of thms
      val (canonical_roots, ordered_env) =
        fold_map locality_canonical_term ordered_roots
          locality_empty_canonical_env
      val (canonical_pattern, canonical_props) =
        (case canonical_roots of
           pattern :: props => (pattern, props)
         | [] => error "Missing AutoLocality operational-pattern root")
      val hidden_terms = maps Thm.hyps_of thms
      val complete_envs =
        locality_remaining_canonical_envs hidden_terms ordered_env

      fun fingerprint_for_env env =
        let
          val thm_fingerprints =
            map2 (fn prop => fn thm =>
              locality_thm_fingerprint env prop thm)
              canonical_props thms
          val (core, thm_fingerprints') =
            chop (length core_thms) thm_fingerprints
          val (disjoint, local_fingerprints) =
            chop (length disjoint_thms) thm_fingerprints'
          val local_certificate =
            (case (#local_thm entry, local_fingerprints) of
               (NONE, []) => NONE
             | (SOME _, [fingerprint]) => SOME fingerprint
             | _ =>
                 error "Malformed AutoLocality certificate fingerprint")
        in
          { pattern = canonical_pattern,
            core = core,
            disjoint = disjoint,
            local_certificate = local_certificate }
        end

      fun choose env NONE =
            SOME (fingerprint_for_env env)
        | choose env (SOME best) =
            let
              val candidate = fingerprint_for_env env
            in
              SOME
                (case locality_entry_certificate_fingerprint_ord
                    (candidate, best) of
                   LESS => candidate
                 | _ => best)
            end
    in
      fold choose complete_envs NONE |> the
    end

  fun locality_entry_conflict (entry : locality_entry) detail =
    error ("Conflicting autolocality registrations for "
      ^ #const_name entry ^ " on " ^ locality_entry_record_name entry
      ^ ": " ^ detail)

  fun locality_entry_merge_conflict
        (entry0 : locality_entry, entry1 : locality_entry) detail =
    let
      val names =
        sort_distinct fast_string_ord [#const_name entry0, #const_name entry1]
      val records =
        sort_distinct fast_string_ord
          [locality_entry_record_name entry0,
           locality_entry_record_name entry1]
    in
      error ("Conflicting autolocality registrations for "
        ^ commas_quote names ^ " on " ^ commas_quote records
        ^ ": " ^ detail)
    end

  fun canonical_locality_entry_representative
        (entry0 : locality_entry, entry1 : locality_entry) =
    (case Term_Ord.fast_term_ord
        (#pattern entry0, #pattern entry1) of
       GREATER => entry1
     | _ => entry0)

  fun canonical_locality_footprint (footprint0, footprint1) =
    (case list_ord fast_string_ord (footprint0, footprint1) of
       GREATER => footprint1
     | _ => footprint0)

  fun merge_locality_entry
        (e0 : locality_entry, e1 : locality_entry) : locality_entry =
    if not (locality_entry_slot_eq (e0, e1)) then
      locality_entry_merge_conflict (e0, e1) "operational keys differ"
    else if #const_name e0 <> #const_name e1 then
      locality_entry_merge_conflict (e0, e1) "constant identities differ"
    else if not (eq_set (op =) (#footprint e0, #footprint e1)) then
      locality_entry_merge_conflict (e0, e1) "footprints differ"
    else if #field e0 <> #field e1 then
      locality_entry_merge_conflict (e0, e1) "field metadata differs"
    else if length (#core_thms e0) <> length (#core_thms e1) then
      locality_entry_merge_conflict (e0, e1)
        "core certificate completeness differs"
    else if length (#disjoint_thms e0) <> length (#disjoint_thms e1) then
      locality_entry_merge_conflict (e0, e1)
        "disjoint certificate completeness differs"
    else if Option.isSome (#local_thm e0) <> Option.isSome (#local_thm e1) then
      locality_entry_merge_conflict (e0, e1)
        "local-action certificate completeness differs"
    else if locality_entry_certificate_fingerprint_ord
        (locality_entry_certificate_fingerprint e0,
         locality_entry_certificate_fingerprint e1) <> EQUAL
    then
      locality_entry_merge_conflict (e0, e1)
        ("certificate propositions, hidden hypotheses, sort hypotheses, "
          ^ "or pattern-variable sharing differ")
    else
      let
        val representative =
          canonical_locality_entry_representative (e0, e1)
      in
        { key = #key representative,
          const_name = #const_name representative,
          pattern = #pattern representative,
          footprint =
            canonical_locality_footprint (#footprint e0, #footprint e1),
          field = #field representative,
          core_thms = #core_thms representative,
          disjoint_thms = #disjoint_thms representative,
          local_thm = #local_thm representative }
      end

  fun insert_locality_entry (entry : locality_entry) =
    LocalityOperationalKeyTable.map_default
      (#key entry, entry)
      (fn entry' => merge_locality_entry (entry', entry))

  fun locality_entry_table_of entries =
    LocalityOperationalKeyTable.build
      (fold insert_locality_entry entries)

  fun merge_locality_entry_tables tables =
    LocalityOperationalKeyTable.join
      (K merge_locality_entry) tables

  \<comment>\<open>Compatibility list views remain deterministic structural-key order, not historical
     insertion order. Stage-2B2 owns any later ordinal compatibility index.\<close>
  fun locality_entries_of_table table =
    LocalityOperationalKeyTable.dest table |> map #2

  fun merge_locality_entry_lists (entries0, entries1) =
    merge_locality_entry_tables
      (locality_entry_table_of entries0, locality_entry_table_of entries1)
    |> locality_entries_of_table

  \<comment>\<open>Global data for tracking footprints of operations. One structural operational-key
     table owns the semantic entries; record-indexed list APIs below are derived compatibility
     views. Pairwise commutativity/cancellation lemmas are no longer pre-generated, so no
     disjointness bookkeeping is needed; cancellations are handled on-the-fly by the
     \<^verbatim>\<open>locality_cancel\<close> simprocs.\<close>
  structure RecordLocalityData = Generic_Data
  (
    type T = locality_entry LocalityOperationalKeyTable.table;
    val empty = LocalityOperationalKeyTable.empty;
    val merge = merge_locality_entry_tables;
  );

  type locality_key_set = unit LocalityOperationalKeyTable.table

  val empty_locality_key_set : locality_key_set =
    LocalityOperationalKeyTable.empty

  fun insert_locality_key key =
    LocalityOperationalKeyTable.map_default (key, ()) (K ())

  fun merge_locality_key_sets key_sets =
    LocalityOperationalKeyTable.join (K (fn _ => ())) key_sets

  fun locality_name_index_names name =
    distinct (op =) [name, Long_Name.base_name name]

  type locality_replay_key = {
    record_name: string,
    canonical_pattern: term,
    idx: int
  }

  fun locality_replay_key_ord
        (key0 : locality_replay_key, key1 : locality_replay_key) =
    (fast_string_ord o apply2 #record_name
      ||| Term_Ord.fast_term_ord o apply2 #canonical_pattern
      ||| int_ord o apply2 #idx) (key0, key1)

  structure LocalityReplayKeyTable =
    Table(type key = locality_replay_key
      val ord = locality_replay_key_ord)

  fun locality_replay_key record_name pattern idx : locality_replay_key =
    { record_name = record_name,
      canonical_pattern = locality_canonical_pattern pattern,
      idx = idx }

  datatype locality_family_head =
      Locality_Family_Const of string
    | Locality_Family_Term of term

  fun locality_family_head_ord
        (Locality_Family_Const name0, Locality_Family_Const name1) =
        fast_string_ord (name0, name1)
    | locality_family_head_ord
        (Locality_Family_Const _, Locality_Family_Term _) = LESS
    | locality_family_head_ord
        (Locality_Family_Term _, Locality_Family_Const _) = GREATER
    | locality_family_head_ord
        (Locality_Family_Term head0, Locality_Family_Term head1) =
        Term_Ord.fast_term_ord (head0, head1)

  fun locality_family_head (Const (name, _)) =
        Locality_Family_Const name
    | locality_family_head head =
        Locality_Family_Term (locality_canonical_pattern head)

  type locality_family_key = {
    record_name: string,
    kind: locality_entry_kind,
    head: locality_family_head
  }

  fun locality_family_key_ord
        (key0 : locality_family_key, key1 : locality_family_key) =
    (fast_string_ord o apply2 #record_name
      ||| locality_entry_kind_ord o apply2 #kind
      ||| locality_family_head_ord o apply2 #head) (key0, key1)

  structure LocalityFamilyKeyTable =
    Table(type key = locality_family_key
      val ord = locality_family_key_ord)

  fun locality_constant_head_name (Const (name, _)) = SOME name
    | locality_constant_head_name _ = NONE

  fun locality_rigid_head_name head =
    (case locality_constant_head_name head of
       SOME name => name
     | NONE =>
         error ("AutoLocality registration has non-constant rigid head "
           ^ ML_Syntax.print_term head))

  fun locality_family_key_of_operational_key
        (key : locality_operational_key) : locality_family_key =
    { record_name = #record_name key,
      kind = #kind key,
      head = locality_family_head (#canonical_head key) }

  type locality_dispatch_key = {
    head_name: string,
    arity: int
  }

  fun locality_dispatch_key_ord
        (key0 : locality_dispatch_key, key1 : locality_dispatch_key) =
    (fast_string_ord o apply2 #head_name
      ||| int_ord o apply2 #arity) (key0, key1)

  fun locality_dispatch_key_eq keys =
    locality_dispatch_key_ord keys = EQUAL

  structure LocalityDispatchKeyTable =
    Table(type key = locality_dispatch_key
      val ord = locality_dispatch_key_ord)

  \<comment>\<open>The physical family arity is the complete arrow spine of the rigid constant's
     declared type, never the number of arguments exposed by one registration. Thus partial
     registrations and constants with explicitly function-valued results share the same trigger.
     A semantic registration may consume only a prefix of that declared spine. Expanded
     abbreviations have structural lambda heads and therefore remain semantic registrations
     without a named physical dispatcher.\<close>
  fun locality_dispatch_key_of_operational_key_opt thy
        (key : locality_operational_key) : locality_dispatch_key option =
    (case locality_constant_head_name (#canonical_head key) of
       NONE => NONE
     | SOME head_name =>
         let
           val declared_arity =
             Sign.the_const_type thy head_name
             |> Term.binder_types
             |> length
           val registered_arity =
             length (snd (Term.strip_comb (#canonical_pattern key)))
               + #args key
           val _ =
             if registered_arity <= declared_arity then ()
             else
               error ("AutoLocality registration consumes "
                 ^ Int.toString registered_arity ^ " arguments of "
                 ^ quote head_name ^ " with declared spine arity "
                 ^ Int.toString declared_arity)
         in
           SOME
             { head_name = head_name,
               arity = declared_arity }
         end)

  fun locality_dispatch_key_of_operational_key thy key =
    (case locality_dispatch_key_of_operational_key_opt thy key of
       SOME dispatch_key => dispatch_key
     | NONE =>
         error ("AutoLocality registration has no constant dispatcher head "
           ^ ML_Syntax.print_term (#canonical_head key)))

  fun locality_dispatch_key_of_entry ctxt (entry : locality_entry) =
    locality_dispatch_key_of_operational_key
      (Proof_Context.theory_of ctxt) (#key entry)

  fun locality_dispatch_key_of_entry_opt ctxt (entry : locality_entry) =
    locality_dispatch_key_of_operational_key_opt
      (Proof_Context.theory_of ctxt) (#key entry)

  fun locality_index_varify_atyps tfrees base =
    let
      val instantiations =
        tfrees |> map_index (fn (i, (name, sort)) =>
          ((name, sort), TVar ((name, base + i), sort)))
    in
      fn TFree key =>
           AList.lookup (op =) instantiations key
           |> the_default (TFree key)
       | typ => typ
    end

  fun locality_index_varify_types term =
    let
      val tfrees = Term.add_tfrees term []
      val base = Term.maxidx_of_term term + 1
    in
      Term.map_types
        (Term.map_atyps (locality_index_varify_atyps tfrees base)) term
    end

  fun locality_match_pattern pattern flexible_prefix =
    let
      val pattern_scheme =
        locality_index_varify_types pattern
      val (head, args) = Term.strip_comb pattern_scheme
      val _ =
        if length flexible_prefix = length args then ()
        else error "Malformed autolocality flexible-prefix metadata"
      val base = Term.maxidx_of_term pattern_scheme + 1
      val args' =
        (args ~~ flexible_prefix) |> map_index (fn (i, (arg, flexible)) =>
          if flexible
          then Var (("locality_prefix", base + i), Term.type_of arg)
          else arg)
    in
      Term.list_comb (head, args')
    end

  fun locality_index_match_pattern
        (key : locality_operational_key) =
    locality_match_pattern
      (#canonical_pattern key) (#flexible_prefix key)

  fun locality_type_is_monomorphic typ =
    null (Term.add_tvarsT typ [])
    andalso null (Term.add_tfreesT typ [])

  fun locality_polymorphic_index_pattern typ pattern =
    Const ("AutoLocality.index", dummyT)
      $ Net.encode_type typ $ pattern

  type locality_key_net = locality_operational_key Net.net

  val empty_locality_key_net : locality_key_net = Net.empty

  fun locality_index_normalize term =
    Envir.beta_eta_contract term

  fun insert_locality_key_net pattern key =
    Net.insert_term_safe locality_operational_key_eq
      (locality_index_normalize pattern, key)

  fun merge_locality_key_nets nets =
    Net.merge locality_operational_key_eq nets

  type locality_path_index = {
    exact_rigid: locality_key_net Typtab.table,
    exact_flexible: locality_key_net Typtab.table,
    polymorphic_rigid: locality_key_net,
    polymorphic_flexible: locality_key_net
  }

  val empty_locality_path_index : locality_path_index =
    { exact_rigid = Typtab.empty,
      exact_flexible = Typtab.empty,
      polymorphic_rigid = empty_locality_key_net,
      polymorphic_flexible = empty_locality_key_net }

  fun insert_locality_path_key
        (key : locality_operational_key)
        (path : locality_path_index) : locality_path_index =
    let
      val pattern =
        locality_index_match_pattern key
        |> locality_index_normalize
      val head_type = Term.type_of (Term.head_of pattern)
      val flexible = exists I (#flexible_prefix key)
      fun insert_exact table =
        Typtab.map_default
          (head_type, empty_locality_key_net)
          (insert_locality_key_net pattern key) table
      fun insert_polymorphic net =
        insert_locality_key_net
          (locality_polymorphic_index_pattern head_type pattern) key net
    in
      if locality_type_is_monomorphic head_type then
        if flexible then
          { exact_rigid = #exact_rigid path,
            exact_flexible = insert_exact (#exact_flexible path),
            polymorphic_rigid = #polymorphic_rigid path,
            polymorphic_flexible = #polymorphic_flexible path }
        else
          { exact_rigid = insert_exact (#exact_rigid path),
            exact_flexible = #exact_flexible path,
            polymorphic_rigid = #polymorphic_rigid path,
            polymorphic_flexible = #polymorphic_flexible path }
      else if flexible then
        { exact_rigid = #exact_rigid path,
          exact_flexible = #exact_flexible path,
          polymorphic_rigid = #polymorphic_rigid path,
          polymorphic_flexible =
            insert_polymorphic (#polymorphic_flexible path) }
      else
        { exact_rigid = #exact_rigid path,
          exact_flexible = #exact_flexible path,
          polymorphic_rigid =
            insert_polymorphic (#polymorphic_rigid path),
          polymorphic_flexible = #polymorphic_flexible path }
    end

  fun merge_locality_path_indexes
        (path0 : locality_path_index,
         path1 : locality_path_index) : locality_path_index =
    { exact_rigid =
        Typtab.join (K merge_locality_key_nets)
          (#exact_rigid path0, #exact_rigid path1),
      exact_flexible =
        Typtab.join (K merge_locality_key_nets)
          (#exact_flexible path0, #exact_flexible path1),
      polymorphic_rigid =
        merge_locality_key_nets
          (#polymorphic_rigid path0, #polymorphic_rigid path1),
      polymorphic_flexible =
        merge_locality_key_nets
          (#polymorphic_flexible path0, #polymorphic_flexible path1) }

  type locality_slot_paths = locality_path_index Inttab.table
  type locality_arity_paths = locality_slot_paths Inttab.table
  type locality_depth_paths = locality_arity_paths Inttab.table
  type locality_family_paths =
    locality_depth_paths LocalityFamilyKeyTable.table

  fun insert_locality_depth_path
        (entry : locality_entry)
        (depths : locality_depth_paths) : locality_depth_paths =
    let
      val key = #key entry
      val depth = length (snd (Term.strip_comb (#canonical_pattern key)))
    in
      depths
      |> Inttab.map_default (depth, Inttab.empty)
           (Inttab.map_default (#args key, Inttab.empty)
             (Inttab.map_default
               (#idx key, empty_locality_path_index)
               (insert_locality_path_key key)))
    end

  fun merge_locality_slot_paths paths =
    Inttab.join (K merge_locality_path_indexes) paths

  fun merge_locality_arity_paths paths =
    Inttab.join (K merge_locality_slot_paths) paths

  fun merge_locality_depth_paths paths =
    Inttab.join (K merge_locality_arity_paths) paths

  fun merge_locality_family_paths paths =
    LocalityFamilyKeyTable.join (K merge_locality_depth_paths) paths

  fun insert_locality_family_path
        (entry : locality_entry)
        (families : locality_family_paths) : locality_family_paths =
    let
      val family =
        locality_family_key_of_operational_key (#key entry)
    in
      LocalityFamilyKeyTable.map_default
        (family, Inttab.empty)
        (insert_locality_depth_path entry) families
    end

  type locality_dispatch_paths =
    locality_depth_paths LocalityDispatchKeyTable.table

  fun insert_locality_dispatch_path dispatch_key entry =
    LocalityDispatchKeyTable.map_default
      (dispatch_key, Inttab.empty)
      (insert_locality_depth_path entry)

  fun merge_locality_dispatch_paths paths =
    LocalityDispatchKeyTable.join
      (K merge_locality_depth_paths) paths

  type locality_secondary_index = {
    records: locality_key_set Symtab.table,
    names: locality_key_set Symtab.table Symtab.table,
    replay_slots: locality_key_set LocalityReplayKeyTable.table,
    families: locality_family_paths,
    dispatch: locality_dispatch_paths
  }

  val empty_locality_secondary_index : locality_secondary_index =
    { records = Symtab.empty,
      names = Symtab.empty,
      replay_slots = LocalityReplayKeyTable.empty,
      families = LocalityFamilyKeyTable.empty,
      dispatch = LocalityDispatchKeyTable.empty }

  fun insert_locality_secondary_key_with_dispatch dispatch_key
        (entry : locality_entry)
        (index : locality_secondary_index) : locality_secondary_index =
    let
      val key = #key entry
      val record_name = locality_entry_record_name entry
      val indexed_names =
        locality_name_index_names (#const_name entry)
      val replay_key =
        locality_replay_key record_name (#pattern entry)
          (locality_entry_idx entry)
    in
      { records =
          #records index
          |> Symtab.map_default
               (record_name, empty_locality_key_set)
               (insert_locality_key key),
        names =
          #names index
          |> Symtab.map_default (record_name, Symtab.empty)
               (fn names =>
                 fold (fn name =>
                   Symtab.map_default
                     (name, empty_locality_key_set)
                     (insert_locality_key key))
                   indexed_names names),
        replay_slots =
          #replay_slots index
          |> LocalityReplayKeyTable.map_default
               (replay_key, empty_locality_key_set)
               (insert_locality_key key),
        families =
          insert_locality_family_path entry (#families index),
        dispatch =
          (case dispatch_key of
             NONE => #dispatch index
           | SOME key =>
               if locality_entry_kind entry = Locality_Attribute
               then
                 insert_locality_dispatch_path key entry
                   (#dispatch index)
               else
                 error "Malformed AutoLocality dispatch-index insertion") }
    end

  fun insert_locality_secondary_key entry =
    insert_locality_secondary_key_with_dispatch NONE entry

  fun merge_locality_secondary_indexes
        (index0 : locality_secondary_index,
         index1 : locality_secondary_index) : locality_secondary_index =
    { records =
        Symtab.join (K merge_locality_key_sets)
          (#records index0, #records index1),
      names =
        Symtab.join
          (K (Symtab.join (K merge_locality_key_sets)))
          (#names index0, #names index1),
      replay_slots =
        LocalityReplayKeyTable.join
          (K merge_locality_key_sets)
          (#replay_slots index0, #replay_slots index1),
      families =
        merge_locality_family_paths
          (#families index0, #families index1),
      dispatch =
        merge_locality_dispatch_paths
          (#dispatch index0, #dispatch index1) }

  \<comment>\<open>All secondary tables contain structural operational keys only. The authoritative
     table above remains the sole owner of entries and theorem certificates.\<close>
  structure LocalitySecondaryIndex = Generic_Data
  (
    type T = locality_secondary_index;
    val empty = empty_locality_secondary_index;
    val merge = merge_locality_secondary_indexes;
  );

  fun locality_index_probe count lookup =
    (locality_count_one count
       AutoLocality_Instrumentation.Lookup_Index_Probes;
     lookup ())

  fun locality_keys_for_names_with count context record_name names =
    let
      val indexed_names =
        locality_index_probe count (fn () =>
          Symtab.lookup
            (#names (LocalitySecondaryIndex.get context)) record_name)
      fun add_name _ keys NONE = keys
        | add_name name keys (SOME names_for_record) =
            (case locality_index_probe count (fn () =>
                    Symtab.lookup names_for_record name) of
               NONE => keys
             | SOME keys' => merge_locality_key_sets (keys, keys'))
    in
      fold (fn name => fn keys =>
        add_name name keys indexed_names)
        (distinct (op =) names) empty_locality_key_set
    end

  fun locality_key_set_of_list keys =
    fold insert_locality_key keys empty_locality_key_set

  fun capture_noninterrupt f =
    (case Exn.capture f () of
       Exn.Res result => SOME result
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else (case exn of
           Locality_Registry_Ambiguity _ => Exn.reraise exn
         | _ => NONE))

  fun locality_terms_provably_equal_with count ctxt (lhs, rhs) =
    let
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lookup_Equality_Attempts
    in
      Term.aconv (lhs, rhs) orelse
      Option.isSome (capture_noninterrupt (fn () =>
        Goal.prove ctxt [] [] (Logic.mk_equals (lhs, rhs))
          (fn {context, ...} =>
            asm_full_simp_tac (context addsimps @{thms fun_eq_iff}) 1)))
    end

  fun locality_terms_provably_equal ctxt pair =
    locality_terms_provably_equal_with locality_no_count ctxt pair

  fun locality_pattern_flexible_pairs ctxt actual pattern flexible_prefix =
    let
      val thy = Proof_Context.theory_of ctxt
      val match_pattern =
        locality_match_pattern pattern flexible_prefix
      val env =
        Pattern.match thy (match_pattern, actual)
          (Vartab.empty, Vartab.empty)
      val (_, stored_args) =
        pattern |> locality_index_varify_types |> Term.strip_comb
      val (_, actual_args) = Term.strip_comb actual
    in
      (stored_args ~~ actual_args ~~ flexible_prefix)
      |> map_filter (fn ((stored, actual), flexible) =>
           if flexible
           then SOME (Envir.subst_term env stored, actual)
           else NONE)
    end

  fun locality_pattern_matches_prefix_with count ctxt
        actual pattern flexible_prefix =
    let
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lookup_Prefix_Alternatives
    in
      Option.isSome (capture_noninterrupt (fn () =>
        let
          val flexible_pairs =
            locality_pattern_flexible_pairs
              ctxt actual pattern flexible_prefix
          val _ =
            if List.all (locality_terms_provably_equal_with count ctxt)
                 flexible_pairs
            then ()
            else raise Pattern.MATCH
        in () end))
    end

  fun locality_key_matches_prefix_with count ctxt actual
        (key : locality_operational_key) =
    locality_pattern_matches_prefix_with count ctxt actual
      (#canonical_pattern key) (#flexible_prefix key)

  datatype locality_path_class =
      Locality_Exact_Rigid_Path
    | Locality_Exact_Flexible_Path
    | Locality_Polymorphic_Rigid_Path
    | Locality_Polymorphic_Flexible_Path

  type locality_query_rank = {
    exact_type: bool,
    rigid_prefix: bool,
    prefix_length: int
  }

  fun locality_query_rank_ord
        (rank0 : locality_query_rank,
         rank1 : locality_query_rank) =
    (bool_ord o apply2 #exact_type
      ||| bool_ord o apply2 #rigid_prefix
      ||| int_ord o apply2 #prefix_length) (rank0, rank1)

  fun locality_path_class_rank prefix_length path_class
        : locality_query_rank =
    case path_class of
      Locality_Exact_Rigid_Path =>
        { exact_type = true,
          rigid_prefix = true,
          prefix_length = prefix_length }
    | Locality_Exact_Flexible_Path =>
        { exact_type = true,
          rigid_prefix = false,
          prefix_length = prefix_length }
    | Locality_Polymorphic_Rigid_Path =>
        { exact_type = false,
          rigid_prefix = true,
          prefix_length = prefix_length }
    | Locality_Polymorphic_Flexible_Path =>
        { exact_type = false,
          rigid_prefix = false,
          prefix_length = prefix_length }

  val locality_path_classes_by_rank =
    [Locality_Exact_Rigid_Path,
     Locality_Exact_Flexible_Path,
     Locality_Polymorphic_Rigid_Path,
     Locality_Polymorphic_Flexible_Path]

  fun locality_path_class_keys_with count actual path_class
        (path : locality_path_index) =
    let
      val normalized_actual =
        locality_index_normalize actual
      val head_type =
        Term.type_of (Term.head_of normalized_actual)
      fun net_keys net query =
        locality_index_probe count (fn () =>
          Net.match_term net (locality_index_normalize query)
          |> locality_key_set_of_list)
      fun exact_keys exact =
        (case locality_index_probe count (fn () =>
                Typtab.lookup exact head_type) of
           NONE => empty_locality_key_set
         | SOME net => net_keys net normalized_actual)
      val polymorphic_actual =
        locality_polymorphic_index_pattern
          head_type normalized_actual
    in
      case path_class of
        Locality_Exact_Rigid_Path =>
          exact_keys (#exact_rigid path)
      | Locality_Exact_Flexible_Path =>
          exact_keys (#exact_flexible path)
      | Locality_Polymorphic_Rigid_Path =>
          net_keys (#polymorphic_rigid path) polymorphic_actual
      | Locality_Polymorphic_Flexible_Path =>
          net_keys (#polymorphic_flexible path) polymorphic_actual
    end

  fun locality_filter_key_set predicate keys =
    LocalityOperationalKeyTable.fold
      (fn (key, ()) => fn result =>
        if predicate key then insert_locality_key key result
        else result)
      keys empty_locality_key_set

  fun locality_key_is_exact_pattern actual
        (key : locality_operational_key) =
    Term.aconv
      (locality_canonical_pattern actual, #canonical_pattern key)

  type locality_ranked_key_query = {
    rank: locality_query_rank,
    actual: term,
    retrieve: unit -> locality_key_set
  }

  fun locality_equality_valid_keys_with count ctxt actual keys =
    let
      val valid =
        locality_filter_key_set
          (locality_key_matches_prefix_with count ctxt actual) keys
      val exact =
        locality_filter_key_set
          (locality_key_is_exact_pattern actual) valid
    in
      if LocalityOperationalKeyTable.is_empty exact
      then valid
      else exact
    end

  fun locality_maximal_rank_keys_with count ctxt queries =
    let
      fun consider (query : locality_ranked_key_query)
            (previous_rank, selected) =
        let
          val rank = #rank query
          val _ =
            (case previous_rank of
               NONE => ()
             | SOME previous =>
                 if locality_query_rank_ord (previous, rank) = LESS
                 then error "Malformed ascending autolocality query rank"
                 else ())
          val selected' =
            (case selected of
               SOME keys => SOME keys
             | NONE =>
                 let
                   val keys =
                     #retrieve query ()
                     |> locality_equality_valid_keys_with
                          count ctxt (#actual query)
                 in
                   if LocalityOperationalKeyTable.is_empty keys
                   then NONE
                   else SOME keys
                 end)
        in
          (SOME rank, selected')
        end
      val (_, selected) = fold consider queries (NONE, NONE)
    in
      the_default empty_locality_key_set selected
    end

  fun locality_dispatch_ranked_key_queries_with count ctxt
        (dispatch_key : locality_dispatch_key) actual =
    let
      val context = Context.Proof ctxt
      val indexed_paths =
        locality_index_probe count (fn () =>
          LocalityDispatchKeyTable.lookup
            (#dispatch (LocalitySecondaryIndex.get context)) dispatch_key)
      val (actual_head, actual_args) = Term.strip_comb actual
      val argument_count = length actual_args
      val shape_matches =
        (case actual_head of
           Const (head_name, _) =>
             head_name = #head_name dispatch_key
             andalso argument_count = #arity dispatch_key
         | _ => false)
      fun int_range first last =
        if first > last then [] else first upto last
      fun int_range_down first last =
        if first < last then []
        else first :: int_range_down (first - 1) last
      fun add_slot path_class actual slots slot keys =
        (case locality_index_probe count (fn () =>
                Inttab.lookup slots slot) of
           NONE => keys
         | SOME path =>
             merge_locality_key_sets
               (keys,
                locality_path_class_keys_with
                  count actual path_class path))
      fun add_arity path_class actual arities arity keys =
        (case locality_index_probe count (fn () =>
                Inttab.lookup arities arity) of
           NONE => keys
         | SOME slots =>
             fold (add_slot path_class actual slots)
               (int_range 0 (arity - 1)) keys)
      fun retrieve depths path_class depth actual () =
        (case locality_index_probe count (fn () =>
                Inttab.lookup depths depth) of
           NONE => empty_locality_key_set
         | SOME arities =>
             fold (add_arity path_class actual arities)
               (int_range 0 (argument_count - depth))
               empty_locality_key_set)
      fun ranked_query depths path_class depth =
        let
          val actual_prefix =
            Term.list_comb
              (actual_head, List.take (actual_args, depth))
        in
          { rank = locality_path_class_rank depth path_class,
            actual = actual_prefix,
            retrieve =
              retrieve depths path_class depth actual_prefix }
        end
      fun ranked_queries depths path_class =
        map (ranked_query depths path_class)
          (int_range_down argument_count 0)
    in
      if not shape_matches then []
      else
        (case indexed_paths of
           NONE => []
         | SOME depths =>
             maps (ranked_queries depths)
               locality_path_classes_by_rank)
    end

  fun locality_family_paths_with count context record_name kind head =
    locality_index_probe count (fn () =>
      let
        val family : locality_family_key =
          { record_name = record_name,
            kind = kind,
            head = locality_family_head head }
      in
        LocalityFamilyKeyTable.lookup
          (#families (LocalitySecondaryIndex.get context)) family
      end)

  fun locality_int_range first last =
    if first > last then [] else first upto last

  fun locality_int_range_down first last =
    if first < last then []
    else first :: locality_int_range_down (first - 1) last

  fun locality_application_keys_with count ctxt record_name kind
        head args =
    let
      val argument_count = length args
      fun add_slot path_class actual slots slot keys =
        (case locality_index_probe count (fn () =>
                Inttab.lookup slots slot) of
           NONE => keys
         | SOME path =>
             merge_locality_key_sets
               (keys,
                locality_path_class_keys_with
                  count actual path_class path))
      fun add_arity path_class actual arities arity keys =
        (case locality_index_probe count (fn () =>
                Inttab.lookup arities arity) of
           NONE => keys
         | SOME slots =>
             fold (add_slot path_class actual slots)
               (locality_int_range 0 (arity - 1)) keys)
      fun retrieve depths path_class depth actual () =
        (case locality_index_probe count (fn () =>
                Inttab.lookup depths depth) of
           NONE => empty_locality_key_set
         | SOME arities =>
             fold (add_arity path_class actual arities)
               (locality_int_range 0 (argument_count - depth))
               empty_locality_key_set)
      fun ranked_query depths path_class depth =
        let
          val actual =
            Term.list_comb (head, List.take (args, depth))
        in
          { rank = locality_path_class_rank depth path_class,
            actual = actual,
            retrieve = retrieve depths path_class depth actual }
        end
      fun ranked_queries depths path_class =
        map (ranked_query depths path_class)
          (locality_int_range_down argument_count 0)
    in
      case locality_family_paths_with
             count (Context.Proof ctxt) record_name kind head of
        NONE => empty_locality_key_set
      | SOME depths =>
          maps (ranked_queries depths) locality_path_classes_by_rank
          |> locality_maximal_rank_keys_with count ctxt
    end

  fun locality_pattern_keys_with count ctxt record_name kind pattern =
    let
      val (head, prefix_args) = Term.strip_comb pattern
      val depth = length prefix_args
      val max_arity =
        length (Term.binder_types (Term.type_of pattern))
      fun add_slot path_class slots slot keys =
        (case locality_index_probe count (fn () =>
                Inttab.lookup slots slot) of
           NONE => keys
         | SOME path =>
             merge_locality_key_sets
               (keys,
                locality_path_class_keys_with
                  count pattern path_class path))
      fun add_arity path_class arities arity keys =
        (case locality_index_probe count (fn () =>
                Inttab.lookup arities arity) of
           NONE => keys
         | SOME slots =>
             fold (add_slot path_class slots)
               (locality_int_range 0 (arity - 1)) keys)
      fun retrieve arities path_class () =
        fold (add_arity path_class arities)
          (locality_int_range 0 max_arity)
          empty_locality_key_set
      fun ranked_query arities path_class =
        { rank = locality_path_class_rank depth path_class,
          actual = pattern,
          retrieve = retrieve arities path_class }
    in
      case locality_family_paths_with
             count (Context.Proof ctxt) record_name kind head of
        NONE => empty_locality_key_set
      | SOME depths =>
          (case locality_index_probe count (fn () =>
                  Inttab.lookup depths depth) of
             NONE => empty_locality_key_set
           | SOME arities =>
               map (ranked_query arities)
                 locality_path_classes_by_rank
               |> locality_maximal_rank_keys_with count ctxt)
    end

  fun locality_pattern_at_idx_keys_with count ctxt record_name kind
        pattern absolute_idx =
    let
      val (head, prefix_args) = Term.strip_comb pattern
      val depth = length prefix_args
      val relative_idx = absolute_idx - depth
      val max_arity =
        length (Term.binder_types (Term.type_of pattern))
      fun add_arity path_class arities arity keys =
        (case locality_index_probe count (fn () =>
                Inttab.lookup arities arity) of
           NONE => keys
         | SOME slots =>
             (case locality_index_probe count (fn () =>
                     Inttab.lookup slots relative_idx) of
                NONE => keys
              | SOME path =>
                  merge_locality_key_sets
                    (keys,
                     locality_path_class_keys_with
                       count pattern path_class path)))
      fun retrieve arities path_class () =
        fold (add_arity path_class arities)
          (locality_int_range (relative_idx + 1) max_arity)
          empty_locality_key_set
      fun ranked_query arities path_class =
        { rank = locality_path_class_rank depth path_class,
          actual = pattern,
          retrieve = retrieve arities path_class }
    in
      if relative_idx < 0 then empty_locality_key_set
      else
        case locality_family_paths_with
               count (Context.Proof ctxt) record_name kind head of
          NONE => empty_locality_key_set
        | SOME depths =>
            (case locality_index_probe count (fn () =>
                    Inttab.lookup depths depth) of
               NONE => empty_locality_key_set
             | SOME arities =>
                 map (ranked_query arities)
                   locality_path_classes_by_rank
                 |> locality_maximal_rank_keys_with count ctxt)
    end

  fun locality_entries_for_keys_generic context keys =
    let
      val entries = RecordLocalityData.get context
      fun entry_of key =
        (case LocalityOperationalKeyTable.lookup entries key of
           SOME entry => entry
         | NONE =>
             error "Stale AutoLocality secondary operational key")
    in
      map entry_of keys
    end

  fun describe_locality_dispatch_key
        (dispatch_key : locality_dispatch_key) =
    quote (#head_name dispatch_key)
      ^ " at full application arity "
      ^ Int.toString (#arity dispatch_key)

  fun canonical_locality_dispatcher_alias (alias0, alias1) =
    if fast_string_ord (alias0, alias1) = GREATER
    then alias1
    else alias0

  type locality_dispatcher_inventory_entry = {
    origin: stamp,
    source_name: string,
    alias: string
  }

  fun merge_locality_dispatcher_inventory_entry dispatch_key
        (entry0 : locality_dispatcher_inventory_entry,
         entry1 : locality_dispatcher_inventory_entry) =
    if #origin entry0 <> #origin entry1 then
      error ("Conflicting independent AutoLocality dispatchers for "
        ^ describe_locality_dispatch_key dispatch_key)
    else if #source_name entry0 <> #source_name entry1 then
      error ("Inconsistent AutoLocality source dispatcher names for "
        ^ describe_locality_dispatch_key dispatch_key)
    else
      { origin = #origin entry0,
        source_name = #source_name entry0,
        alias =
          canonical_locality_dispatcher_alias
            (#alias entry0, #alias entry1) }

  fun insert_locality_dispatcher_alias dispatch_key origin
        source_name alias inventory =
    LocalityDispatchKeyTable.map_default
      (dispatch_key,
       { origin = origin,
         source_name = source_name,
         alias = alias })
      (fn entry =>
        merge_locality_dispatcher_inventory_entry dispatch_key
          (entry,
           { origin = origin,
             source_name = source_name,
             alias = alias }))
      inventory

  fun merge_locality_dispatcher_inventories inventories =
    LocalityDispatchKeyTable.join
      merge_locality_dispatcher_inventory_entry inventories

  \<comment>\<open>Local inventory of named generic dispatchers. It contains no theorem payload and
     no declaration lineage. A private origin stamp distinguishes transport of one standard
     declaration from independently allocated sibling dispatchers. One deterministic alias
     per family is enough for \<^verbatim>\<open>[[locality_cancel]]\<close> to restore a representative after
     \<^verbatim>\<open>simp only:\<close> clears the ambient simpset.\<close>
  structure LocalityDispatcherInventory = Generic_Data
  (
    type T =
      locality_dispatcher_inventory_entry
        LocalityDispatchKeyTable.table;
    val empty = LocalityDispatchKeyTable.empty;
    val merge = merge_locality_dispatcher_inventories;
  );

  fun locality_dispatcher_entry context dispatch_key =
    LocalityDispatchKeyTable.lookup
      (LocalityDispatcherInventory.get context) dispatch_key

  fun locality_dispatcher_declared context dispatch_key =
    Option.isSome (locality_dispatcher_entry context dispatch_key)

  \<comment>\<open>Register the footprint for a new attribute/operation.\<close>
  fun add_record_locality_entry_generic ctxt (rec_name : string)
        (entry : locality_entry) context =
    let
      val _ =
        if rec_name = locality_entry_record_name entry then ()
        else locality_entry_conflict entry "record identities differ"
      val replay =
        LocalityOperationalKeyTable.defined
          (RecordLocalityData.get context) (#key entry)
      val dispatch_key =
        if locality_entry_kind entry = Locality_Attribute
        then locality_dispatch_key_of_entry_opt ctxt entry
        else NONE
      val _ = locality_pretty_trace ctxt 1 (fn () =>
        Pretty.text "Registering footprint"
        @ [Pretty.brk 1,
           Pretty.list "[" "]" (List.map Pretty.str (#footprint entry)),
           Pretty.brk 1]
        @ Pretty.text "for term"
        @ [Pretty.brk 1, Syntax.pretty_term ctxt (#pattern entry), Pretty.brk 1]
        @ Pretty.text "for record" @ [Pretty.brk 1, Pretty.str rec_name]
        |> Pretty.block)
    in
      case Exn.capture
          (RecordLocalityData.map (insert_locality_entry entry)) context of
        Exn.Res context' =>
          let
            val context'' =
              if replay then context'
              else
                LocalitySecondaryIndex.map
                  (insert_locality_secondary_key_with_dispatch
                    dispatch_key entry) context'
            val ctxt' = Context.proof_of context''
            val _ =
              AutoLocality_Instrumentation.record_counters ctxt' (fn () =>
                let
                  val counter =
                    if replay
                    then AutoLocality_Instrumentation.Lifecycle_Replays
                    else
                      AutoLocality_Instrumentation.Lifecycle_Semantic_Insertions
                  val index_counters =
                    if replay then []
                    else
                      [(AutoLocality_Instrumentation.Index_Nodes,
                        if locality_entry_kind entry = Locality_Attribute
                        then 5 else 4),
                       (AutoLocality_Instrumentation.Index_Secondary_Insertions,
                        1)]
                in (counter, 1) :: index_counters end)
          in context'' end
      | Exn.Exn exn =>
          if Exn.is_interrupt exn then Exn.reraise exn
          else
            let
              val _ =
                AutoLocality_Instrumentation.record_counters ctxt (fn () =>
                  [(AutoLocality_Instrumentation.Lifecycle_Conflicts, 1)])
            in Exn.reraise exn end
    end

  \<comment>\<open>Lookup the footprint data associated with a record, as an association list.\<close>
  val get_record_locality_data_generic : Context.generic -> (Symtab.key * locality_entry) list
   = RecordLocalityData.get
     #> LocalityOperationalKeyTable.dest
     #> map (fn (key, entry) => (#record_name key, entry))

  val get_record_locality_data = Context.Proof #>  get_record_locality_data_generic
  val get_record_locality_data_raw_generic = RecordLocalityData.get

  \<comment>\<open>Get list of records that we manage any footprint information about\<close>
  val get_registered_records =
    Context.Proof
    #> LocalitySecondaryIndex.get
    #> #records
    #> Symtab.keys
  
  \<comment>\<open>Lookup footprint data for record\<close>
  fun get_record_locality_data_for_record_generic r ctxt : locality_entry list option =
    let
      val keys =
        Symtab.lookup (#records (LocalitySecondaryIndex.get ctxt)) r
        |> Option.map LocalityOperationalKeyTable.keys
      val entries =
        Option.map (locality_entries_for_keys_generic ctxt) keys
    in
      case entries of
        SOME (_ :: _) => entries
      | _ => NONE
    end

  fun get_record_locality_data_for_record r = Context.Proof #> get_record_locality_data_for_record_generic r
  fun has_record_locality_data_for_record r ctxt = get_record_locality_data_for_record r ctxt |> Option.isSome

  \<comment>\<open>Lookup all registered attributes for a record\<close>
  fun get_attributes ctxt = ctxt
     |> get_record_locality_data
     |> List.filter (fn (_, e : locality_entry) =>
          locality_entry_kind e = Locality_Attribute)

  fun get_record_locality_entries_generic (r : string) ctxt =
    case get_record_locality_data_for_record_generic r ctxt of
       NONE => []
     | SOME entries => entries

  fun get_record_locality_entries (r : string) =
    Context.Proof #> get_record_locality_entries_generic r

  fun get_record_locality_entries_for_const_generic (r : string) (c : string) ctxt =
    let
      val keys =
        Symtab.lookup (#names (LocalitySecondaryIndex.get ctxt)) r
        |> Option.mapPartial (fn names => Symtab.lookup names c)
        |> Option.map LocalityOperationalKeyTable.keys
    in
      keys
      |> Option.map (locality_entries_for_keys_generic ctxt)
      |> the_default []
    end

  fun get_record_locality_entries_for_const (r : string) (c : string) =
    Context.Proof #> get_record_locality_entries_for_const_generic r c

  fun has_record_locality_entry_generic r c ctxt =
    not (null (get_record_locality_entries_for_const_generic r c ctxt))

  fun locality_registration_conflict ctxt rec_name pattern detail =
    let
      val count = locality_direct_counter ctxt
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lifecycle_Conflicts
    in
      error ("Conflicting autolocality registration for "
        ^ Syntax.string_of_term ctxt pattern ^ " on " ^ rec_name ^ ": " ^ detail)
    end

  fun locality_registration_is_replay ctxt rec_name const_name pattern
        flexible_prefix kind footprint args idx field expected_core_count
        expected_disjoint_count expect_local_thm =
    let
      val count = locality_direct_counter ctxt
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lifecycle_Registration_Attempts
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lookup_Requests
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lookup_Index_Probes
      val replay_key = locality_replay_key rec_name pattern idx
      val candidates =
        LocalityReplayKeyTable.lookup
          (#replay_slots
            (LocalitySecondaryIndex.get (Context.Proof ctxt)))
          replay_key
        |> Option.map LocalityOperationalKeyTable.keys
        |> Option.map
             (locality_entries_for_keys_generic (Context.Proof ctxt))
        |> the_default []
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Entries_Examined candidates
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Candidates_Returned candidates
      fun metadata_matches (entry : locality_entry) =
           #const_name entry = const_name
        andalso locality_entry_kind entry = kind
        andalso locality_entry_args entry = args
        andalso locality_entry_flexible_prefix entry = flexible_prefix
      fun payload_matches (entry : locality_entry) =
           eq_set (op =) (#footprint entry, footprint)
        andalso #field entry = field
      fun entry_is_complete (entry : locality_entry) =
           length (#core_thms entry) = expected_core_count
        andalso length (#disjoint_thms entry) = expected_disjoint_count
        andalso Option.isSome (#local_thm entry) = expect_local_thm
    in
      case candidates of
        [] => false
      | [entry] =>
          if not (metadata_matches entry) then
            locality_registration_conflict ctxt rec_name pattern
              "role, arity, constant identity, or flexible-prefix metadata differs"
          else if not (payload_matches entry) then
            locality_registration_conflict ctxt rec_name pattern
              "footprint or field metadata differs"
          else if not (entry_is_complete entry) then
            locality_registration_conflict ctxt rec_name pattern
              "the existing registration is incomplete"
          else
            (locality_count_one count
               AutoLocality_Instrumentation.Lifecycle_Replays;
             true)
      | _ =>
          locality_registration_conflict ctxt rec_name pattern
            "multiple entries occupy the same typed record slot"
    end

  fun locality_registration_replay_proof ctxt =
    \<comment>\<open>Keep the command's trailing proof terminator valid without
       publishing another theorem or declaration.\<close>
    Proof.theorem NONE (K I) [] ctxt

  fun prepare_rec_name (ctxt : Proof.context) (rec_name : string) =
    let
      val theory = Proof_Context.theory_of ctxt
      \<comment>\<open>Replace the type-name parser's arguments with fresh variables while retaining
         every sort constraint declared by datatype-record selectors or
         standard-record metadata. The bare type-name parser returns dummy
         arguments at sort {}, even when the generated constants retain
         stronger source-level constraints.\<close>
      fun prepare_typ ty =
        let
          val (base, args) = Term.dest_Type ty
          val declared_sorts =
            (case Ctr_Sugar.ctr_sugar_of ctxt base of
               SOME sugar =>
                 (case #selss sugar of
                    (sel :: _) :: _ =>
                      (case Term.domain_type (Term.type_of sel) of
                         Type (base', selector_args) =>
                           if base = base'
                           then map Type.sort_of_atyp selector_args
                           else replicate (length args) []
                       | _ => replicate (length args) [])
                  | _ => replicate (length args) [])
             | NONE =>
                 (case Record.get_info theory base of
                    SOME info => map snd (#args info)
                  | NONE => replicate (length args) []))
          fun prepare_arg (i, arg) =
            let
              val parsed_sort = Type.sort_of_atyp arg handle TYPE _ => []
              val declared_sort = nth declared_sorts i
            in
              TVar (("?'a", i),
                if null parsed_sort then declared_sort else parsed_sort)
            end
        in
          Type (base, map_index prepare_arg args)
        end
      val prepared_rec_ty = rec_name
        |> Proof_Context.read_type_name {proper = true, strict = false} ctxt
        |> prepare_typ
      val (rec_name_full, _) = prepared_rec_ty |> dest_Type
      val rec_ty =
        if Option.isSome (Record.get_info theory rec_name_full)
        then Sign.certify_typ_mode Type.mode_default theory prepared_rec_ty
        else prepared_rec_ty
    in
       (rec_ty, rec_name_full)
    end

  \<comment>\<open>Pretty printing helper\<close>
  fun pretty_locality_entry ctxt rec_name (entry : locality_entry) =
    let
      val (rec_ty, _) = prepare_rec_name ctxt rec_name
      val pattern = #pattern entry
      val fp = #footprint entry
      val idx = locality_entry_idx entry
    in
      Pretty.text "On record"
       @ [Pretty.brk 1, Syntax.pretty_typ ctxt rec_ty]
       @ Pretty.text "," @ [Pretty.brk 1,
       Syntax.pretty_term ctxt pattern, Pretty.brk 1]
       @ [Pretty.enclose "(" ")" (
            [Pretty.str "arg:", Pretty.str (Int.toString idx)] |> Pretty.breaks),
          Pretty.brk 1]
       @ Pretty.text "has footprint:" @ [Pretty.brk 1, Pretty.list "[" "]" (List.map Pretty.str fp)]
      |> Pretty.block
    end

  \<comment>\<open>Print all footprint data associated with a given record\<close>
  fun print_locality_data_for_record (ctxt : Proof.context) (rec_name : string) =
     let val (_, rec_name) = prepare_rec_name ctxt rec_name
         val data = (get_record_locality_data_for_record_generic rec_name (Context.Proof ctxt)
                  |> curry Option.getOpt) []
         val _ = List.map (pretty_locality_entry ctxt rec_name) data
                 |> Pretty.chunks |> Pretty.writeln
     in
       ()
     end

  \<comment>\<open>Print all footprint data associated with any record\<close>
  fun print_locality_data_for_all_records (ctxt : Proof.context) =
     let val recs = get_registered_records ctxt in
        (List.map (print_locality_data_for_record ctxt) recs); ()
     end

  \<comment>\<open>Print locality data for either all or a specific record\<close>
  fun print_locality_data (rec_name_opt : string option) ctxt =
     ((case rec_name_opt of
        NONE => print_locality_data_for_all_records ctxt
      | SOME rec_name => print_locality_data_for_record ctxt rec_name); ctxt)

  fun string_to_identifier s = s
    |> String.explode |> List.map (fn c => if c = #" " orelse c = #"." then #"_" else c)
                      |> List.map (fn c => if c = #"'" then #"P" else c)
    |> List.filter (fn c => Char.isAlphaNum c orelse c = #"_")
    |> String.implode

  fun locality_public_id ctxt pattern =
    let
      val cname = extract_const pattern
      val has_baked_const =
        snd (Term.strip_comb pattern)
        |> exists (fn arg => case Term.head_of arg of Const _ => true | _ => false)
    in
      if has_baked_const
      then string_to_identifier (Syntax.pretty_term ctxt pattern |> Pretty.pure_string_of)
      else string_to_identifier (Long_Name.base_name cname)
    end

  fun assert_locality_public_id_available ctxt rec_name kind idx public_id pattern =
    let
      val conflicts =
        get_record_locality_entries rec_name ctxt
        |> List.filter (fn (entry : locality_entry) =>
             locality_entry_kind entry = kind
             andalso locality_entry_idx entry = idx
             andalso locality_public_id ctxt (#pattern entry) = public_id
             andalso not (locality_registration_pattern_eq ctxt
               (#pattern entry, pattern)))
    in
      case conflicts of
        [] => ()
      | entry :: _ =>
          let
            val count = locality_direct_counter ctxt
            val _ = locality_count_one count
              AutoLocality_Instrumentation.Lifecycle_Conflicts
          in
            error ("Autolocality generated-name collision for " ^ public_id
              ^ " on " ^ rec_name ^ " between "
              ^ Syntax.string_of_term ctxt (#pattern entry) ^ " and "
              ^ Syntax.string_of_term ctxt pattern)
          end
    end

  fun register_locality_op_commutativity_thm_name rec_name c = 
    (string_to_identifier rec_name) ^ "_local_op_" ^ c ^ "_core"
  fun register_locality_op_disjointness_thm_name rec_name c = 
    (string_to_identifier rec_name) ^ "_local_op_" ^ c ^ "_disjoint"
  fun register_locality_op_local_action_thm_name rec_name c = 
    (string_to_identifier rec_name) ^ "_local_op_" ^ c ^ "_local"

  fun register_locality_attr_cancellation_thm_name rec_name c i =
    (rec_name |> string_to_identifier) ^ "_local_attr_" ^ c ^ "_" ^ (Int.toString i) ^ "_core"
  fun register_locality_attr_cancellation_thm_list_name rec_name c i =
    (rec_name |> string_to_identifier) ^ "_local_attr_" ^ c ^ "_" ^ (Int.toString i) ^ "_cancel"

  \<comment>\<open>Physical dispatcher bindings encode the complete long-name component
     sequence. Each original component has an indexed byte-length/chunk-count frame followed
     by indexed fixed-size hexadecimal payload chunks. The component count and arity have
     separate frames, and the fixed base name remains below Isabelle's long-name range limit.\<close>
  val locality_dispatch_hex_payload_limit = 16000

  fun locality_dispatch_hex_byte byte =
    let
      val value = Word8.toInt byte
    in
      hex_digit (value div 16) ^ hex_digit (value mod 16)
    end

  fun locality_dispatch_hex_chunks encoded =
    let
      val encoded_size = size encoded
      fun chunks offset =
        if offset >= encoded_size then []
        else
          let
            val chunk_size =
              Int.min
                (locality_dispatch_hex_payload_limit,
                 encoded_size - offset)
          in
            String.substring (encoded, offset, chunk_size)
              :: chunks (offset + chunk_size)
          end
    in
      if encoded_size = 0 then [""] else chunks 0
    end

  fun locality_dispatch_name_components
        (component_index, component) =
    let
      val bytes = Byte.stringToBytes component
      val encoded =
        Word8Vector.foldr
          (fn (byte, suffix) =>
            locality_dispatch_hex_byte byte :: suffix)
          [] bytes
        |> String.concat
      val payloads = locality_dispatch_hex_chunks encoded
      val component_index_string = Int.toString component_index
      val header =
        "c" ^ component_index_string
        ^ "_b" ^ Int.toString (Word8Vector.length bytes)
        ^ "_n" ^ Int.toString (length payloads)
      val payload_components =
        payloads
        |> map_index (fn (payload_index, payload) =>
             "c" ^ component_index_string
             ^ "_p" ^ Int.toString payload_index
             ^ "_" ^ payload)
    in
      header :: payload_components
    end

  fun register_locality_dispatch_simproc_components head_name arity =
    let
      val _ =
        if arity >= 0 then ()
        else error "Negative AutoLocality dispatcher arity"
      val components = Long_Name.explode head_name
      val encoded_components =
        components
        |> map_index locality_dispatch_name_components
        |> flat
    in
      ["autolocality_dispatch_v1",
       "k" ^ Int.toString (length components)]
      @ encoded_components
      @ ["a" ^ Int.toString arity,
         "autolocality_locality_dispatch_simproc"]
    end

  fun register_locality_dispatch_simproc_name head_name arity =
    register_locality_dispatch_simproc_components head_name arity
    |> Long_Name.implode

  fun locality_dispatch_simproc_components
        (dispatch_key : locality_dispatch_key) =
    register_locality_dispatch_simproc_components
      (#head_name dispatch_key) (#arity dispatch_key)

  fun locality_dispatch_simproc_binding dispatch_key =
    let
      val (qualifiers, base_name) =
        split_last (locality_dispatch_simproc_components dispatch_key)
    in
      Binding.name base_name
      |> fold_rev (Binding.qualify true) qualifiers
    end

  fun locality_dispatch_simproc_name dispatch_key =
    locality_dispatch_simproc_binding dispatch_key
    |> Binding.long_name_of

  fun default_named_theorems_for_record (rec_name : string) =
    (rec_name |> string_to_identifier) ^ "_locality_facts"

  fun strip_prefix (prefix : string) (s : string) : string option =
     if String.isPrefix prefix s then
        SOME (String.extract (s, size prefix, NONE))
     else
        NONE

  val strlist_to_str = String.concatWith ", "
  fun dest_field_update const =
    let val base = Long_Name.base_name const in
      case strip_prefix "update_" base of
        SOME field => SOME field
      | NONE => try (unsuffix Record.updateN) base
    end

  fun fieldlist_to_str fs = "[" ^ (strlist_to_str fs) ^ "]"

  fun unpack_attributes_default (ctxt : Proof.context) (rec_name : string) attribs_opt =
     case attribs_opt of
         SOME attribs => attribs
       | NONE => let val default_thms = default_named_theorems_for_record rec_name
                     val attr = Token.explode0 (Thy_Header.get_keywords' ctxt) default_thms
                 in [attr] end

\<close>
subsection\<open>Complex hoisting and cancellations using \<^verbatim>\<open>simproc\<close>\<close>

text\<open>
  The existing cancellation and commutativity lemmas are not always enough to identify all
  footprint-based simplifications. For example, it can happen that in a term \<^verbatim>\<open>attr (f (g r))\<close>
  the operation \<^verbatim>\<open>g\<close> can be cancelled with \<^verbatim>\<open>attr\<close>, but the cancellation lemma does not trigger
  because \<^verbatim>\<open>f\<close> -- which may well \<^emph>\<open>not\<close> be cancellable with \<^verbatim>\<open>attr\<close> -- blocks it. In this case,
  \<^emph>\<open>if\<close> \<^verbatim>\<open>f\<close> and \<^verbatim>\<open>g\<close> commute, one can swap them first and then cancel \<^verbatim>\<open>g\<close> with \<^verbatim>\<open>attr\<close>. This is
  what the simproc developed in this section does.

  Note that the general situation is more complicated since any attribute and operation can have
  an arbitrary number of additional arguments which need to be managed and tracked. Also, there is
  a priori not maximum depths for detecting possible cancellations: The above example could be
  complicated to \<^verbatim>\<open>attr (f0 (f1 (f2( ... (g x)))))\<close> which requires commuting \<^verbatim>\<open>g\<close> past all \<^verbatim>\<open>f_i\<close>
  first before it can be cancelled with \<^verbatim>\<open>attr\<close>.

  See \<^file>\<open>AutoLocality_Tests/AutoLocality_Test_Cancel.thy\<close> for an example of the resulting
  simproc \<^verbatim>\<open>locality_cancel\<close>.
\<close>

ML\<open>
  type 'a op_term_with_gap = 'a * (term * term list * term list)

  \<comment>\<open>Recursively zooms into an argument of a term, according to a picker function, retaining
     the previous and following arguments.\<close>
  fun strip_comb_iter_with count
        (picker : term -> term list -> (int * 'a) option)
        (t : term) : 'a op_term_with_gap list * term =
    let
      fun core (acc_rev : 'a op_term_with_gap list) (t : term) =
         let
           val (head, args) = t |> Term.strip_comb
           val iter = picker head args
         in
           case iter of
              NONE =>
                let
                  val _ = locality_count_int count
                    AutoLocality_Instrumentation.Planner_Tail_Copies
                    (fn () => length acc_rev)
                in (rev acc_rev, t) end
            | SOME (idx, data) =>
                core ((data, (head, List.take (args, idx),
                  List.drop (args, idx + 1))) :: acc_rev)
                  (List.nth (args, idx))
         end
    in
      core [] t
    end

  fun strip_comb_iter picker t =
    strip_comb_iter_with locality_no_count picker t

  \<comment>\<open>This is a left inverse to \<^verbatim>\<open>strip_comb_iter\<close>\<close>
  fun recombine_decomposed_comb_with _ ([], body) = body
    | recombine_decomposed_comb_with count
        (((_, (head, pre, suf)) :: inner), body) =
        let
          val r = recombine_decomposed_comb_with count (inner, body)
          val _ = locality_count_int count
            AutoLocality_Instrumentation.Planner_Application_Frames
            (fn () => length pre + 1 + length suf)
          val _ = locality_count_int count
            AutoLocality_Instrumentation.Planner_Tail_Copies
            (fn () => 2 * length pre + 1)
        in
          Term.list_comb (head, pre @ [r] @ suf)
        end

  fun recombine_decomposed_comb decomp =
    recombine_decomposed_comb_with locality_no_count decomp

  fun fun_conv_many (f_conv: conv) (arg_convs: conv list) =
     List.foldl (fn (arg, f) => Conv.combination_conv f arg) f_conv arg_convs

  fun arg_convN num_args n conv = 
     fun_conv_many Conv.all_conv (replicate (Int.max(0,n - 1)) Conv.all_conv @ [conv] @ replicate (num_args - n - 1) Conv.all_conv)

  fun op_term_with_gap_conv ([], _) _ = Conv.all_conv
     | op_term_with_gap_conv ((_, (_, pre, post)) :: ls, t) conv = 
         let val arg_convs = List.map (K Conv.all_conv) pre @ [op_term_with_gap_conv (ls, t) conv] @ List.map (K Conv.all_conv) post
         in
             fun_conv_many conv arg_convs
         end      

  fun op_term_with_gap_conv_with count
        ([], _) (_: conv) (_: conv -> conv) =
        (locality_count_one count
           AutoLocality_Instrumentation.Planner_Base_Child_Builds;
         Conv.all_conv)
     | op_term_with_gap_conv_with count
         ((_, (_, pre, post)) :: ls, t)
         (conv: conv) (step_conv: conv -> conv) =
         let
           val _ = locality_count_one count
             AutoLocality_Instrumentation.Planner_Recursive_Node_Builds
           val _ = locality_count_one count
             AutoLocality_Instrumentation.Planner_Context_Lifts
           val _ = locality_count_int count
             AutoLocality_Instrumentation.Planner_Application_Frames
             (fn () => length pre + 1 + length post)
           val _ = locality_count_one count
             AutoLocality_Instrumentation.Planner_Tail_Copies
           val child_conv =
             op_term_with_gap_conv_with count (ls, t) conv step_conv
             |> Conv.cache_conv
           val arg_convs =
             List.map (K Conv.all_conv) pre
             @ [child_conv]
             @ List.map (K Conv.all_conv) post
         in
             (conv then_conv
               (step_conv (Conv.try_conv child_conv)))
             else_conv (fun_conv_many Conv.all_conv arg_convs)
         end

  fun op_term_with_gap_conv' decomp conv step_conv =
    op_term_with_gap_conv_with locality_no_count decomp conv step_conv
\<close>

text\<open>A small experiment demonstrating what \<^verbatim>\<open>strip_comb_iter\<close> does. Here, we always pick
the second argument of a function application.\<close>

experiment
begin
ML\<open>local
  \<comment>\<open>Zoom into the second argumet of a term application\<close>
  fun picker_second (_ : term) (args : term list) : (int * unit) option =
     if length args < 2 then
       NONE
     else
       SOME (1, ())

  \<comment>\<open>Helper function to pretty-print the result of \<^verbatim>\<open>strip_comb_iter\<close>\<close>
  fun print_strip_comb_iter_result (ctxt : Proof.context)
     ([], t) = [Syntax.pretty_term ctxt t]
   | print_strip_comb_iter_result ctxt ((_, (cur, pre, post)) :: ls, t) =
         Pretty.fbreaks ([Syntax.pretty_term ctxt cur]
          @ List.map (Syntax.pretty_term ctxt) pre
          @ [Pretty.block (print_strip_comb_iter_result ctxt (ls, t))]
          @ List.map (Syntax.pretty_term ctxt) post)

  val t = @{term \<open>f (g0 a00 a01) (g1 a10 (g11 a110 a111)) (g2 a20 a21)\<close>}
  val t_decomp = t |> strip_comb_iter picker_second 
  val t_recomb = t_decomp |> recombine_decomposed_comb
in
  val _ = t_decomp |> print_strip_comb_iter_result @{context} 
                   |> Pretty.block 
                   |> Pretty.writeln
  val _ = Syntax.pretty_term @{context} t |> Pretty.writeln
  val _ = Syntax.pretty_term @{context} t_recomb |> Pretty.writeln
end\<close>

end

ML\<open>
  fun locality_varify_atyps tfrees base =
    let
      val instantiations =
        tfrees |> map_index (fn (i, (name, sort)) =>
          ((name, sort), TVar ((name, base + i), sort)))
    in
      fn TFree key =>
           AList.lookup (op =) instantiations key
           |> the_default (TFree key)
       | typ => typ
    end

  \<comment>\<open>Turn fixed type variables into fresh schematic variables while retaining any
     schematic variables already introduced by a declaration morphism. Isabelle's
     global varifier rejects mixed TFree/TVar terms, which occur for polymorphic
     datatype-record fields after local-theory transport.\<close>
  fun locality_varify_typ typ =
    let
      val tfrees = Term.add_tfreesT typ []
      val base = Term.maxidx_of_typ typ + 1
    in
      Term.map_atyps (locality_varify_atyps tfrees base) typ
    end

  fun locality_varify_types term =
    let
      val tfrees = Term.add_tfrees term []
      val base = Term.maxidx_of_term term + 1
    in
      Term.map_types
        (Term.map_atyps (locality_varify_atyps tfrees base)) term
    end

  fun locality_assumption_tfrees ctxt =
    fold (fn cterm => Term.add_tfrees (Thm.term_of cterm))
      (Assumption.all_assms_of ctxt) []

  \<comment>\<open>Locale definition equations carry the locale predicate as a hidden theorem
     hypothesis. Type frees shared with that predicate must remain fixed while proving the
     certificate: schematizing them independently makes the definition equation unusable even
     though it is available in the local proof context. Other type frees remain schematic, which
     preserves polymorphic registrations and deliberately supports mixed TFree/TVar terms.\<close>
  fun locality_varify_types_preserving protected_tfrees term =
    let
      val tfrees =
        Term.add_tfrees term []
        |> filter_out (member (op =) protected_tfrees)
      val base = Term.maxidx_of_term term + 1
    in
      Term.map_types
        (Term.map_atyps (locality_varify_atyps tfrees base)) term
    end

  fun locality_entry_prefix_length (entry : locality_entry) =
    length (snd (Term.strip_comb (#pattern entry)))

  fun locality_entry_absolute_idx (entry : locality_entry) =
    locality_entry_prefix_length entry + locality_entry_idx entry

  fun locality_entry_match_pattern (entry : locality_entry) =
    locality_match_pattern
      (#pattern entry) (locality_entry_flexible_prefix entry)

  fun locality_entry_flexible_pairs ctxt (actual : term) (entry : locality_entry) =
    locality_pattern_flexible_pairs ctxt actual
      (#pattern entry) (locality_entry_flexible_prefix entry)

  fun locality_entry_matches_prefix_with count ctxt
        (actual : term) (entry : locality_entry) =
    locality_pattern_matches_prefix_with count ctxt actual
      (#pattern entry) (locality_entry_flexible_prefix entry)

  fun locality_entry_matches_prefix ctxt actual entry =
    locality_entry_matches_prefix_with locality_no_count ctxt actual entry

  \<comment>\<open>Locale declarations are transported with the concrete interpretation term that was
     supplied to the locale machinery. Isabelle may subsequently print or parse a provably equal
     term (for example, @{term Suc} instead of @{term "\<lambda>n. n + 1"}). Matching such a prefix is
     not enough: the stored certificates must also be rewritten to that actual typed prefix before
     conversion can consume them. Keep this specialization local to the lookup; the context data
     retains the declaration's canonical transported entry.\<close>
  fun locality_specialize_entry_with count ctxt
        (actual : term) (entry : locality_entry) : locality_entry =
    let
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lookup_Specializations
      fun prove_rewrite (stored, actual) =
        if Term.aconv (stored, actual) then NONE
        else SOME (Goal.prove ctxt [] [] (Logic.mk_equals (stored, actual))
          (fn {context, ...} =>
            asm_full_simp_tac (context addsimps @{thms fun_eq_iff}) 1))
      val rewrites =
        locality_entry_flexible_pairs ctxt actual entry
        |> map_filter prove_rewrite
      fun rewrite_thm thm =
        thm
        |> Thm.transfer' ctxt
        |> fold (fn rewrite =>
             Conv.fconv_rule
               (Conv.try_conv (Conv.bottom_rewrs_conv [rewrite] ctxt)))
             rewrites
      fun specialize core_thms disjoint_thms local_thm =
        { key = #key entry,
          const_name = #const_name entry,
          pattern = actual,
          footprint = #footprint entry,
          field = #field entry,
          core_thms = core_thms,
          disjoint_thms = disjoint_thms,
          local_thm = local_thm }
    in
      if null rewrites then
        if Term.aconv (#pattern entry, actual) then entry
        else specialize (#core_thms entry) (#disjoint_thms entry) (#local_thm entry)
      else specialize
        (map rewrite_thm (#core_thms entry))
        (map rewrite_thm (#disjoint_thms entry))
        (Option.map rewrite_thm (#local_thm entry))
    end

  fun locality_specialize_entry ctxt actual entry =
    locality_specialize_entry_with locality_no_count ctxt actual entry

  fun locality_entry_matches_application_with count ctxt
        (head : term) (args : term list) (entry : locality_entry) =
    let
      val prefix_length = locality_entry_prefix_length entry
    in
      length args >= prefix_length + locality_entry_args entry andalso
      locality_entry_matches_prefix_with count ctxt
        (Term.list_comb (head, List.take (args, prefix_length))) entry
    end

  fun locality_entry_matches_application ctxt head args entry =
    locality_entry_matches_application_with locality_no_count ctxt head args entry

  fun locality_entries_have_same_effect_with count
        (entries : locality_entry list) =
    case entries of
      [] => true
    | entry :: entries' =>
        fold (fn entry' => fn same_effect =>
          let
            val _ = locality_count_one count
              AutoLocality_Instrumentation.Lookup_Comparisons
            val same_effect' =
              locality_entry_kind entry = locality_entry_kind entry'
              andalso locality_entry_absolute_idx entry =
                locality_entry_absolute_idx entry'
              andalso eq_set (op =)
                (#footprint entry, #footprint entry')
          in
            same_effect andalso same_effect'
          end) entries' true

  fun locality_entries_have_same_effect entries =
    locality_entries_have_same_effect_with locality_no_count entries

  \<comment>\<open>Select the most specific typed registration matching an application. Exact typed
     matches take precedence over schematic polymorphic matches, rigid prefixes over flexible
     prefixes, and longer registered partial applications over shorter ones. Remaining compatible
     duplicates are harmless import-diamond replays. Incompatible matches are rejected instead of
     selecting the first entry by constant name.\<close>
  fun select_locality_entry_kind_with count ctxt
        (rec_name : string) kind
        (head : term) (args : term list) =
    let
      val context = Context.Proof ctxt
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lookup_Requests
      val candidates =
        locality_application_keys_with
          count ctxt rec_name kind head args
        |> LocalityOperationalKeyTable.keys
        |> locality_entries_for_keys_generic context
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Entries_Examined candidates
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Candidates_Returned candidates
    in
      case candidates of
        [] => NONE
      | entry :: _ =>
          if locality_entries_have_same_effect_with count candidates then
            let
              val n = locality_entry_prefix_length entry
              val actual = Term.list_comb (head, List.take (args, n))
            in
              SOME (locality_entry_absolute_idx entry,
                locality_specialize_entry_with count ctxt actual entry)
            end
          else
            locality_registry_ambiguity
              ("Ambiguous autolocality registrations on " ^ rec_name)
    end

  fun select_locality_entry_with count ctxt rec_name kind_name head args =
    select_locality_entry_kind_with count ctxt rec_name
      (locality_entry_kind_of_string kind_name) head args

  fun select_locality_entry ctxt rec_name kind_name head args =
    select_locality_entry_with locality_no_count ctxt
      rec_name kind_name head args

  \<comment>\<open>Picker for operations inside an attribute's record telescope.\<close>
  fun locality_operation_picker_with count ctxt rec_name head args =
    select_locality_entry_kind_with count ctxt rec_name
      Locality_Operation head args

  fun locality_operation_picker ctxt rec_name head args =
    locality_operation_picker_with locality_no_count ctxt rec_name head args

  fun disjoint_footprint (fpA : string list) (fpB : string list) =
     length (Library.inter (op =) fpA fpB) = 0

  fun disjoint_entries (e : locality_entry) (f : locality_entry) =
     disjoint_footprint (#footprint e) (#footprint f)

  fun merge_footprints (fpA : string list) (fpB : string list) =
    Library.merge (op =) (fpA, fpB)

  fun lift_redundant_operations_core_with count front back fp entries =
    let
      fun core front_rev back_rev _ [] =
            let
              val _ = locality_count_int count
                AutoLocality_Instrumentation.Planner_Tail_Copies
                (fn () => length front + length back
                  + length front_rev + length back_rev)
            in
              (front @ rev front_rev, back @ rev back_rev)
            end
        | core front_rev back_rev footprint
            ((e : locality_entry, f) :: efs) =
            if disjoint_footprint footprint (#footprint e) then
              core ((e, f) :: front_rev) back_rev footprint efs
            else
              core front_rev ((e, f) :: back_rev)
                (merge_footprints footprint (#footprint e)) efs
    in
      core [] [] fp entries
    end

  fun lift_redundant_operations_core front back fp entries =
    lift_redundant_operations_core_with locality_no_count
      front back fp entries

  \<comment>\<open>If the toplevel term is an attribute on a record, look for operations applied to the
  record argument that can be hoisted out and cancelled.

  For example, if \<^verbatim>\<open>attr ?x (?r :: 'rec) ?y\<close> is an attribute on record \<^verbatim>\<open>'rec\<close> with footprint
  \<^verbatim>\<open>{a,b}\<close>, say, \<^verbatim>\<open>opA ?r ?z\<close> is an operation on \<^verbatim>\<open>'rec\<close> with footprint \<^verbatim>\<open>{a, c}\<close>, and \<^verbatim>\<open>opB ?w ?r\<close>
  is another operation on \<^verbatim>\<open>'rec\<close> with footprintb \<^verbatim>\<open>{d, e}\<close>, then \<^verbatim>\<open>opB\<close> can be hoisted in the
  term \<^verbatim>\<open>attr x (opA (opB w r) z) y\<close>, giving \<^verbatim>\<open>attr x (opB w (opA r z) y\<close>.

  Note if \<^verbatim>\<open>opB\<close> had footprint \<^verbatim>\<open>{c, d}\<close>, say, then it could not be hoisted because it does not
  commute with \<^verbatim>\<open>opA\<close>; hence, as we descend into the term, we have to maintain the union of the
  footprints of terms we looked at.\<close>
  fun hoist_redundant_operations_core_with count
        ((e : locality_entry, f) :: inner) =
        if locality_entry_kind e = Locality_Attribute then
          let
            val (front, back) =
              lift_redundant_operations_core_with count
                [] [] (#footprint e) inner
          in
            (length front = 0, (e, f) :: (front @ back),
              List.map #1 front, List.map #1 back)
          end
        else (true, (e, f) :: inner, [], [])
    | hoist_redundant_operations_core_with _ x = (true, x, [], [])

  fun hoist_redundant_operations_with count (x,y) =
    let
      val (action, xp, f, b) =
        hoist_redundant_operations_core_with count x
    in
      (action, (xp, y), f, b)
    end

  fun hoist_redundant_operations decomp =
    hoist_redundant_operations_with locality_no_count decomp

  \<comment>\<open>Definition theorem(s) for a constant, if it has one; otherwise the empty list. We must
     return an \<^emph>\<open>unconditional\<close> definition equation, because the cancellation/locality proofs unfold
     it in a cleared simpset that cannot discharge side conditions. Two name resolutions can
     produce different forms. The fully-qualified name (\<^verbatim>\<open>Foo.bar_def\<close>) avoids grabbing a
     same-named constant from another theory — important when several records share a field/op base
     name (cf. the qualified-name cases in
     \<^verbatim>\<open>AutoLocality_Test_Boundaries\<close>). But inside a locale, the fully-qualified \<^emph>\<open>exported\<close> def carries
     the locale predicate as a premise (\<^verbatim>\<open>locale ?p \<Longrightarrow> Foo.bar ?p R \<equiv> \<dots>\<close>), unusable in a cleared
     simpset, whereas the \<^emph>\<open>local\<close> def under the base name is unconditional (\<^verbatim>\<open>bar R \<equiv> \<dots>\<close>) with the
     locale parameter free. So we gather candidates from both the qualified and the base name and
     prefer an unconditional one; this fixes locale-local constants while preserving the
     cross-theory disambiguation.\<close>
  fun locality_selected_definition ctxt (cname : string) =
    if is_const_with_def ctxt cname then
      let
        fun get nm =
          (try (Proof_Context.get_thms ctxt) nm |> the_default [])
          |> map (pair nm)
        fun unconditional t = null (Logic.strip_imp_prems (Thm.prop_of t))
        fun defines (_, thm) =
          Term.exists_subterm
            (fn Const (cname', _) => cname = cname' | _ => false)
            (Thm.prop_of thm)
        val candidates =
          get (Thm.def_name cname)
          @ get (Thm.def_name (Long_Name.base_name cname))
          |> filter defines
      in
        case List.filter (unconditional o #2) candidates of
           candidate :: _ => SOME candidate
         | [] =>
             (case candidates of
                candidate :: _ => SOME candidate
              | [] => NONE)
      end
    else NONE

  fun locality_def_thms_of ctxt cname =
    locality_selected_definition ctxt cname
    |> Option.map (single o #2)
    |> the_default []

  fun locality_def_fact_name ctxt cname =
    locality_selected_definition ctxt cname
    |> Option.map #1

  fun locality_standard_record_hierarchy_with count thy rec_name =
    let
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Record_Hierarchy_Scans
      val info = Record.the_info thy rec_name
      val parents =
        (case #parent info of
           NONE => []
         | SOME (_, parent_name) =>
             locality_standard_record_hierarchy_with count thy parent_name)
    in
      parents @ [info]
    end

  fun locality_standard_record_hierarchy thy rec_name =
    locality_standard_record_hierarchy_with locality_no_count thy rec_name

  fun locality_field_selector_names ctxt rec_name =
    get_fields_full rec_name ctxt
    |> map (Syntax.read_term ctxt #> extract_const)

  fun locality_field_name_lookup kind names field =
    case List.find (fn name => Long_Name.base_name name = field) names of
      SOME name => name
    | NONE => error ("Unknown record " ^ kind ^ " " ^ quote field)

  fun locality_field_selector_name ctxt rec_name field =
    locality_field_name_lookup "field"
      (locality_field_selector_names ctxt rec_name) field

  fun locality_field_update_name ctxt rec_name field =
    case List.find (fn name => dest_field_update name = SOME field)
           (get_field_updates_full rec_name ctxt) of
      SOME name => name
    | NONE => error ("Unknown record field update " ^ quote field)

  \<comment>\<open>The field selector/update algebra for datatype records or standard records.
     Datatype records expose a dedicated quadratic \<^verbatim>\<open>record_simps\<close> collection. Standard
     records keep per-level simps in `Record.info`; gather only the selected
     record's inheritance chain instead of importing the global record
     simpset.\<close>
  fun locality_record_simps_of_with count ctxt
        (rec_name : string) : thm list =
    let
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Record_Preparations
      val thy = Proof_Context.theory_of ctxt
      val simps =
        case Record.get_info thy rec_name of
          NONE =>
            Attrib.eval_thms ctxt
              [(rec_name ^ ".record_simps" |> Facts.named, [])]
        | SOME _ =>
            locality_standard_record_hierarchy_with count thy rec_name
            |> maps #simps
            |> distinct Thm.eq_thm_prop
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Record_Rules_Selected simps
    in
      simps
    end

  fun locality_record_simps_of ctxt rec_name =
    locality_record_simps_of_with
      (locality_direct_counter ctxt) ctxt rec_name

  fun locality_record_expand_thms ctxt rec_name =
    let val thy = Proof_Context.theory_of ctxt in
      case Record.get_info thy rec_name of
        SOME info => [#equality info]
      | NONE => Proof_Context.get_thms ctxt (rec_name ^ ".expand")
    end

  fun locality_record_expand_thm_name ctxt rec_name =
    if Option.isSome (Record.get_info (Proof_Context.theory_of ctxt) rec_name)
    then rec_name ^ ".equality"
    else rec_name ^ ".expand"

  \<comment>\<open>A minimal simpset carrying only the supplied lemmas on top of \<^verbatim>\<open>HOL_ss\<close>, with \<^verbatim>\<open>if\<close> splitting
     enabled. Building on \<^verbatim>\<open>HOL_ss\<close> rather than the full ambient simpset is the key performance lever:
     the record-update algebra goals are pure rewriting, so the classical reasoner and the hundreds
     of ambient simp rules are dead weight.

     Two ingredients beyond the bare lemmas are essential. (1) \<^verbatim>\<open>if_split\<close>: an operation whose body
     is a top-level conditional (e.g. \<^verbatim>\<open>if c then update_a \<dots> else update_b \<dots>\<close>) generates locality
     goals with that \<^verbatim>\<open>if\<close> on both sides; without splitting it, the field algebra cannot normalise
     through the branches and the goal survives. (2) \<^verbatim>\<open>HOL_ss\<close> rather than \<^verbatim>\<open>HOL_basic_ss\<close>: splitting
     the \<^verbatim>\<open>if\<close> in a commutativity/disjointness goal produces residual implications carrying the branch
     condition and its negation (e.g. \<^verbatim>\<open>c \<longrightarrow> \<not>c \<longrightarrow> \<dots>\<close>); discharging those needs the \<^verbatim>\<open>if\<close>-congruence and
     boolean simplification that \<^verbatim>\<open>HOL_ss\<close> provides but \<^verbatim>\<open>HOL_basic_ss\<close> (even with \<^verbatim>\<open>simp_thms\<close>) does
     not. \<^verbatim>\<open>HOL_ss\<close> is still vastly lighter than the old \<^verbatim>\<open>auto\<close>/ambient-simpset approach — measured at
     the same speed as \<^verbatim>\<open>HOL_basic_ss\<close> on the common (non-conditional) field-update goals.\<close>
  fun locality_make_simpset ctxt (simps : thm list) : Proof.context =
    let
      val count = locality_direct_counter ctxt
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Record_Simpset_Builds
    in
      Splitter.add_split @{thm if_split}
        (put_simpset HOL_ss ctxt addsimps simps)
    end

  \<comment>\<open>The (definition-unfolding + \<^verbatim>\<open>record_simps\<close>) lemma list for a record and a set of constants.
     This is the expensive lookup — \<^verbatim>\<open>record_simps\<close> is quadratic in the number of fields — so a
     caller proving many goals over the same record should compute it once and reuse it.

     \<^verbatim>\<open>Let_def\<close> is included because an operation whose body is a \<^verbatim>\<open>let \<dots> in \<dots>\<close> (e.g.
     \<^verbatim>\<open>w_apply_policy\<close>, whose body binds a local before the update
     telescope) unfolds to a \<^verbatim>\<open>let\<close> that blocks \<^verbatim>\<open>record_simps\<close> from reaching the underlying field
     updates; without \<^verbatim>\<open>Let_def\<close> the field algebra cannot normalise through it and the
     commutativity/disjointness/local-action goals survive. (The old \<^verbatim>\<open>auto\<close>-based discharge carried
     \<^verbatim>\<open>Let_def\<close> in its simp set for exactly this reason.)\<close>
  fun locality_record_lemmas ctxt (rec_name : string) (cnames : string list) : thm list =
    @{thms Let_def} @ maps (locality_def_thms_of ctxt) cnames @ locality_record_simps_of ctxt rec_name

  \<comment>\<open>The user-defined constants directly referenced in \<^verbatim>\<open>cname\<close>'s body (one level deep). These are
     the helper functions / operations an operation \<^emph>\<open>delegates\<close> to (e.g. \<^verbatim>\<open>w_split_set\<close> calls
     \<^verbatim>\<open>split_pair\<close>; \<^verbatim>\<open>w_nested\<close> calls another operation on an inner record). To discharge the
     locality goals the field algebra must see through these, so their definitions have to be
     unfolded alongside the operation's own.
     We restrict to constants in the record's own theory and skip \<^verbatim>\<open>case_*\<close> combinators (those are
     handled by split rules, and unfolding their internal definition would defeat the split).\<close>
  fun locality_body_helper_consts ctxt (rec_name : string) (cname : string) : string list =
    let
      val rec_thy = Long_Name.qualifier rec_name
      val record_field_consts =
        locality_field_selector_names ctxt rec_name
        @ get_field_updates_full rec_name ctxt
      fun same_theory c =
        Long_Name.qualifier c = rec_thy orelse Long_Name.qualifier (Long_Name.qualifier c) = rec_thy
      (* Constants belonging to the record's own datatype machinery — its selectors, field updates,
         constructor, case combinator — live under the '<rec_name>.' namespace. These must NOT be
         unfolded as "helpers": their definitions expand to a 'case <constructor>' on the record,
         which then gets case-split, manufacturing spurious subgoals (e.g. 'update_f g (make_rec \<dots>)
         = make_rec \<dots>'). The record algebra is handled entirely by 'record_simps', so we drop them. *)
      fun is_record_machinery c =
        Long_Name.qualifier c = rec_name
        orelse member (op =) record_field_consts c
      val consts = fold (fn d => Term.add_consts (Thm.prop_of d)) (locality_def_thms_of ctxt cname) []
                   |> map fst |> distinct (op =)
    in
      consts |> List.filter (fn c =>
        c <> cname andalso same_theory c andalso is_const_with_def ctxt c
        andalso not (is_record_machinery c)
        andalso not (String.isPrefix "case_" (Long_Name.base_name c)))
    end

  type locality_body_helper_plan = {
    unfold: string list,
    certificates: thm list
  }

  \<comment>\<open>Collect maximal applications of the one-level helper constants in a definition. Looking
     at the constant name alone is insufficient: a registration for \<^verbatim>\<open>helper A\<close> cannot justify
     suppressing the definition of an occurrence \<^verbatim>\<open>helper B x R\<close>. Descending through the
     arguments, rather than through the application spine, records only the complete occurrence and
     not each of its partial prefixes.\<close>
  fun locality_body_helper_applications ctxt cname helpers =
    let
      fun application_eq
            ((helper0, head0, args0), (helper1, head1, args1)) =
        helper0 = helper1 andalso
        Term.aconv
          (Term.list_comb (head0, args0),
           Term.list_comb (head1, args1))
      fun collect term applications =
        let
          val (head, args) = Term.strip_comb term
          val applications' =
            (case head of
               Const (helper, _) =>
                 if member (op =) helpers helper
                 then insert application_eq (helper, head, args) applications
                 else applications
             | _ => applications)
        in
          case term of
            Abs (_, _, body) => collect body applications'
          | _ => fold collect args applications'
        end
    in
      fold (collect o Thm.prop_of)
        (locality_def_thms_of ctxt cname) []
    end

  \<comment>\<open>Prefer a registered helper's linear certificates only when every actual occurrence in
     the definition is covered by a typed registration. The selected certificate objects are passed
     directly to the generated proof, so this also works when the helper was registered under a
     custom theorem attribute and is absent from the record's default locality-facts bundle.

     If any occurrence is uncovered, unfold the helper definition. This is deliberately
     all-or-nothing per helper constant: mixing a certificate for one specialization with raw
     unfolding for another makes the automatic proof harder to predict and buys no useful
     performance advantage.\<close>
  fun locality_body_helper_plan ctxt rec_name cname :
        locality_body_helper_plan =
    let
      val helpers = locality_body_helper_consts ctxt rec_name cname
      val applications =
        locality_body_helper_applications ctxt cname helpers
      fun matching_entries head args =
        [Locality_Operation, Locality_Attribute]
        |> map_filter (fn kind =>
             select_locality_entry_kind_with locality_no_count
               ctxt rec_name kind head args
             |> Option.map #2)
      fun entry_certificates (entry : locality_entry) =
        #core_thms entry @ #disjoint_thms entry
      fun analyse helper =
        let
          val helper_applications =
            applications
            |> List.filter (fn (helper', _, _) => helper = helper')
          val entries =
            helper_applications
            |> map (fn (_, head, args) =>
                 matching_entries head args)
        in
          if not (null helper_applications)
              andalso List.all (not o null) entries
          then
            (NONE,
             flat entries
             |> maps entry_certificates)
          else
            (SOME helper, [])
        end
      val analyses = map analyse helpers
    in
      { unfold = map_filter fst analyses,
        certificates =
          maps snd analyses
          |> map (Thm.transfer' ctxt)
          |> distinct Thm.eq_thm_prop }
    end

  val locality_body_helper_certificate_fact =
    "autolocality_body_helper_certificates"

  \<comment>\<open>Method strings are parsed against a private copy of the declaration context containing
     the selected helper certificates as one internal fact. The fact is captured in the method
     closure and never installed in the surrounding local theory or its ambient simpset.\<close>
  fun locality_body_helper_method_context ctxt certificates =
    if null certificates then ctxt
    else
      Proof_Context.put_thms false
        (locality_body_helper_certificate_fact,
         SOME certificates) ctxt

  \<comment>\<open>Datatype case-split rules (\<^verbatim>\<open>T.split\<close>) for every \<^verbatim>\<open>case_T\<close> combinator appearing in the bodies of
     the given constants. An operation whose body is a \<^verbatim>\<open>case x of \<dots>\<close> (e.g.
     \<^verbatim>\<open>maybe_steal_secret_metadata_page_pure\<close>, on a \<^verbatim>\<open>page_theft\<close>) needs \<^verbatim>\<open>page_theft.split\<close> to push
     the surrounding field projection / update through the branches. \<^verbatim>\<open>if\<close> and \<^verbatim>\<open>prod\<close> are always
     included since \<^verbatim>\<open>if\<close>-bodies and tuple-\<^verbatim>\<open>let\<close>s are common and their split rules are cheap.\<close>
  fun locality_body_case_splits ctxt (cnames : string list) : thm list =
    let
      fun split_name_of c =
        let val b = Long_Name.base_name c in
          if String.isPrefix "case_" b then SOME (Long_Name.qualifier c ^ ".split") else NONE
        end
      val consts = fold (fn cn => fold (fn d => Term.add_consts (Thm.prop_of d))
                                       (locality_def_thms_of ctxt cn)) cnames []
                   |> map fst |> distinct (op =)
      val names = map_filter split_name_of consts
    in
      @{thms if_split prod.split}
      @ maps (fn n => (Proof_Context.get_thms ctxt n) handle ERROR _ => []) names
    end

  \<comment>\<open>A minimal simpset (as \<^verbatim>\<open>locality_make_simpset\<close>) extended with the case-split rules relevant to the
     bodies of \<^verbatim>\<open>cnames\<close>. Used by the declaration-time discharge so that conditional / tuple-let /
     datatype-case operation bodies normalise.\<close>
  fun locality_make_split_simpset ctxt (simps : thm list) (cnames : string list) : Proof.context =
    locality_make_simpset ctxt simps |> fold Splitter.add_split (locality_body_case_splits ctxt cnames)

  \<comment>\<open>Names of the same case-split rules, for use in method strings (\<^verbatim>\<open>auto split: \<dots>\<close>). Mirrors
     \<^verbatim>\<open>locality_body_case_splits\<close> but returns fact names rather than theorems.\<close>
  fun locality_body_case_split_names ctxt (cnames : string list) : string list =
    let
      fun split_name_of c =
        let val b = Long_Name.base_name c in
          if String.isPrefix "case_" b then SOME (Long_Name.qualifier c ^ ".split") else NONE
        end
      val consts = fold (fn cn => fold (fn d => Term.add_consts (Thm.prop_of d))
                                       (locality_def_thms_of ctxt cn)) cnames []
                   |> map fst |> distinct (op =)
      val names = map_filter split_name_of consts
    in
      ["if_split", "prod.split"]
      @ List.filter (fn n => can (Proof_Context.get_thms ctxt) n) names
    end

  \<comment>\<open>The record's accumulating \<^verbatim>\<open><rec>_locality_facts\<close> bundle, if it exists. This carries the
     already-derived locality lemmas of \<^emph>\<open>previously registered\<close> operations, which is exactly what
     lets an operation that \<^emph>\<open>delegates\<close> to another (e.g. one whose body calls a previously
     registered operation) be discharged: the callee's facts normalise the inner call. Empty if the
     bundle has not been created yet.\<close>
  fun locality_facts_bundle ctxt (rec_name : string) : thm list =
    (Named_Theorems.get ctxt (Named_Theorems.check ctxt (default_named_theorems_for_record rec_name, Position.none)))
    handle ERROR _ => []

  \<comment>\<open>General-purpose discharge for a locality goal, used as the fallback when the fast minimal \<^verbatim>\<open>simp\<close>
     leaves a residue. This mirrors the old (pre-rewrite) discharge — full \<^verbatim>\<open>auto\<close> with case
     splitting (for \<^verbatim>\<open>if\<close> / \<^verbatim>\<open>case\<close> / tuple-\<^verbatim>\<open>let\<close> bodies), the operation/record lemmas, and the
     record's locality-facts bundle (for delegation to other operations) — but is invoked only on the
     goals the cheap path could not close, so it is no longer on the hot path of wide-record
     initialisation (which proves no per-field-update lemmas at all). \<^verbatim>\<open>intro_thms\<close> are added as
     introduction rules (e.g. \<^verbatim>\<open>rec.expand\<close> for the local-action goal).\<close>
  fun locality_auto_tac ctxt (rec_name : string) (cnames : string list) (intro_thms : thm list) : tactic =
    let
      val count = locality_direct_counter ctxt
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Record_Simpset_Builds
      val ctxt' =
        ctxt addsimps
          (locality_record_lemmas ctxt rec_name cnames
            @ locality_facts_bundle ctxt rec_name)
        |> fold Splitter.add_split (locality_body_case_splits ctxt cnames)
    in auto_tac (ctxt' addSIs intro_thms) end

  \<comment>\<open>Tactic discharging a record equality by unfolding the given constant definitions and the
     record's \<^verbatim>\<open>record_simps\<close>. This is the workhorse for the on-the-fly cancellation simproc — it
     reduces "unfold the operations, normalise the field algebra". It deliberately uses a \<^emph>\<open>cleared\<close>
     simpset (no ambient rules, no congruences, no other simprocs): the simproc calls this from
     inside a running \<^verbatim>\<open>simp\<close>, so anything in the ambient set could loop or re-enter the locality
     simprocs. Do not switch this to \<^verbatim>\<open>HOL_basic_ss\<close>/the ambient simpset — see the declaration-time
     tactics below for the faster \<^verbatim>\<open>HOL_basic_ss\<close> variants used outside the simproc.\<close>
  fun locality_simp_defs_tac ctxt (rec_name : string) (cnames : string list) : tactic =
    let
      val count = locality_direct_counter ctxt
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Record_Simpset_Builds
    in
      simp_tac
        (clear_simpset ctxt addsimps
          (locality_record_lemmas ctxt rec_name cnames)) 1
    end

  \<comment>\<open>Tactic for the 'local action' lemma \<^verbatim>\<open>op ... R = update_<fp> (\<lambda>_. field (op ... R)) R\<close>.
     This is a record equality that is in general only provable by record extensionality
     (\<^verbatim>\<open>rec.expand\<close>): an operation may set a field with a function of the \<^emph>\<open>old\<close> value (e.g.
     \<^verbatim>\<open>update_f (\<lambda>old. g old)\<close>), and the two sides agree only because that old value is itself the
     current field. So we reduce to field equalities by \<^verbatim>\<open>rec.expand\<close>, then normalise each with the
     field algebra. Covers both bare field updates and genuine operations.

     Performance: the old implementation used \<^verbatim>\<open>auto_tac\<close> with \<^verbatim>\<open>rec.expand\<close> as an introduction rule
     over the full ambient simpset, which is ~9x slower per goal than resolving \<^verbatim>\<open>expand\<close> explicitly
     and finishing with a minimal \<^verbatim>\<open>simp\<close>. We try a \<^verbatim>\<open>simp\<close>-only attempt first (for the common case
     where both sides are already syntactically equal record updates and \<^verbatim>\<open>expand\<close> is unnecessary),
     then fall back to resolving \<^verbatim>\<open>expand\<close> and discharging the resulting field equalities.

     The simp-only attempt is wrapped in \<^verbatim>\<open>SOLVED'\<close>: an operation that writes a field with a function
     of the \<^emph>\<open>old\<close> value (e.g. \<^verbatim>\<open>update_qc (\<lambda>old. old + qc R)\<close>) does \<^emph>\<open>not\<close> close by rewriting alone —
     \<^verbatim>\<open>simp\<close> partially normalises but leaves the two update-functions provably-but-not-syntactically
     equal. Without \<^verbatim>\<open>SOLVED'\<close> that partial success would short-circuit the \<^verbatim>\<open>ORELSE\<close> and the residual
     goal would escape, so \<^verbatim>\<open>Goal.prove\<close> would fail and the footprint entry would never be registered.\<close>
  fun locality_local_action_tac ctxt (rec_name : string) (cnames : string list) : tactic =
    let
      val ss = locality_make_split_simpset ctxt (locality_record_lemmas ctxt rec_name cnames) cnames
      val expand = locality_record_expand_thms ctxt rec_name
    in
      SOLVED' (asm_full_simp_tac ss) 1
      ORELSE SOLVED' (resolve_tac ctxt expand THEN_ALL_NEW asm_full_simp_tac ss) 1
      \<comment>\<open>Build the (expensive) \<^verbatim>\<open>auto\<close> simpset lazily — only if the two cheap \<^verbatim>\<open>simp\<close> attempts above
         both fail — so the common case never pays for it.\<close>
      ORELSE (fn st => locality_auto_tac ctxt rec_name cnames expand st)
    end

  fun locality_transfer_thms ctxt =
    map (Thm.transfer' ctxt)

  fun locality_entry_certificates ctxt (entry : locality_entry) =
    locality_transfer_thms ctxt (#core_thms entry @ #disjoint_thms entry)

  fun locality_certificate_thms ctxt (entries : locality_entry list) =
    entries
    |> maps (locality_entry_certificates ctxt)
    |> distinct Thm.eq_thm_prop

  fun locality_local_rewrites ctxt (entries : locality_entry list) =
    entries
    |> map_filter #local_thm
    |> locality_transfer_thms ctxt
    |> distinct Thm.eq_thm_prop
    |> map (fn thm => thm RS @{thm eq_reflection})

  fun locality_meta_rewrites ctxt thms =
    thms
    |> locality_transfer_thms ctxt
    |> map (fn thm => thm RS @{thm eq_reflection})

  fun locality_rewrs_conv [] = Conv.all_conv
    | locality_rewrs_conv thms = Conv.rewrs_conv thms

  fun locality_bottom_rewrs_conv [] _ = Conv.all_conv
    | locality_bottom_rewrs_conv thms ctxt = Conv.bottom_rewrs_conv thms ctxt

  fun locality_field_core_rewrites record_simps (entry : locality_entry) =
    if locality_entry_kind entry <> Locality_Operation
       orelse not (#field entry) then []
    else
      record_simps |> map_filter (fn thm =>
        capture_noninterrupt (fn () =>
          let
            val rewrite = thm RS @{thm eq_reflection}
            val lhs_head = rewrite |> Thm.lhs_of |> Thm.term_of |> extract_const
            val rhs_head = rewrite |> Thm.rhs_of |> Thm.term_of |> extract_const
            val entry_name = #const_name entry
            val _ =
              if Option.isSome (dest_field_update lhs_head)
                 andalso Option.isSome (dest_field_update rhs_head)
                 andalso lhs_head <> rhs_head
              then ()
              else raise Match
          in
            if lhs_head = entry_name then rewrite
            else if rhs_head = entry_name then rewrite RS @{thm Pure.symmetric}
            else raise Match
          end))

  fun locality_core_rewrites ctxt record_simps entries =
    let
      val declared =
        entries |> maps #core_thms |> distinct Thm.eq_thm_prop
        |> locality_meta_rewrites ctxt
      val fields =
        entries |> maps (locality_field_core_rewrites record_simps)
    in
      Library.merge Thm.eq_thm_prop (declared, fields)
    end

  fun locality_core_update_field thm =
    capture_noninterrupt (fn () =>
      thm |> Thm.rhs_of |> Thm.term_of |> extract_const |> dest_field_update |> the)

  fun locality_filter_core_rewrites fields =
    List.filter (fn thm =>
      case locality_core_update_field thm of
        SOME field => member (op =) fields field
      | NONE => false)

  fun locality_operation_applier (entry : locality_entry) prefix =
    let
      val operation = #pattern entry
      val args = locality_entry_args entry
      val idx = locality_entry_idx entry
      val argtys = Term.binder_types (Term.type_of operation) |> take args
      val frees = map_index (fn (i, ty) => Free (prefix ^ Int.toString i, ty)) argtys
    in
      (nth argtys idx,
       fn rec_arg => Term.list_comb (operation,
         map_index (fn (i, fr) => if i = idx then rec_arg else fr) frees))
    end

  fun locality_entry_pattern_at_record_type ctxt
        (entry : locality_entry) record_type =
    let
      val fresh_inc = Term.maxidx_of_typ record_type + 1
      val pattern =
        #pattern entry
        |> locality_varify_types_preserving
             (locality_assumption_tfrees ctxt)
        |> Term.map_types (Logic.incr_tvar fresh_inc)
      val arg_types =
        Term.binder_types (Term.type_of pattern)
        |> take (locality_entry_args entry)
      val source_record_type =
        nth arg_types (locality_entry_idx entry)
      val type_env =
        Sign.typ_match (Proof_Context.theory_of ctxt)
          (source_record_type, record_type) Vartab.empty
        handle Type.TYPE_MATCH =>
          error ("Cannot specialize AutoLocality pattern "
            ^ Syntax.string_of_term ctxt (#pattern entry)
            ^ " at record type "
            ^ Syntax.string_of_typ ctxt record_type)
      val pattern' = Envir.subst_term_types type_env pattern
      val arg_types' =
        Term.binder_types (Term.type_of pattern')
        |> take (locality_entry_args entry)
    in
      (pattern', arg_types')
    end

  \<comment>\<open>Derive one generic attribute/operation cancellation theorem from the two entries'
     linear certificates. Apply an operation's self-referential `_local` theorem only once,
     immediately cancel the resulting footprint updates, and generalize the result. Expanding a
     complete telescope before cancellation duplicates its inner record term once per footprint
     field and is therefore exponential even though the final equality is small.\<close>
  fun locality_prove_cancellation_entries_with count ctxt rec_name
        (attribute : locality_entry) (operation : locality_entry) =
    (case Exn.capture (fn () =>
       let
         val (operation_record_type, apply_operation) =
           locality_operation_applier operation "operation_"
         val record = Free ("R", operation_record_type)
         val operation_result = apply_operation record
         val (attribute_out, attribute_out_arg_types) =
           locality_entry_pattern_at_record_type ctxt attribute
             (Term.type_of operation_result)
         val (attribute_in, attribute_in_arg_types) =
           locality_entry_pattern_at_record_type ctxt attribute
             operation_record_type
         val attribute_idx = locality_entry_idx attribute
         val _ =
           (attribute_out_arg_types ~~ attribute_in_arg_types)
           |> map_index (fn (i, (out_type, in_type)) =>
                if i = attribute_idx orelse out_type = in_type then ()
                else error "Attribute non-record argument types do not agree")
         val attribute_args =
           map_index (fn (i, typ) =>
             Free ("attribute_" ^ Int.toString i, typ))
             attribute_out_arg_types
         fun apply_attribute pattern rec_arg =
           Term.list_comb (pattern,
             map_index (fn (i, arg) =>
               if i = attribute_idx then rec_arg else arg)
               attribute_args)
         val lhs = apply_attribute attribute_out operation_result
         val expected_rhs = apply_attribute attribute_in record
         val (attribute_head, lhs_args) = Term.strip_comb lhs
         val attribute_absolute_idx =
           locality_entry_absolute_idx attribute
         val attribute_gap =
           (attribute,
            (attribute_head,
             List.take (lhs_args, attribute_absolute_idx),
             List.drop (lhs_args, attribute_absolute_idx + 1)))
         val operation_expansion =
           if #field attribute then []
           else locality_local_rewrites ctxt [operation]
         val _ =
           if #field attribute orelse #field operation
              orelse not (null operation_expansion)
           then ()
           else error "Operation has no local-action certificate"
         val cancellation_thms =
           if #field attribute
           then Library.merge Thm.eq_thm_prop
             (#disjoint_thms operation,
              locality_record_simps_of_with count ctxt rec_name)
           else #core_thms attribute
         val cancellation_rewrites =
           locality_meta_rewrites ctxt cancellation_thms
         val _ =
           if null cancellation_rewrites
           then error "No attribute/operation cancellation certificates"
           else ()
         fun descend_attribute child_conv =
           let
             val (_, (_, pre, post)) = attribute_gap
             val _ = locality_count_one count
               AutoLocality_Instrumentation.Planner_Recursive_Node_Builds
             val _ = locality_count_one count
               AutoLocality_Instrumentation.Planner_Context_Lifts
             val _ = locality_count_int count
               AutoLocality_Instrumentation.Planner_Application_Frames
               (fn () => length pre + 1 + length post)
             val _ = locality_count_one count
               AutoLocality_Instrumentation.Planner_Tail_Copies
           in
             fun_conv_many Conv.all_conv
               (map (K Conv.all_conv) pre @ [child_conv]
                 @ map (K Conv.all_conv) post)
           end
         val expand_operation =
           if null operation_expansion then Conv.all_conv
           else descend_attribute
             (locality_rewrs_conv operation_expansion)
         val cancel_operation =
           Conv.repeat_conv
             (locality_rewrs_conv cancellation_rewrites)
         val _ = locality_count_one count
           AutoLocality_Instrumentation.Proof_Cterms
         val result =
           (expand_operation then_conv cancel_operation)
             (Thm.cterm_of ctxt lhs)
         val actual_rhs = result |> Thm.rhs_of |> Thm.term_of
         val _ =
           if Term.aconv_untyped (actual_rhs, expected_rhs) then ()
           else error "Attribute/operation cancellation produced the wrong result"
       in
         result
         |> Thm.forall_intr_frees
         |> Thm.forall_elim_vars 0
       end) () of
       Exn.Res thm =>
         (locality_count_one count
            AutoLocality_Instrumentation.Proof_Results;
          SOME thm)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           (locality_pretty_trace ctxt 1 (fn () =>
              Pretty.text "AutoLocality pair cancellation declined:"
              @ [Pretty.brk 1, Pretty.str (Runtime.exn_message exn)]
              |> Pretty.block);
            NONE))

  \<comment>\<open>Derive one operation/operation commutativity theorem from the two entries' linear
     certificates. This is deliberately proved in the invocation context and never registered:
     cancellation asks only for the back/front swaps required by the current telescope.\<close>
  fun locality_prove_commutativity_entries_with count ctxt rec_name
        (entryA : locality_entry) (entryB : locality_entry) : thm option =
    (case capture_noninterrupt (fn () =>
       let
         val (rty, appA) = locality_operation_applier entryA "a_"
         val (_, appB) = locality_operation_applier entryB "b_"
         val R = Free ("R", rty)
         val goal =
           HOLogic.mk_Trueprop (HOLogic.mk_eq (appA (appB R), appB (appA R)))
       in
         Goal.prove ctxt [] [] goal
           (fn {context, ...} =>
             let
               val simps = locality_certificate_thms context [entryA, entryB]
                 @ locality_record_simps_of_with count context rec_name
               val local_rewrites =
                 locality_local_rewrites context [entryA, entryB]
               val _ = locality_count_one count
                 AutoLocality_Instrumentation.Record_Simpset_Builds
             in
               (if null local_rewrites then all_tac
                else CONVERSION
                  (Conv.bottom_rewrs_conv local_rewrites context) 1)
               THEN simp_tac (clear_simpset context addsimps simps) 1
             end)
       end) of
       NONE => NONE
     | SOME thm =>
         (locality_count_one count
            AutoLocality_Instrumentation.Proof_Results;
          SOME thm))

  fun locality_prove_commutativity_entries ctxt rec_name entryA entryB =
    locality_prove_commutativity_entries_with
      (locality_direct_counter ctxt) ctxt rec_name entryA entryB

  \<comment>\<open>Fast path for a requested hoist: expand the cancellable front operations with their
     `_local` certificates and normalize both the original and hoisted telescopes with only the
     relevant `_core` field commutations and record algebra. This avoids deriving an explicit
     operation/operation theorem for the common single-field shape. Multi-field and deeper shapes
     that do not converge to the same normal form fall through to direct on-demand swaps.\<close>
  fun locality_prove_hoisting_by_normalization_with count ctxt rec_name ctm
        ctm_decomposed ctm_decomposed_hoisted
        (front_entries : locality_entry list) (back_entries : locality_entry list) =
    capture_noninterrupt (fn () =>
      let
        val record_simps =
          locality_record_simps_of_with count ctxt rec_name
        val front_locality = locality_local_rewrites ctxt front_entries
        val back_locality = locality_local_rewrites ctxt back_entries
        val front_footprint = front_entries |> maps #footprint |> distinct (op =)
        val back_footprint = back_entries |> maps #footprint |> distinct (op =)
        val front_commutativity =
          locality_core_rewrites ctxt record_simps front_entries
          |> locality_filter_core_rewrites back_footprint
        val back_commutativity =
          locality_core_rewrites ctxt record_simps back_entries
          |> locality_filter_core_rewrites front_footprint
        val ctxt_clear = clear_simpset ctxt
        val _ = locality_count_int count
          AutoLocality_Instrumentation.Record_Simpset_Builds (fn () => 3)
        val ctxt_record_simps = ctxt_clear addsimps record_simps
        val ctxt_front_commutativity = ctxt_clear addsimps front_commutativity
        val ctxt_back_commutativity = ctxt_clear addsimps back_commutativity
        val inner_conv =
          locality_bottom_rewrs_conv back_locality ctxt
          then_conv Simplifier.rewrite ctxt_front_commutativity
          then_conv Simplifier.rewrite ctxt_record_simps
        fun telescope_conv decomp =
          op_term_with_gap_conv_with count decomp
            (locality_rewrs_conv front_locality)
            (Conv.combination_conv (Conv.arg_conv inner_conv))
        val _ = locality_count_one count
          AutoLocality_Instrumentation.Proof_Cterms
        val ctm_hoisted =
          ctm_decomposed_hoisted
          |> recombine_decomposed_comb_with count
          |> Thm.cterm_of ctxt
        val original_reduce =
          (telescope_conv ctm_decomposed
           then_conv Simplifier.rewrite ctxt_back_commutativity) ctm
        val hoisted_reduce =
          telescope_conv ctm_decomposed_hoisted ctm_hoisted
        val _ = locality_count_int count
          AutoLocality_Instrumentation.Proof_Compositions (fn () => 2)
        val result =
          (hoisted_reduce RS @{thm Pure.symmetric})
          RS (original_reduce RS @{thm Pure.transitive})
        val _ =
          if Term.aconv (result |> Thm.rhs_of |> Thm.term_of, Thm.term_of ctm_hoisted)
          then ()
          else error "Autolocality normalization produced the wrong hoisted telescope"
        val _ = locality_count_one count
          AutoLocality_Instrumentation.Proof_Results
      in result end)

  fun locality_prove_hoisting_by_normalization ctxt rec_name ctm
        ctm_decomposed ctm_decomposed_hoisted front_entries back_entries =
    locality_prove_hoisting_by_normalization_with
      (locality_direct_counter ctxt) ctxt rec_name ctm
      ctm_decomposed ctm_decomposed_hoisted front_entries back_entries

  \<comment>\<open>Rewrite an operation telescope to its stable footprint partition by applying only the
     adjacent operation/operation swaps selected by the planner.  Every operation occurrence is
     tagged with its original position, so identical operations remain distinguishable and both
     front and back partitions retain source order.

     A swap is applied at its exact telescope position.  The conversion follows the unique record
     argument path through the attribute and the already-fixed outer operations, rewrites the
     adjacent pair once, and returns.  It never asks the simplifier to normalize a complete
     telescope and never scans the whole term for a matching pair.  Generic commutativity theorems
     are memoized by their exact typed operation patterns for the duration of this callback.\<close>
  fun locality_prove_hoisting_by_exact_swaps_with count ctxt rec_name ctm
        ctm_decomposed ctm_decomposed_hoisted =
    capture_noninterrupt (fn () =>
      let
        val (entries, body) = ctm_decomposed
        val (hoisted_entries, hoisted_body) = ctm_decomposed_hoisted
        val (attribute_gap, operation_gaps) =
          (case entries of
             attribute_gap :: operation_gaps =>
               (attribute_gap, operation_gaps)
           | [] => error "Missing attribute in autolocality telescope")
        val attribute = fst attribute_gap
        val indexed_operations =
          operation_gaps
          |> map_index (fn (index, gap) => (index, gap))

        fun stable_partition _ [] front_rev back_rev =
              (rev front_rev, rev back_rev)
          | stable_partition blocked
              ((occurrence as (_, (entry : locality_entry, _))) :: rest)
              front_rev back_rev =
              if disjoint_footprint blocked (#footprint entry)
              then
                stable_partition blocked rest
                  (occurrence :: front_rev) back_rev
              else
                stable_partition
                  (merge_footprints blocked (#footprint entry))
                  rest front_rev (occurrence :: back_rev)
        val (front, back) =
          stable_partition (#footprint attribute)
            indexed_operations [] []
        val target = front @ back
        val target_term =
          recombine_decomposed_comb
            (attribute_gap :: map #2 target, body)
        val expected_hoisted =
          recombine_decomposed_comb ctm_decomposed_hoisted
        val _ =
          if Term.aconv (body, hoisted_body)
             andalso Term.aconv (target_term, expected_hoisted)
             andalso length entries = length hoisted_entries
          then ()
          else error "Exact AutoLocality swap plan disagrees with hoisting"

        fun same_specialized_entry
              (entry0 : locality_entry, entry1 : locality_entry) =
          locality_entry_slot_eq (entry0, entry1)
          andalso Term.aconv (#pattern entry0, #pattern entry1)
        fun lookup_swap _ _ [] = NONE
          | lookup_swap back_entry front_entry
              (((back0, front0), rewrite) :: rest) =
              if same_specialized_entry (back_entry, back0)
                 andalso same_specialized_entry (front_entry, front0)
              then SOME rewrite
              else lookup_swap back_entry front_entry rest
        fun derive_swap back_entry front_entry memo =
          (case lookup_swap back_entry front_entry memo of
             SOME rewrite => (rewrite, memo)
           | NONE =>
               let
                 val theorem =
                   (case locality_prove_commutativity_entries_with count
                           ctxt rec_name back_entry front_entry of
                      SOME result => result
                    | NONE =>
                        error
                          "Failed to derive exact AutoLocality adjacent swap")
                 val _ = locality_count_one count
                   AutoLocality_Instrumentation.Planner_Swaps
                 val _ = locality_count_one count
                   AutoLocality_Instrumentation.Proof_Compositions
                 val rewrite =
                   theorem
                   |> Thm.forall_intr_frees
                   |> Thm.forall_elim_vars 0
                   |> (fn generalized =>
                        generalized RS @{thm eq_reflection})
               in
                 (rewrite,
                  ((back_entry, front_entry), rewrite) :: memo)
               end)

        fun lift_to_exact_position [] rewrite = Conv.rewr_conv rewrite
          | lift_to_exact_position
              ((_, (_, pre, post)) :: outer) rewrite =
              let
                val _ = locality_count_one count
                  AutoLocality_Instrumentation.Planner_Recursive_Node_Builds
                val _ = locality_count_one count
                  AutoLocality_Instrumentation.Planner_Context_Lifts
                val _ = locality_count_int count
                  AutoLocality_Instrumentation.Planner_Application_Frames
                  (fn () => length pre + 1 + length post)
                val _ = locality_count_one count
                  AutoLocality_Instrumentation.Planner_Tail_Copies
                val child =
                  lift_to_exact_position outer rewrite
              in
                fun_conv_many Conv.all_conv
                  (map (K Conv.all_conv) pre
                    @ [child]
                    @ map (K Conv.all_conv) post)
              end

        fun swap_adjacent index current current_ctm accumulated memo =
          let
            val (left_occurrence, right_occurrence) =
              (nth current index, nth current (index + 1))
            val (_, (back_entry, _)) = left_occurrence
            val (_, (front_entry, _)) = right_occurrence
            val _ =
              if disjoint_entries back_entry front_entry then ()
              else error "AutoLocality planned a non-commuting adjacent swap"
            val (rewrite, memo') =
              derive_swap back_entry front_entry memo
            val outer =
              attribute_gap
                :: map #2 (List.take (current, index))
            val step =
              lift_to_exact_position outer rewrite current_ctm
            val (prefix, suffix) = chop index current
            val current' =
              (case suffix of
                 left :: right :: rest =>
                   prefix @ right :: left :: rest
               | _ => error "Malformed AutoLocality adjacent swap")
            val expected =
              recombine_decomposed_comb
                (attribute_gap :: map #2 current', body)
            val _ =
              if Term.aconv
                   (step |> Thm.rhs_of |> Thm.term_of, expected)
              then ()
              else error "Exact AutoLocality swap rewrote the wrong position"
            val _ = locality_count_one count
              AutoLocality_Instrumentation.Planner_Swap_Applications
            val _ = locality_count_one count
              AutoLocality_Instrumentation.Proof_Compositions
            val accumulated' = Thm.transitive accumulated step
          in
            (current', Thm.rhs_of step, accumulated', memo')
          end

        fun bubble target_index current_index state =
          if current_index = target_index then state
          else
            let
              val (current, current_ctm, accumulated, memo) = state
              val state' =
                swap_adjacent (current_index - 1)
                  current current_ctm accumulated memo
            in
              bubble target_index (current_index - 1) state'
            end
        fun arrange target_index state =
          if target_index = length target then state
          else
            let
              val wanted = fst (nth target target_index)
              val (current, _, _, _) = state
              val current_index =
                find_index (fn (occurrence, _) =>
                  occurrence = wanted) current
              val _ =
                if current_index >= target_index then ()
                else error "AutoLocality lost a planned operation occurrence"
              val state' = bubble target_index current_index state
            in
              arrange (target_index + 1) state'
            end

        val initial =
          (indexed_operations, ctm, Conv.all_conv ctm, [])
        val (actual, actual_ctm, result, _) = arrange 0 initial
        val _ =
          if map fst actual = map fst target
             andalso
               Term.aconv
                 (Thm.term_of actual_ctm, expected_hoisted)
          then ()
          else error "Exact AutoLocality swaps did not reach the target"
      in
        result
      end)

  \<comment>\<open>Prove exactly one requested telescope cancellation by conversion. Derive only the
     operation/operation swaps needed to move the cancellable front operations across the blocked
     back operations, rewrite the original telescope to the already-computed hoisted telescope,
     derive one attribute/operation cancellation rule per distinct operational key and actual typed
     operation pattern, and schedule those invocation-local rules in front-operation order. Apply
     each scheduled rule once at the registered attribute root, lifting it only across any
     unregistered trailing application arguments. No user definition is unfolded and no pairwise
     theorem is registered or cached.\<close>
  fun locality_prove_cancellation_with count ctxt rec_name ctm
        ctm_decomposed ctm_decomposed_hoisted
        (front_entries : locality_entry list) (expected_rhs : term) =
    (case Exn.capture (fn () =>
      let
        val _ = locality_count_one count
          AutoLocality_Instrumentation.Planner_Requests
        val _ = locality_count_list count
          AutoLocality_Instrumentation.Planner_Cancellations front_entries
        val attr_entry =
          case fst ctm_decomposed of
            (entry, _) :: _ => entry
          | [] => error "Missing attribute in autolocality telescope"

        val _ = locality_count_one count
          AutoLocality_Instrumentation.Proof_Cterms
        val ctm_hoisted =
          ctm_decomposed_hoisted
          |> recombine_decomposed_comb_with count
          |> Thm.cterm_of ctxt
        val original_to_hoisted =
          if Term.aconv (Thm.term_of ctm, Thm.term_of ctm_hoisted)
          then Conv.all_conv ctm
          else
            case locality_prove_hoisting_by_exact_swaps_with count
                   ctxt rec_name ctm
                   ctm_decomposed ctm_decomposed_hoisted of
              SOME thm => thm
            | NONE => raise Match
        val actual_hoisted = original_to_hoisted |> Thm.rhs_of |> Thm.term_of
        val _ =
          if Term.aconv (actual_hoisted, Thm.term_of ctm_hoisted) then ()
          else error "Autolocality swaps did not produce the expected hoisted telescope"

        fun typed_cancellation_pattern (operation : locality_entry) =
          #pattern operation |> Envir.beta_eta_contract
        fun lookup_cancellation memo (operation : locality_entry) =
          (case LocalityOperationalKeyTable.lookup memo (#key operation) of
             NONE => NONE
           | SOME typed_rewrites =>
               Termtab.lookup typed_rewrites
                 (typed_cancellation_pattern operation))
        fun insert_cancellation (operation : locality_entry) rewrite =
          LocalityOperationalKeyTable.map_default
            (#key operation, Termtab.empty)
            (Termtab.update_new
              (typed_cancellation_pattern operation, rewrite))
        fun make_schedule [] _ schedule_rev = rev schedule_rev
          | make_schedule (operation :: operations) memo schedule_rev =
              let
                val (rewrite, memo') =
                  (case lookup_cancellation memo operation of
                     SOME rewrite => (rewrite, memo)
                   | NONE =>
                       let
                         val rewrite =
                           case locality_prove_cancellation_entries_with count
                                  ctxt rec_name attr_entry operation of
                             SOME thm => thm
                           | NONE => raise Match
                       in
                         (rewrite,
                          insert_cancellation operation rewrite memo)
                       end)
              in
                make_schedule operations memo' (rewrite :: schedule_rev)
              end
        val cancellation_schedule =
          make_schedule front_entries
            LocalityOperationalKeyTable.empty []
        val attribute_registered_arity =
          locality_entry_prefix_length attr_entry
            + locality_entry_args attr_entry
        fun apply_root_rewrite rewrite current =
          let
            val actual_arity =
              current
              |> Thm.term_of
              |> Term.strip_comb
              |> snd
              |> length
            val suffix_arity =
              actual_arity - attribute_registered_arity
            val _ =
              if suffix_arity >= 0 then ()
              else
                error
                  "AutoLocality cancellation lost the registered attribute root"
            val _ = locality_count_int count
              AutoLocality_Instrumentation.Planner_Application_Frames
              (fn () => suffix_arity)
          in
            fun_conv_many (Conv.rewr_conv rewrite)
              (replicate suffix_arity Conv.all_conv) current
          end
        fun apply_schedule [] _ accumulated = accumulated
          | apply_schedule (rewrite :: rewrites) current accumulated =
              let
                val step = apply_root_rewrite rewrite current
              in
                apply_schedule rewrites (Thm.rhs_of step)
                  (Thm.transitive accumulated step)
              end
        val hoisted_to_cancelled =
          apply_schedule cancellation_schedule ctm_hoisted
            (Conv.all_conv ctm_hoisted)
        val _ = locality_count_list count
          AutoLocality_Instrumentation.Planner_Root_Rewrites
          cancellation_schedule
        val _ = locality_count_one count
          AutoLocality_Instrumentation.Proof_Compositions
        val result =
          hoisted_to_cancelled
          RS (original_to_hoisted RS @{thm Pure.transitive})
        val actual_rhs = result |> Thm.rhs_of |> Thm.term_of
        val _ =
          (* Dropping a polymorphic datatype-record update can change only
             phantom type instantiations on the surrounding attribute. The
             recombined expected telescope records the intended constant/free
             shape but may retain the pre-cancellation instantiation; the
             conversion result itself is the kernel-checked, well-typed RHS. *)
          if Term.aconv_untyped (actual_rhs, expected_rhs) then ()
          else error "Autolocality conversion produced an unexpected right-hand side"
        val _ = locality_count_one count
          AutoLocality_Instrumentation.Proof_Results
      in result end) () of
       Exn.Res result => SOME result
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           (locality_pretty_trace ctxt 1 (fn () =>
              Pretty.text "Autolocality cancellation proof declined:"
              @ [Pretty.brk 1, Pretty.str (Runtime.exn_message exn)]
              |> Pretty.block);
            NONE))

  fun locality_prove_cancellation ctxt rec_name ctm
        ctm_decomposed ctm_decomposed_hoisted
        front_entries expected_rhs =
    locality_prove_cancellation_with
      (locality_direct_counter ctxt) ctxt rec_name ctm
      ctm_decomposed ctm_decomposed_hoisted
      front_entries expected_rhs

  fun select_locality_entry_for_pattern_kind_with count
        ctxt rec_name kind pattern =
    let
      val context = Context.Proof ctxt
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lookup_Requests
      val candidates =
        locality_pattern_keys_with
          count ctxt rec_name kind pattern
        |> LocalityOperationalKeyTable.keys
        |> locality_entries_for_keys_generic context
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Entries_Examined candidates
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Candidates_Returned candidates
    in
      case candidates of
        [] => NONE
      | entry :: _ =>
          if locality_entries_have_same_effect_with count candidates
          then SOME (locality_specialize_entry_with count ctxt pattern entry)
          else locality_registry_ambiguity
            ("Ambiguous autolocality pattern on " ^ rec_name)
    end

  fun select_locality_entry_for_pattern_with count
        ctxt rec_name kind_name pattern =
    select_locality_entry_for_pattern_kind_with count ctxt rec_name
      (locality_entry_kind_of_string kind_name) pattern

  fun select_locality_entry_for_pattern ctxt rec_name kind_name pattern =
    select_locality_entry_for_pattern_with
      (locality_direct_counter ctxt) ctxt rec_name kind_name pattern

  fun select_locality_entry_for_pattern_at_idx_kind_with count
        ctxt rec_name kind pattern idx =
    let
      val context = Context.Proof ctxt
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lookup_Requests
      val candidates =
        locality_pattern_at_idx_keys_with
          count ctxt rec_name kind pattern idx
        |> LocalityOperationalKeyTable.keys
        |> locality_entries_for_keys_generic context
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Entries_Examined candidates
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Candidates_Returned candidates
    in
      case candidates of
        [] => NONE
      | entry :: _ =>
          if locality_entries_have_same_effect_with count candidates
          then SOME (locality_specialize_entry_with count ctxt pattern entry)
          else locality_registry_ambiguity
            ("Ambiguous autolocality pattern on " ^ rec_name)
    end

  fun select_locality_entry_for_pattern_at_idx_with count
        ctxt rec_name kind_name pattern idx =
    select_locality_entry_for_pattern_at_idx_kind_with count ctxt rec_name
      (locality_entry_kind_of_string kind_name) pattern idx

  fun select_locality_entry_for_pattern_at_idx
        ctxt rec_name kind_name pattern idx =
    select_locality_entry_for_pattern_at_idx_with
      (locality_direct_counter ctxt)
      ctxt rec_name kind_name pattern idx

  fun locality_pattern_at_entry_type ctxt pattern
        (entry : locality_entry) =
    let
      val thy = Proof_Context.theory_of ctxt
      val target = #pattern entry
      val fresh_inc = Term.maxidx_of_term target + 1
      val pattern' =
        pattern
        |> locality_varify_types_preserving
             (locality_assumption_tfrees ctxt)
        |> Term.map_types (Logic.incr_tvar fresh_inc)
      val type_env =
        Sign.typ_match thy
          (Term.type_of pattern', Term.type_of target)
          Vartab.empty
    in
      Envir.subst_term_types type_env pattern'
    end

  fun locality_explicit_pattern_candidates_with count ctxt
        rec_name kind pattern absolute_idx =
    let
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Lookup_Requests
      val keys =
        (case absolute_idx of
           NONE =>
             locality_pattern_keys_with count ctxt rec_name kind pattern
         | SOME idx =>
             locality_pattern_at_idx_keys_with
               count ctxt rec_name kind pattern idx)
      val entries =
        locality_entries_for_keys_generic
          (Context.Proof ctxt)
          (LocalityOperationalKeyTable.keys keys)
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Entries_Examined entries
      fun specialize entry =
        capture_noninterrupt (fn () =>
          let
            val actual =
              locality_pattern_at_entry_type ctxt pattern entry
            val _ =
              if locality_entry_matches_prefix_with count
                   ctxt actual entry
              then ()
              else raise Pattern.MATCH
          in
            locality_specialize_entry_with count
              ctxt actual entry
          end)
      val candidates = map_filter specialize entries
      val _ = locality_count_list count
        AutoLocality_Instrumentation.Lookup_Candidates_Returned
        candidates
    in
      candidates
    end

  fun select_locality_entry_for_explicit_pattern_with count ctxt
        rec_name kind pattern absolute_idx =
    case locality_explicit_pattern_candidates_with count ctxt
           rec_name kind pattern absolute_idx of
      [] => NONE
    | entry :: entries =>
        if locality_entries_have_same_effect_with count
             (entry :: entries)
        then SOME entry
        else locality_registry_ambiguity
          ("Ambiguous autolocality pattern on " ^ rec_name)

  fun locality_commutativity_record_candidates_with count
        ctxt patternA patternB =
    let
      fun has_operation rec_name pattern =
        select_locality_entry_for_explicit_pattern_with count
          ctxt rec_name Locality_Operation pattern NONE
        |> Option.isSome
    in
      get_registered_records ctxt
      |> List.filter (fn rec_name =>
           has_operation rec_name patternA
             andalso has_operation rec_name patternB)
      |> sort_strings
    end

  fun locality_commutativity_record_candidates ctxt patternA patternB =
    locality_commutativity_record_candidates_with
      (locality_direct_counter ctxt) ctxt patternA patternB

  fun locality_cancellation_record_candidates_with count
        ctxt operation_pattern attribute_pattern
        attribute_relative_idx =
    let
      val attribute_absolute_idx =
        length (snd (Term.strip_comb attribute_pattern)) +
          attribute_relative_idx
      fun has_operation rec_name =
        select_locality_entry_for_explicit_pattern_with count
          ctxt rec_name Locality_Operation operation_pattern NONE
        |> Option.isSome
      fun has_attribute rec_name =
        select_locality_entry_for_explicit_pattern_with count
          ctxt rec_name Locality_Attribute attribute_pattern
          (SOME attribute_absolute_idx)
        |> Option.isSome
    in
      get_registered_records ctxt
      |> List.filter (fn rec_name =>
           has_operation rec_name andalso has_attribute rec_name)
      |> sort_strings
    end

  fun locality_cancellation_record_candidates ctxt
        operation_pattern attribute_pattern
        attribute_relative_idx =
    locality_cancellation_record_candidates_with
      (locality_direct_counter ctxt) ctxt
      operation_pattern attribute_pattern
      attribute_relative_idx

  fun locality_require_unique_record attribute_name candidates =
    case candidates of
      [rec_name] => rec_name
    | [] =>
        error (attribute_name ^ ": cannot infer a record type from the "
          ^ "supplied registrations; use the explicit (record_type) form")
    | _ =>
        error (attribute_name ^ ": record type is ambiguous among "
          ^ space_implode ", " (map quote candidates)
          ^ "; use the explicit (record_type) form")

  fun locality_infer_commutativity_record
        ctxt patternA patternB =
    locality_commutativity_record_candidates ctxt patternA patternB
    |> locality_require_unique_record
         "locality_autocommutativity"

  fun locality_infer_cancellation_record
        ctxt operation_pattern attribute_pattern
        attribute_relative_idx =
    locality_cancellation_record_candidates ctxt
      operation_pattern attribute_pattern
      attribute_relative_idx
    |> locality_require_unique_record
         "locality_autocancellation"

  \<comment>\<open>Auto-derive the pairwise commutativity theorem for two registered operations on a record:
     \<^verbatim>\<open>opA argsA (opB argsB R) = opB argsB (opA argsA R)\<close>, with the non-record arguments held as fixed
     fresh frees and the record threaded through the registered argument position of each.

     This is \<^emph>\<open>sound by construction\<close>: \<^verbatim>\<open>Goal.prove\<close> returns a theorem only if the proof closes, so a
     pair that does not actually commute yields \<^verbatim>\<open>NONE\<close> rather than a false 'theorem'. Two operations
     commute when their footprints are disjoint, because a registered footprint is a read-\<^emph>\<open>and\<close>-write
     footprint: an operation's \<^verbatim>\<open>_core\<close> lemma only proves at registration if it neither reads nor
     writes any field outside its footprint, so disjoint-footprint operations cannot observe or
     clobber each other. Operations sharing a field (e.g. two writers of the same field) genuinely
     do not commute and are correctly declined.

     The operation \<^emph>\<open>names\<close> may be short or qualified; they are resolved to the fully-qualified
     constant the footprint database is keyed under. Unlike the old eager generator, nothing is
     registered or stored - the caller decides what to do with the returned theorem. How this is
     best surfaced (a command, an attribute, an on-the-fly simproc for op-over-op telescopes) is
     left open; this is the core derivation.\<close>
  fun locality_prove_commutativity ctxt (rec_name0 : string) (patternA : term) (patternB : term)
        : thm option =
    let
      val count = locality_direct_counter ctxt
    in
    capture_noninterrupt (fn () => let
      val (_, rec_name) = prepare_rec_name ctxt rec_name0
      fun entry_of pattern =
        case select_locality_entry_for_pattern_kind_with count
               ctxt rec_name Locality_Operation pattern of
          SOME entry => entry
        | NONE => error "No matching operation footprint registration"
      val eA = entry_of patternA
      val eB = entry_of patternB
    in
      case locality_prove_commutativity_entries_with count
             ctxt rec_name eA eB of
        SOME thm => thm
      | NONE => error "Failed to derive operation commutativity"
    end)
    end

  \<comment>\<open>simproc identifying cancellable subexpressions in a term, and eliminating them.

  Given a term \<^verbatim>\<open>attr (op1 (op2 ... (opn r) ...))\<close> where \<^verbatim>\<open>attr\<close> is a registered attribute and
  the \<^verbatim>\<open>opi\<close> are registered operations, we identify those operations whose footprint is disjoint
  from everything between them and \<^verbatim>\<open>attr\<close> (so they can be hoisted out and then cancelled against
  \<^verbatim>\<open>attr\<close>). We compute the cancelled right-hand side directly from the telescope, then prove the
  equality \<^verbatim>\<open>lhs = rhs\<close> ad hoc via \<^verbatim>\<open>locality_prove_eq\<close>. No conversion choreography or pre-generated
  commutativity lemmas are needed.\<close>
  fun decompose_locality_telescope_with count
        ctxt rec_name (attribute : locality_entry) lhs =
    let
      val (head, args) = Term.strip_comb lhs
    in
      if locality_entry_matches_application_with count
           ctxt head args attribute then
        let
          val idx = locality_entry_absolute_idx attribute
          val record_term = nth args idx
          val (operations, body) =
            strip_comb_iter_with count
              (locality_operation_picker_with count ctxt rec_name) record_term
          val attribute_gap =
            (attribute, (head, List.take (args, idx), List.drop (args, idx + 1)))
        in (attribute_gap :: operations, body) end
      else ([], lhs)
    end

  fun decompose_locality_telescope ctxt rec_name attribute lhs =
    decompose_locality_telescope_with
      (locality_direct_counter ctxt) ctxt rec_name attribute lhs

  fun locality_cancellation_for_entry_with count
        rec_name (attribute0 : locality_entry) ctxt ctm =
    (case Exn.capture (fn () => let
       val lhs = Thm.term_of ctm
       val (head, args) = Term.strip_comb lhs
       val prefix_length = locality_entry_prefix_length attribute0
       val attribute =
         if length args >= prefix_length
         then locality_specialize_entry_with count ctxt
           (Term.list_comb (head, List.take (args, prefix_length))) attribute0
         else attribute0
       val _ = locality_pretty_trace ctxt 1 (fn () =>
         [Pretty.text "Locality simproc for"
          @ [Pretty.brk 1,
             Pretty.list "(" ")" [Pretty.str rec_name, Pretty.str (#const_name attribute)],
             Pretty.brk 1, Pretty.str "called"] |> Pretty.block,
          [Pretty.str "Term:", Pretty.brk 1, Syntax.pretty_term ctxt lhs]
          |> Pretty.block]
         |> Pretty.chunks)

       val ctm_decomposed =
         decompose_locality_telescope_with count
           ctxt rec_name attribute lhs

       (* Identify redundant operations in the body of the attribute and hoist them out *)
       val (no_op, ctm_decomposed_hoisted, front_entries, back_entries) = ctm_decomposed
         |> hoist_redundant_operations_with count

       \<comment>\<open>Helper function to pretty-print the result of \<^verbatim>\<open>strip_comb_iter\<close>\<close>
       fun print_strip_comb_iter_result (ctxt : Proof.context)
         ([], t) = [Syntax.pretty_term ctxt t]
       | print_strip_comb_iter_result ctxt ((entry, (cur, pre, post)) :: ls, t) =
             Pretty.fbreaks ([[Syntax.pretty_term ctxt cur, Pretty.brk 1, Pretty.enclose "\<llangle>INFO: " "\<rrangle>" [pretty_locality_entry ctxt rec_name entry]] |> Pretty.block]
              @ List.map (Syntax.pretty_term ctxt) pre
              @ [Pretty.block (print_strip_comb_iter_result ctxt (ls, t))]
              @ List.map (Syntax.pretty_term ctxt) post)

      val _ = locality_pretty_trace ctxt 1 (fn () =>
        print_strip_comb_iter_result ctxt ctm_decomposed |> Pretty.block)
      val _ = locality_pretty_trace ctxt 1 (fn () =>
        print_strip_comb_iter_result ctxt ctm_decomposed_hoisted |> Pretty.block)

    in if no_op then NONE else let

       (* The hoisted telescope is (attr :: front @ back, body), where 'front' are the
          cancellable (disjoint) operations. Dropping them gives the cancelled telescope,
          and recombining yields the desired right-hand side. *)
       val cancelled_decomp =
         case ctm_decomposed_hoisted of
           (attr_gap :: rest, body) => (attr_gap :: List.drop (rest, length front_entries), body)
         | x => x
       val rhs = recombine_decomposed_comb_with count cancelled_decomp

       val _ = locality_pretty_trace ctxt 1 (fn () =>
         [Pretty.str "Cancelled RHS:", Pretty.brk 1, Syntax.pretty_term ctxt rhs]
         |> Pretty.block)
    in
       case locality_prove_cancellation_with count ctxt rec_name ctm
              ctm_decomposed ctm_decomposed_hoisted
              front_entries rhs of
         NONE => NONE
       | SOME thm =>
           (let val _ = locality_pretty_trace ctxt 1 (fn () =>
                  [Pretty.str "Final equation:", Pretty.brk 1,
                   Syntax.pretty_term ctxt (Thm.prop_of thm)]
                  |> Pretty.block)
            in SOME thm end)
    end end) () of
       Exn.Res result => result
     | Exn.Exn exn =>
          if Exn.is_interrupt exn then Exn.reraise exn
          else (case exn of
            Locality_Registry_Ambiguity _ => Exn.reraise exn
          | _ =>
            (locality_pretty_trace ctxt 1 (fn () =>
               Pretty.text "locality cancellation declined after exception:"
               @ [Pretty.brk 1, Pretty.str (Runtime.exn_message exn)]
               |> Pretty.block);
             NONE)))

  fun locality_cancellation_for_entry rec_name attribute ctxt ctm =
    locality_cancellation_for_entry_with
      (locality_direct_counter ctxt) rec_name attribute ctxt ctm

  fun locality_cancellation_simproc_for_entry rec_name attribute ctxt ctm =
    if not (Config.get ctxt locality_cancel_enabled) then NONE
    else
      locality_with_callback ctxt (fn count =>
        locality_cancellation_for_entry_with count
          rec_name attribute ctxt ctm)

  \<comment>\<open>Compatibility entry point used by the ML regression harness. Simprocs installed by
     declarations close over only their family dispatch key and do not use this
     name-based lookup.\<close>
  fun locality_cancellation_simproc rec_name attr_name idx ctxt ctm =
    if not (Config.get ctxt locality_cancel_enabled) then NONE
    else
      locality_with_callback ctxt (fn count =>
        let
          val context = Context.Proof ctxt
          val parsed_const =
            try (Syntax.read_term ctxt #> extract_const) attr_name
          val (head, args) = ctm |> Thm.term_of |> Term.strip_comb
          fun name_matches (entry : locality_entry) =
               #const_name entry = attr_name
            orelse Long_Name.base_name (#const_name entry) = Long_Name.base_name attr_name
            orelse parsed_const = SOME (#const_name entry)
          val _ = locality_count_one count
            AutoLocality_Instrumentation.Lookup_Requests
          val lookup_names =
            attr_name :: Long_Name.base_name attr_name
              :: the_list parsed_const
          val keys =
            locality_keys_for_names_with count context rec_name lookup_names
            |> LocalityOperationalKeyTable.keys
          val entries =
            locality_entries_for_keys_generic context keys
          val _ = locality_count_list count
            AutoLocality_Instrumentation.Lookup_Entries_Examined entries
          val candidates =
            entries
            |> List.filter (fn (entry : locality_entry) =>
                 locality_entry_kind entry = Locality_Attribute
                 andalso name_matches entry)
            |> List.filter
                 (locality_entry_matches_application_with count ctxt head args)
          val max_prefix =
            fold (fn entry => fn n =>
              Int.max (locality_entry_prefix_length entry, n)) candidates 0
          val candidates =
            candidates
            |> List.filter (fn entry =>
                 locality_entry_prefix_length entry = max_prefix)
          val _ = locality_count_list count
            AutoLocality_Instrumentation.Lookup_Candidates_Returned candidates
        in
          case try (nth candidates) idx of
            NONE => NONE
          | SOME entry =>
              let
                val n = locality_entry_prefix_length entry
              val actual = Term.list_comb (head, List.take (args, n))
            in
                locality_cancellation_for_entry_with count rec_name
                  (locality_specialize_entry_with count ctxt actual entry)
                  ctxt ctm
              end
        end)

  fun locality_prove_cancellation_fact ctxt (rec_name0 : string)
        (operation_pattern : term) (attribute_pattern : term)
        (attribute_relative_idx : int)
        : thm option =
    let
      val count = locality_direct_counter ctxt
    in
    capture_noninterrupt (fn () =>
      let
        val (_, rec_name) = prepare_rec_name ctxt rec_name0
        val operation =
          case select_locality_entry_for_pattern_kind_with count
                 ctxt rec_name Locality_Operation operation_pattern of
            SOME entry => entry
          | NONE => error "No matching operation footprint registration"
        val attribute_absolute_idx =
          length (snd (Term.strip_comb attribute_pattern)) +
            attribute_relative_idx
        val attribute =
          case select_locality_entry_for_pattern_at_idx_kind_with count
                 ctxt rec_name Locality_Attribute
                 attribute_pattern attribute_absolute_idx of
            SOME entry => entry
          | NONE => error "No matching attribute footprint registration"
        val (operation_record_type, apply_operation) =
          locality_operation_applier operation "operation_"
        val (attribute_record_type, apply_attribute) =
          locality_operation_applier attribute "attribute_"
        val _ =
          if operation_record_type = attribute_record_type then ()
          else error "Operation and attribute record types do not agree"
        val record = Free ("R", operation_record_type)
        val _ = locality_count_one count
          AutoLocality_Instrumentation.Proof_Cterms
        val ctm =
          record
          |> apply_operation
          |> apply_attribute
          |> Thm.cterm_of ctxt
      in
        case locality_cancellation_for_entry_with count
               rec_name attribute ctxt ctm of
          SOME thm =>
            (locality_count_one count
               AutoLocality_Instrumentation.Proof_Compositions;
             thm RS @{thm meta_eq_to_obj_eq})
        | NONE => error "Failed to derive operation/attribute cancellation"
      end)
    end

  fun locality_dispatch_canonical_type typ =
    let
      fun add_variable (T as TVar _) = insert (op =) T
        | add_variable (T as TFree _) = insert (op =) T
        | add_variable _ = I
      fun variable_sort (TVar (_, sort)) = sort
        | variable_sort (TFree (_, sort)) = sort
        | variable_sort _ =
            error "Non-variable type in AutoLocality dispatcher scheme"
      val variables =
        Term.fold_atyps add_variable typ []
        |> sort Term_Ord.typ_ord
      val instantiations =
        variables |> map_index (fn (i, variable) =>
          (variable,
           TVar (("locality_dispatch_type", i),
             variable_sort variable)))
      fun canonicalize atyp =
        AList.lookup (op =) instantiations atyp
        |> the_default atyp
    in
      Term.map_atyps canonicalize typ
    end

  fun locality_dispatch_trigger ctxt
        (dispatch_key : locality_dispatch_key) =
    let
      val thy = Proof_Context.theory_of ctxt
      val head_type =
        Sign.the_const_type thy (#head_name dispatch_key)
        |> locality_dispatch_canonical_type
      val argument_types = Term.binder_types head_type
      val _ =
        if length argument_types = #arity dispatch_key then ()
        else
          error ("Stale AutoLocality dispatcher arity for "
            ^ describe_locality_dispatch_key dispatch_key)
      val arguments =
        argument_types |> map_index (fn (i, typ) =>
          Var (("locality_dispatch_arg", i), typ))
      val trigger =
        Term.list_comb
          (Const (#head_name dispatch_key, head_type), arguments)
        |> Envir.beta_eta_contract
      val _ =
        if null (Term.add_tfrees trigger [])
          andalso null (Term.add_frees trigger [])
        then ()
        else
          error ("AutoLocality dispatcher trigger captures fixed variables for "
            ^ describe_locality_dispatch_key dispatch_key)
    in
      trigger
    end

  fun locality_dispatch_key_of_trigger trigger : locality_dispatch_key =
    let
      val (head, arguments) =
        trigger
        |> Envir.beta_eta_contract
        |> Term.strip_comb
    in
      { head_name = locality_rigid_head_name head,
        arity = length arguments }
    end

  fun locality_dispatch_witness ctxt dispatch_key =
    locality_dispatch_trigger ctxt dispatch_key
    |> Thm.cterm_of ctxt
    |> Drule.mk_term
    |> Thm.trim_context

  fun locality_cancellation_simproc_for_dispatch
        dispatch_key ctxt ctm =
    if not (Config.get ctxt locality_cancel_enabled) then NONE
    else
      locality_with_callback ctxt (fn count =>
        let
          val context = Context.Proof ctxt
          val actual = Thm.term_of ctm
          val _ = locality_count_one count
            AutoLocality_Instrumentation.Lookup_Requests
          val queries =
            locality_dispatch_ranked_key_queries_with
              count ctxt dispatch_key actual

          fun try_entries [] = NONE
            | try_entries (entry :: entries) =
                (case locality_cancellation_for_entry_with count
                        (locality_entry_record_name entry) entry ctxt ctm of
                   NONE => try_entries entries
                 | result => result)

          fun try_queries [] = NONE
            | try_queries
                ((query : locality_ranked_key_query) :: queries') =
                let
                  val keys =
                    #retrieve query ()
                    |> locality_equality_valid_keys_with
                         count ctxt (#actual query)
                in
                  if LocalityOperationalKeyTable.is_empty keys then
                    try_queries queries'
                  else
                    let
                      val entries =
                        keys
                        |> LocalityOperationalKeyTable.keys
                        |> locality_entries_for_keys_generic context
                      val _ = locality_count_list count
                        AutoLocality_Instrumentation.Lookup_Entries_Examined
                        entries
                      val _ = locality_count_list count
                        AutoLocality_Instrumentation.Lookup_Candidates_Returned
                        entries
                    in
                      \<comment>\<open>The first nonempty equality-valid rank shadows every
                         lower rank, even when all of its cancellation
                         attempts decline.\<close>
                      try_entries entries
                    end
                end
        in
          try_queries queries
        end)

  fun locality_simproc_binding dispatch_key =
    locality_dispatch_simproc_binding dispatch_key

  fun locality_simproc_spec ctxt dispatch_key identifier :
      (term, morphism -> Simplifier.proc, thm list)
        Simplifier.simproc_spec =
    let
      val count = locality_direct_counter ctxt
      val trigger = locality_dispatch_trigger ctxt dispatch_key
      val _ = locality_count_one count
        AutoLocality_Instrumentation.Proof_Cterms
      val simproc_binding = locality_simproc_binding dispatch_key
      val _ = locality_pretty_trace ctxt 0 (fn () =>
        Pretty.text ("Creating locality dispatcher for ")
        @ [Pretty.str (describe_locality_dispatch_key dispatch_key),
           Pretty.brk 1, Syntax.pretty_term ctxt trigger]
        |> Pretty.block)
    in
      { passive = false,
        name = simproc_binding,
        kind = Simproc,
        lhss = [trigger],
        proc = fn _ =>
          locality_cancellation_simproc_for_dispatch dispatch_key,
        identifier = [identifier] }
    end

  type locality_entry_descriptor = {
    record_name: string,
    kind: locality_entry_kind,
    const_name: string,
    flexible_prefix: bool list,
    footprint: string list,
    args: int,
    idx: int,
    field: bool,
    core_count: int,
    disjoint_count: int,
    has_local: bool
  }

  fun locality_entry_descriptor (entry : locality_entry) :
        locality_entry_descriptor =
    { record_name = locality_entry_record_name entry,
      kind = locality_entry_kind entry,
      const_name = #const_name entry,
      flexible_prefix = locality_entry_flexible_prefix entry,
      footprint = #footprint entry,
      args = locality_entry_args entry,
      idx = locality_entry_idx entry,
      field = #field entry,
      core_count = length (#core_thms entry),
      disjoint_count = length (#disjoint_thms entry),
      has_local = Option.isSome (#local_thm entry) }

  fun locality_entry_fact_bundle lthy (entry : locality_entry) =
    map Thm.trim_context
      (Drule.mk_term (Thm.cterm_of lthy (#pattern entry))
        :: (#core_thms entry @ #disjoint_thms entry
          @ the_list (#local_thm entry)))

  fun locality_trim_morphism context phi =
    Morphism.set_trim_context'' context phi

  fun morph_locality_entry_bundle_with psi
        (descriptor : locality_entry_descriptor) facts0 : locality_entry =
    let
      val facts = Morphism.fact psi facts0
      val (pattern_fact, certificate_facts) =
        (case facts of
           fact :: facts' => (fact, facts')
         | [] => error "Missing autolocality operational-pattern witness")
      val pattern = Thm.term_of (Drule.dest_term pattern_fact)
      val (core_thms0, certificate_facts') =
        chop (#core_count descriptor) certificate_facts
      val (disjoint_thms0, local_facts) =
        chop (#disjoint_count descriptor) certificate_facts'
      val finish = Thm.trim_context
      val local_thm =
        (case (#has_local descriptor, local_facts) of
           (false, []) => NONE
         | (true, [thm]) => SOME (finish thm)
         | _ => error "Malformed autolocality certificate bundle")
    in
      make_locality_entry
        (#record_name descriptor) (#kind descriptor)
        (#const_name descriptor) pattern
        (#flexible_prefix descriptor) (#footprint descriptor)
        (#args descriptor) (#idx descriptor) (#field descriptor)
        (map finish core_thms0) (map finish disjoint_thms0) local_thm
    end

  fun morph_locality_entry_bundle context phi descriptor facts0 =
    morph_locality_entry_bundle_with
      (locality_trim_morphism context phi) descriptor facts0

  fun replay_locality_dispatcher_name dispatch_key origin source_name
        binding phi context =
    let
      val ctxt = Context.proof_of context
      val alias =
        Name_Space.full_name (Name_Space.naming_of context)
          (Morphism.binding phi binding)
      val _ =
        Simplifier.the_simproc ctxt alias
        handle ERROR msg =>
          error ("Failed to resolve local AutoLocality named simproc "
            ^ quote alias ^ " for "
            ^ describe_locality_dispatch_key dispatch_key
            ^ ":\n" ^ msg)
    in
      LocalityDispatcherInventory.map
        (insert_locality_dispatcher_alias
          dispatch_key origin source_name alias) context
    end

  fun ensure_locality_dispatcher dispatch_key lthy =
    let
      val current_context = Context.Proof lthy
      val target_context =
        Context.Proof (Local_Theory.target_of lthy)
      val current_entry =
        locality_dispatcher_entry current_context dispatch_key
      val target_entry =
        locality_dispatcher_entry target_context dispatch_key
    in
      case (target_entry, current_entry) of
        (SOME _, SOME _) =>
          let
            val _ =
              AutoLocality_Instrumentation.record_counters lthy (fn () =>
                [(AutoLocality_Instrumentation.Lifecycle_Duplicate_Dispatchers,
                  1)])
          in
            lthy
          end
      | (NONE, SOME _) =>
          error ("AutoLocality dispatcher for "
            ^ describe_locality_dispatch_key dispatch_key
            ^ " is visible only in a temporary local context; "
            ^ "register it in its owning local theory")
      | (SOME _, NONE) =>
          error ("AutoLocality target dispatcher is absent from the "
            ^ "current local theory for "
            ^ describe_locality_dispatch_key dispatch_key)
      | (NONE, NONE) =>
          let
            val binding = locality_simproc_binding dispatch_key
            val origin = stamp ()
            val source_name =
              Local_Theory.full_name lthy binding
            val identifier =
              locality_dispatch_witness lthy dispatch_key
            val (_, lthy') =
              Simplifier.define_simproc
                (locality_simproc_spec
                  lthy dispatch_key identifier) lthy
            val lthy'' =
              lthy'
              |> Local_Theory.declaration
                   {pervasive = false, syntax = false,
                    pos = Binding.pos_of binding}
                   (replay_locality_dispatcher_name
                     dispatch_key origin source_name binding)
            val _ =
              if locality_dispatcher_declared
                   (Context.Proof lthy'') dispatch_key
                 andalso locality_dispatcher_declared
                   (Context.Proof
                     (Local_Theory.target_of lthy'')) dispatch_key
              then ()
              else
                error ("Failed to declare local AutoLocality dispatcher for "
                  ^ describe_locality_dispatch_key dispatch_key)
            val _ =
              AutoLocality_Instrumentation.record_counters lthy''
                (fn () =>
                  [(AutoLocality_Instrumentation.Lifecycle_Dispatcher_Insertions,
                    1)])
          in
            lthy''
          end
    end

  fun replay_locality_registration rec_name descriptor facts0 phi context =
    let
      val ctxt = Context.proof_of context
      val entry =
        morph_locality_entry_bundle context phi descriptor facts0
    in
      add_record_locality_entry_generic ctxt rec_name entry context
    end

  \<comment>\<open>Declare a complete typed registration. Attribute families receive one
     ordinary local named simproc declaration. Its generic callback consults the
     separately declared, morphism-aware semantic registry at invocation time.
     A small local name inventory supports explicit reactivation after
     \<^verbatim>\<open>simp only:\<close>; it does not own theorem payloads or require background-theory
     installation.\<close>
  fun add_record_locality_entry ctxt (rec_name : string)
        (entry : locality_entry) lthy =
    let
      val _ = locality_pretty_trace ctxt 1 (fn () =>
        [Pretty.str "add_record_locality_entry", Pretty.brk 1,
         Syntax.pretty_term ctxt (#pattern entry), Pretty.brk 1,
         Pretty.list "[" "]" (List.map Pretty.str (#footprint entry))]
        |> Pretty.block)
      val descriptor = locality_entry_descriptor entry
      val facts0 = locality_entry_fact_bundle lthy entry
      val dispatch_key =
        if locality_entry_kind entry = Locality_Attribute
        then locality_dispatch_key_of_entry_opt ctxt entry
        else NONE
      val lthy' =
        (case dispatch_key of
           NONE => lthy
         | SOME key => ensure_locality_dispatcher key lthy)
      fun declare_registration lthy' =
        Local_Theory.declaration
          {pervasive = false, syntax = false, pos = Position.none}
          (replay_locality_registration
            rec_name descriptor facts0)
          lthy'
    in
      declare_registration lthy'
    end

  \<comment>\<open>End of the simproc code\<close>

  fun state_locality_for_op attribs_opt (rec_name : string) (p_name: string)
    (footprint: string list) (with_proof : bool) (ctxt : Proof.context)  =
    let
      (* Lookup fields from record *)
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val field_selectors_full = locality_field_selector_names ctxt rec_name
      val fields = map Long_Name.base_name field_selectors_full
      val field_updates_full = get_field_updates_full rec_name ctxt
      fun field_selector_for field =
        locality_field_name_lookup "field" field_selectors_full field
      fun field_update_for field =
        case List.find (fn name => dest_field_update name = SOME field)
               field_updates_full of
          SOME name => name
        | NONE => error ("Unknown record field update " ^ quote field)

      (* Checks if a string is a field in the given record *)
      fun check_field (f0 : string) : bool = List.exists (fn f1 => f0 = f1) fields
      (* Check that the footprint is a list of fields *)
      val footprint_ok = List.all check_field footprint

      (* Lookup disjoint fields -- we'll need one orthogonality lemma for each of them *)
      val disjoint_fields = List.filter (fn f0 => List.all (fn f1 => f0 <> f1) footprint) fields
      val _ = (if not footprint_ok then
         (  "Invalid footprint "
         ^ fieldlist_to_str footprint
         ^ " for record " ^ rec_name ^ " with fields "
         ^ fieldlist_to_str fields
         |> error) else ())

      val p_term = Syntax.read_term ctxt p_name

      (* Get rid of positioning information that's inherent in p_name and rec_name since they
         are produced by Parse.typ and Parse.term, respectively. Otherwise, the proposition-strings
         built below won't be recognized. *)
      val p_name = p_term |> extract_const
      val rec_name = Syntax.read_input rec_name |> Input.string_of

      val is_field = member (op =) field_updates_full p_name

      (* Check that the given term is indeed a function on the given record *)
      val (_, num_args, rec_namex) =  dest_fun_term ctxt rec_ty p_term |> Option.valOf
      (* Identifier used for the generated fact names. For a bare constant this is just its base
         name (keeping the common-case names stable). For a PARTIAL APPLICATION - e.g.
         'w_apply_policy policy_a' - the baked-in argument is what
         distinguishes one locality_lemma from another with the same head constant, so it must enter
         the name: deriving p_id from the head alone makes the two collide (duplicate fact). We
         therefore fold the applied arguments into the identifier via the pretty-printed term. *)
      (* A PARTIAL APPLICATION is the operator applied to one or more CONSTANT arguments — e.g.
         'w_apply_policy policy_a'. We must distinguish these from
         LOCALE PARAMETERS, which 'Syntax.read_term' also applies to the bare constant but as fixed
         'Free's (e.g. inside locale 'scaler', 'bumpval' reads as 'scaler.bumpval $ Free bump'). Only
         the Const-headed arguments count: they are what the baked-in operator must carry. Locale
         parameters are left to the ordinary 'make_arglist'/'num_args' machinery (which fills the
         remaining argument positions), so the locale case keeps the original behaviour. *)
      (* Baked-in constants enter 'discharge_cnames' below, so their definitions are unfolded by
         the automatic discharge in order to expose the field footprint: 'w_apply_policy policy_a'
         needs 'policy_a_def' before wf04 becomes visible. Two guards keep that from unfolding
         arguments where it cannot help.

         (1) The constant's type must mention the record type. A bool, numeral or string literal
             carries no record structure, so unfolding it can reveal no field of the record.

         (2) The constant must not be declared by the logical core, i.e. by a theory at or below
             \<^theory>\<open>HOL\<close>. Core constants do have definitions, but those are the
             axiomatic underpinning of the logic rather than operations on data:
             \<^const>\<open>True\<close> is defined as \<^term>\<open>(\<lambda>x::bool. x) = (\<lambda>x. x)\<close>,
             so handing 'True_def' to the simplifier rewrites its own normal form and the
             discharge diverges instead of failing.

         The declaring theory is resolved through the constant name space rather than by
         inspecting the long name, so a user constant that merely happens to sit in a
         'HOL'-prefixed namespace is not misclassified. Narrowing this list cannot rename any
         generated fact: 'locality_public_id' decides partial-application naming from 'p_term'
         with its own, deliberately broader, test. *)
      fun baked_const_unfoldable (c, T) =
        let
          val mentions_record =
            T |> Term.exists_subtype (fn Type (n, _) => n = rec_name | _ => false)
          val declaring_theory =
            try (Name_Space.theory_name {long = true}
                  (Consts.space_of (Proof_Context.consts_of ctxt))) c
          val from_logical_core =
            (case declaring_theory of
               NONE => false
             | SOME thy_name =>
                 (case try (Theory.check {long = true} ctxt) (thy_name, Position.none) of
                    NONE => false
                  | SOME thy => Context.subthy (thy, \<^theory>\<open>HOL\<close>)))
        in
          mentions_record andalso not from_logical_core
        end

      val baked_cnames = snd (Term.strip_comb p_term) |> map_filter (fn t =>
        case Term.head_of t of
          Const (c, T) => if baked_const_unfoldable (c, T) then SOME c else NONE
        | _ => NONE)

      (* Identifier used for the generated fact names. For a bare constant (or one applied only to
         locale parameters) this is its base name, keeping the common-case names stable; for a genuine
         partial application the baked-in constant must enter the name, or two locality_lemmas with the
         same head constant collide (duplicate fact). *)
      val p_id = locality_public_id ctxt p_term
      val _ =
        assert_locality_public_id_available ctxt rec_name
          Locality_Operation rec_namex p_id p_term

      (* The operator string used to BUILD the lemma statements: the pretty-printed term itself,
         wrapped in parens for safe re-parsing. This is correct in all three cases: a bare constant
         prints as its (short, re-parseable) name; a genuine partial application keeps its baked
         argument ('(w_apply_policy policy_a)') rather than abstracting it into a fresh variable; and
         a locale operation prints with its parameter in the short form that re-parses with the
         parameter re-applied (the fully-qualified head 'p_name' would NOT re-apply it, causing a
         type clash). *)
      val p_op_str = "(" ^ (Syntax.pretty_term ctxt p_term |> Pretty.pure_string_of) ^ ")"

      val helper_plan =
        locality_body_helper_plan ctxt rec_name p_name
      val helper_certificates = #certificates helper_plan

      (* Constants to unfold when discharging: the operation, the constants baked into a partial
         application, and helpers whose actual applications have no matching registration. *)
      val discharge_cnames =
        (p_name :: baked_cnames
          @ #unfold helper_plan)
        |> distinct (op =)

      fun arglist_with x =
            make_arglist num_args
         |> list_set_nth rec_namex x
         |> String.concatWith " "
      val argsA = arglist_with "R"
      fun argsB field =
        arglist_with ("(" ^ field_update_for field ^ " f R)")

      (* Build statements of locality lemmas *)
      fun commutativity_str (prop : string) (field : string) =
          "\<And>f " ^ argsA ^ " . " ^ prop ^ " " ^ argsB field ^ " = " ^
                               field_update_for field ^ " f (" ^ prop ^ " " ^ argsA ^ ")"
      fun get_commutativity_stm prop field = commutativity_str prop field |> Syntax.read_prop ctxt
      val commutativity_stms = List.map (get_commutativity_stm p_op_str) disjoint_fields

      (* Build statements of disjointness lemmas *)
      fun disjoint_str (prop : string) (field : string) =
         let val field_proj = field_selector_for field in
           "\<And>f " ^ argsA ^ ". " ^ field_proj ^ " (" ^ prop ^ " " ^ argsA ^ ") = " ^
                               field_proj ^ " R"
         end
      fun get_disjoint_stm prop field = disjoint_str prop field |> Syntax.read_prop ctxt
      val disjoint_stms = List.map (get_disjoint_stm p_op_str) disjoint_fields

      fun make_iterated_field_update fields_with_vals arg =
         fold (fn (f,v) => fn s => field_update_for f ^ " (\<lambda>_. " ^ v ^ ") (" ^ s ^ ")")
              fields_with_vals
              ("(" ^ arg ^ ")")

      fun field_proj field = field_selector_for field

      \<comment>\<open>Build a no-op telescope of field updates: each field is rewritten to its own current
         projection, so the telescoped record is provably equal to the original. Used by the
         disjointness proof to introduce the disjoint fields under a no-op update before pushing
         them past the operation via commutativity.\<close>
      fun make_noop_iterated_field_update fields arg =
         let val fields_with_vals = List.map (fn f => (f, field_proj f ^ " (" ^ arg ^ ")")) fields
         in make_iterated_field_update fields_with_vals arg end

      (* Build statements of 'local action' lemmas *)
      fun local_action_str (prop : string) =
         let
             fun new_field_val f = field_proj f ^ "( " ^ prop ^ " " ^ argsA ^ ")"
             val footprint_with_vals = List.map (fn f => (f, new_field_val f)) footprint
             val field_updates = make_iterated_field_update footprint_with_vals "R"
         in
           "\<And>f " ^ argsA ^ ". " ^ prop ^ " " ^ argsA ^ " = " ^ field_updates
         end
      val local_action_stm = local_action_str p_op_str |> Syntax.read_prop ctxt

      val commutativity_thm_name = register_locality_op_commutativity_thm_name rec_name p_id
      val disjointness_thm_name = register_locality_op_disjointness_thm_name rec_name p_id
      val local_action_thm_name = register_locality_op_local_action_thm_name rec_name p_id
      val flexible_prefix = locality_pattern_flexible_prefix p_term
      val replay =
        locality_registration_is_replay ctxt rec_name p_name p_term
          flexible_prefix Locality_Operation
          footprint num_args rec_namex is_field
          (length disjoint_fields) (length disjoint_fields) true

      fun after_qed (apply_attribs : bool) (named_thm_list_opt) name (cont : Proof.context -> Proof.context) thms ctxt =
        let val thms = thms |> flat
          val attribs = unpack_attributes_default ctxt rec_name attribs_opt
           |> List.map (Attrib.check_src ctxt)
          val default_attribs = not (Option.isSome attribs_opt)
          val public_attribs =
            if apply_attribs andalso default_attribs then attribs else []
          val note_explicit_attribs =
            apply_attribs andalso not default_attribs
        in ctxt
           |> (case named_thm_list_opt of
               SOME n => fold (fn t => Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none} (fn _ => Named_Theorems.add_thm n t)) thms
             | NONE => I)
           |> Local_Theory.note
                (((Binding.name name), public_attribs), thms) |> snd
           |> (if note_explicit_attribs then
                 (Local_Theory.note ((Binding.empty,attribs), thms) #> snd)
               else
                 I)
           |> cont
        end

      \<comment>\<open>The core (commutativity-with-disjoint-field-updates) lemmas remain interactive, so the
         user can supply a manual proof for awkward operations. The automatic attempt is the old
         method-string \<^verbatim>\<open>auto simp add: Let_def <defs> <_locality_facts>\<close>, which is a single \<^verbatim>\<open>auto\<close>
         call against the ambient simpset. Switching to an ML-built simpset regressed this badly:
         the ML approach constructs an ambient+\<^verbatim>\<open>record_simps\<close>+facts simpset eagerly per phase per
         field-update during \<^verbatim>\<open>locality_init\<close> (~1.8s for 21 constructions on a wide record), even when
         the goal closes by trivial rewriting; the method-string form lets the simplifier reuse the
         already-indexed ambient net.\<close>
      val default_simps =
        let val const_unfold =
              discharge_cnames |> map_filter (locality_def_fact_name ctxt)
            val helper_facts =
              if null helper_certificates then []
              else [locality_body_helper_certificate_fact]
            val locality_facts = if Option.isSome attribs_opt then [] else [default_named_theorems_for_record rec_name]
            val all_simps =
              ["Let_def"] @ const_unfold @ helper_facts @ locality_facts
        in
          String.concatWith " " all_simps
        end
      val default_splits = String.concatWith " " (locality_body_case_split_names ctxt discharge_cnames)

      fun start_core_proof ctxt cont =
        let
          val method_ctxt =
            locality_body_helper_method_context
              ctxt helper_certificates
        in
          ctxt
          |> Proof.theorem NONE (after_qed (not is_field) NONE commutativity_thm_name cont) [map (fn t => (t,[])) commutativity_stms]
          |> apply_method (SIMPLE_METHOD all_tac)
          |> (if with_proof then
               apply_txt method_ctxt
                 ("(auto simp add: " ^ default_simps
                   ^ " split: " ^ default_splits ^ ")?")
             else
               I)
        end

      \<comment>\<open>The 'local action' lemma is fully automatic. The old method-string discharge is
         \<^verbatim>\<open>auto intro: <rec>.expand simp add: <disjointness>\<close>: extensionality reduces to per-field
         equalities which the disjointness lemma normalises. We re-enter an interactive proof and
         globally close it, which keeps the proof shape uniform with \<^verbatim>\<open>derive_disjointness\<close> and avoids
         the eager ML simpset construction that the WIP rewrite paid per op.\<close>
      fun derive_locality cont ctxt =
         let
           val expand_thm_name =
             locality_record_expand_thm_name ctxt rec_name
           val _ = locality_pretty_trace ctxt 0 (fn () =>
             [Pretty.str "Autoderive locality theorem: ",
              Syntax.pretty_term ctxt local_action_stm]
             |> Pretty.breaks |> Pretty.block) in
           (   ctxt
            |> Proof.theorem NONE (after_qed false NONE local_action_thm_name cont) [map (fn t => (t,[])) [local_action_stm]]
            |> apply_method (SIMPLE_METHOD all_tac)
            |> apply_txt ctxt ("(auto intro: " ^ expand_thm_name
                 ^ " simp add: " ^ disjointness_thm_name ^ ")")
            |> Proof.global_done_proof)
           handle ERROR _ =>
              ([Pretty.str "Something went wrong proving locality theorem: ",
                Syntax.pretty_term ctxt local_action_stm]
               |> Pretty.breaks |> Pretty.block |> Pretty.string_of |> warning; ctxt)
         end

      \<comment>\<open>The disjointness lemmas (field projections not in the footprint are unaffected by the
         operation) are proved by the old \<^verbatim>\<open>subgoal_tac\<close>+\<^verbatim>\<open>simp\<close>+\<^verbatim>\<open>subst commutativity\<close> trick: rewrite
         the operation to a record where the disjoint field has been refreshed by a no-op update,
         then push that update past the operation via the freshly-proved commutativity lemma, and
         simplify. As with the core proof we use the method-string form to avoid eager ML simpset
         construction.\<close>
      fun derive_disjointness cont ctxt =
        let val subgoal = p_op_str ^ " " ^ argsA ^ " = " ^
               p_op_str ^ " " ^ arglist_with ("(" ^ make_noop_iterated_field_update disjoint_fields "R" ^ ")")
        in
           (  ctxt
           |> Proof.theorem NONE (after_qed true NONE disjointness_thm_name cont) [map (fn t => (t,[])) disjoint_stms]
           |> apply_method (SIMPLE_METHOD all_tac)
           |> apply_txt ctxt ("(subgoal_tac\<open>" ^ subgoal ^ "\<close>"
                      ^ ", " ^ "simp only:"
                      ^ ", " ^ "(subst " ^ commutativity_thm_name ^ ")+"
                      ^ ", " ^ "simp, simp)+")
           |> Proof.global_done_proof)
           handle ERROR e => (
              [Pretty.text "Something went wrong proving disjointness theorem:" |> Pretty.block]
              @ List.map (Syntax.pretty_term ctxt) disjoint_stms
              @ [Pretty.text "This is the original error message:" |> Pretty.block,
                 Pretty.text e |> Pretty.block]
              |> Pretty.chunks |> Pretty.string_of |> warning; ctxt)
         end

       fun wrapup ctxt =
         let
           val local_thms = Proof_Context.get_thms ctxt local_action_thm_name
           val local_thm =
             (case local_thms of
                [thm] => SOME thm
              | _ => error ("Expected one local-action theorem for " ^ p_name))
           val entry : locality_entry =
             make_locality_entry rec_name Locality_Operation
               p_name p_term flexible_prefix footprint num_args rec_namex
               is_field
               (Proof_Context.get_thms ctxt commutativity_thm_name)
               (Proof_Context.get_thms ctxt disjointness_thm_name)
               local_thm
         in
           add_record_locality_entry ctxt rec_name entry ctxt
         end
    in
      if replay then
        locality_registration_replay_proof ctxt
      else
        let
          val (_, _, ctxt') =
            check_create_named_theorems
              (default_named_theorems_for_record rec_name) ctxt
        in
          start_core_proof ctxt'
            (derive_disjointness (derive_locality wrapup))
        end
    end

  fun state_locality_for_attribute attribs_opt (rec_name : string) (p_term: term)
      (footprint: string list) (with_proof : bool) (rec_namex : int) (ctxt : Proof.context)  =
    let 
      (* Lookup fields from record *)
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val fields = get_fields rec_name ctxt

      val strlist_to_str = String.concatWith ", "
      fun fieldlist_to_str fs = "[" ^ (strlist_to_str fs) ^ "]"

      (* Checks if a string is a field in the given record *)
      fun is_field (f0 : string) : bool = List.exists (fn f1 => f0 = f1) fields
      (* Check that the footprint is a list of fields *)
      val footprint_ok = List.all is_field footprint

      (* Lookup disjoint fields -- we'll need one orthogonality lemma for each of them *)
      val disjoint_fields = List.filter (fn f0 => List.all (fn f1 => f0 <> f1) footprint) fields
      val _ = (if not footprint_ok then
         (  "Invalid footprint "
         ^ fieldlist_to_str footprint
         ^ " for record " ^ rec_name ^ " with fields "
         ^ fieldlist_to_str fields
         |> error) else ())

      (* Use the passed-in term directly - don't re-parse! 
         This preserves locale parameter applications. *)
      val p_name = p_term |> extract_const
      val (_, num_args, rec_namexs) = dest_attr_term ctxt rec_ty p_term |> Option.valOf
      (* Identifier used for the generated fact names. As on the operation path, a bare constant
         uses its base name (stable common-case names), but a PARTIAL APPLICATION must fold the
         applied argument into the name — otherwise two attributes that are different partial
         applications of one head constant (or an abbreviation aliasing another attribute) collide on
         the generated cancellation fact/list name. *)
      val p_id = locality_public_id ctxt p_term

      val _ = if not (Library.member (op =) rec_namexs rec_namex) then
        error ("Illegal argument index " ^ (rec_namex |> Int.toString) ^
               " passed to state_locality_for_attribute, valid indices are " ^
               (rec_namexs |> List.map Int.toString |> String.concatWith ", "))
        else ()
      val _ =
        assert_locality_public_id_available ctxt rec_name
          Locality_Attribute rec_namex p_id p_term

      (* Build proposition terms directly to preserve locale parameter applications.
         Keep p_term itself as the public registration pattern, but specialize a
         freshened copy of its type scheme at the selected record argument.
         Polymorphic constants parsed in a theory context contain fixed TFrees;
         applying that raw term to rec_ty-valued arguments would mix two
         independent type-variable coordinate systems. *)
      val certificate_term =
        let
          val fresh_inc = Term.maxidx_of_typ rec_ty + 1
          val term_scheme =
            p_term
            |> locality_varify_types_preserving
                 (locality_assumption_tfrees ctxt)
            |> Term.map_types (Logic.incr_tvar fresh_inc)
        in
          term_scheme
        end
      val certificate_rec_ty =
        nth (Term.binder_types (Term.type_of certificate_term)) rec_namex
      
      (* Create free variable for the record *)
      val R_var = Free ("R", certificate_rec_ty)
      
      (* Get the argument types from the specialized certificate term. *)
      val p_ty = Term.type_of certificate_term
      val arg_tys = Term.binder_types p_ty |> Library.take num_args
      val p_result_ty = Term.body_type p_ty
      
      (* Create free variables for all arguments *)
      val arg_vars = arg_tys |> Library.map_index (fn (i, ty) => 
        if i = rec_namex then R_var else Free ("arg" ^ Int.toString i, ty))
      
      (* Build the update term for a field: update_field f R 
         where f has the appropriate field update type *)
      fun mk_update_term field =
        let
            val upd_name = locality_field_update_name ctxt rec_name field
            val sel_name = locality_field_selector_name ctxt rec_name field
            val thy = Proof_Context.theory_of ctxt
            val fresh_inc = Term.maxidx_of_term certificate_term + 1
            fun read_fresh_const name =
              let
                val t = Syntax.read_term ctxt name
              in
                (extract_const t,
                 Term.type_of t
                 |> locality_varify_typ
                 |> Logic.incr_tvar fresh_inc)
              end
            val (_, sel_ty) = read_fresh_const sel_name
            val sel_match =
              Sign.typ_match thy
                (Term.domain_type sel_ty, certificate_rec_ty) Vartab.empty
              handle Type.TYPE_MATCH =>
                error ("Cannot instantiate field selector " ^ sel_name
                  ^ " from " ^ Syntax.string_of_typ ctxt sel_ty
                  ^ " at record type "
                  ^ Syntax.string_of_typ ctxt certificate_rec_ty
                  ^ "\nInternal selector type: " ^ ML_Syntax.print_typ sel_ty
                  ^ "\nInternal record type: "
                  ^ ML_Syntax.print_typ certificate_rec_ty)
            val field_ty =
              Envir.subst_type sel_match (Term.range_type sel_ty)
            val (upd_const_name, upd_ty) = read_fresh_const upd_name
            val upd_arg_tys = Term.binder_types upd_ty
            val upd_field_fun_ty = nth upd_arg_tys 0
            val upd_record_input_ty = nth upd_arg_tys 1
            (* Constrain the updated field and the input record, but leave type
               parameters occurring only in the output record schematic. A
               datatype-record updater may change such phantom parameters even
               when the field update itself is endomorphic. *)
            val upd_input_match =
              Sign.typ_match thy
                (upd_record_input_ty, certificate_rec_ty) Vartab.empty
              handle Type.TYPE_MATCH =>
                error ("Cannot instantiate field updater " ^ upd_name
                  ^ " input from " ^ Syntax.string_of_typ ctxt upd_ty
                  ^ " at record type "
                  ^ Syntax.string_of_typ ctxt certificate_rec_ty
                  ^ "\nInternal updater type: " ^ ML_Syntax.print_typ upd_ty
                  ^ "\nInternal record type: "
                  ^ ML_Syntax.print_typ certificate_rec_ty)
            val upd_match =
              Sign.typ_match thy
                (upd_field_fun_ty, field_ty --> field_ty) upd_input_match
              handle Type.TYPE_MATCH =>
                error ("Cannot instantiate field updater " ^ upd_name
                  ^ " function from " ^ Syntax.string_of_typ ctxt upd_ty
                  ^ " at field type " ^ Syntax.string_of_typ ctxt field_ty
                  ^ "\nInternal updater type: " ^ ML_Syntax.print_typ upd_ty
                  ^ "\nInternal field type: " ^ ML_Syntax.print_typ field_ty)
            val upd_const =
              Const (upd_const_name, Envir.subst_type upd_match upd_ty)
            val f_var = Free ("f", field_ty --> field_ty)
        in (f_var, upd_const $ f_var $ R_var) end
      
      (* Apply the certificate term to arguments, substituting rec_arg for the
         record position. Freshen and specialize the attribute separately for
         each side: the updater output may differ from its input only in
         phantom record parameters, while all non-record arguments and the
         result type remain shared by the equality. *)
      fun apply_p_term_to rec_arg =
        let
          val thy = Proof_Context.theory_of ctxt
          val target_arg_tys =
            arg_vars |> map_index (fn (i, v) =>
              if i = rec_namex then Term.type_of rec_arg else Term.type_of v)
          val target_ty =
            fold_rev (fn arg_ty => fn result_ty => arg_ty --> result_ty)
              target_arg_tys p_result_ty
          val target_maxidx =
            fold (fn T => fn i => Int.max (Term.maxidx_of_typ T, i))
              (target_ty :: map Term.type_of arg_vars) ~1
          val term_scheme =
            certificate_term
            |> Term.map_types (Logic.incr_tvar (target_maxidx + 1))
          val tyenv =
            Sign.typ_match thy
              (Term.type_of term_scheme, target_ty) Vartab.empty
            handle Type.TYPE_MATCH =>
              error ("Cannot specialize attribute "
                ^ Syntax.string_of_term ctxt p_term
                ^ " at record type "
                ^ Syntax.string_of_typ ctxt (Term.type_of rec_arg))
          val specialized_term = Envir.subst_term_types tyenv term_scheme
          val args = arg_vars |> map_index (fn (i, v) =>
            if i = rec_namex then rec_arg else v)
        in
          Term.list_comb (specialized_term, args)
        end
      
      (* Build commutativity statement: \<And>f R args. p_term (update f R) args = p_term R args *)
      fun mk_commutativity_stm field =
        let val (f_var, update_term) = mk_update_term field
            val lhs = apply_p_term_to update_term
            val rhs = apply_p_term_to R_var
            val eq = HOLogic.mk_eq (lhs, rhs)
            val prop = HOLogic.mk_Trueprop eq
            (* Quantify over f, R, and all other argument variables *)
            val other_args = arg_vars |> List.filter (fn v => v <> R_var)
        in fold_rev Logic.all (other_args @ [R_var, f_var]) prop end
      
      val commutativity_stms = List.map mk_commutativity_stm disjoint_fields

      fun after_qed (named_thm_list_opt) name (cont : Proof.context -> Proof.context) thms ctxt =
        let val thms = thms |> flat
          val attribs = unpack_attributes_default ctxt rec_name attribs_opt
           |> List.map (Attrib.check_src ctxt)
          val default_attribs = not (Option.isSome attribs_opt)
          val public_attribs = if default_attribs then attribs else []
        in ctxt
           |> (case named_thm_list_opt of
               SOME n => fold (fn t => Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none} (Named_Theorems.add_thm n t |> K)) thms
             | NONE => I)
           |> Local_Theory.note
                (((Binding.name name), public_attribs), thms) |> snd
           |> (if default_attribs then I
               else Local_Theory.note ((Binding.empty,attribs), thms) #> snd)
           |> cont
        end

      \<comment>\<open>As for operations, the cancellation lemmas remain interactive, so the user can supply a
         manual proof. The automatic attempt is the old method-string \<^verbatim>\<open>auto simp add: Let_def
         <defs> <_locality_facts>\<close>: handing the rules to \<^verbatim>\<open>auto\<close> by name lets the simplifier reuse the
         ambient indexed simpset, whereas the WIP rewrite's ML-built simpset paid for ambient
         construction eagerly per-call.\<close>
      val helper_plan =
        locality_body_helper_plan ctxt rec_name p_name
      val helper_certificates = #certificates helper_plan

      (* As on the operation path: unfold the attribute and helpers whose actual applications have
         no matching registration, so case/let/delegation attribute bodies normalise. *)
      val attr_discharge_cnames =
        (p_name :: #unfold helper_plan)
        |> distinct (op =)
      val default_simps =
        let val const_unfold =
              attr_discharge_cnames |> map_filter (locality_def_fact_name ctxt)
            val helper_facts =
              if null helper_certificates then []
              else [locality_body_helper_certificate_fact]
            val locality_facts = if Option.isSome attribs_opt then [] else [default_named_theorems_for_record rec_name]
            val all_simps =
              ["Let_def"] @ const_unfold @ helper_facts @ locality_facts
        in
          String.concatWith " " all_simps
        end
      val default_splits = String.concatWith " " (locality_body_case_split_names ctxt attr_discharge_cnames)

      val cancellation_thm_name = register_locality_attr_cancellation_thm_name rec_name p_id rec_namex
      val cancellation_thms_name = register_locality_attr_cancellation_thm_list_name rec_name p_id rec_namex
      val flexible_prefix = locality_pattern_flexible_prefix p_term
      val replay =
        locality_registration_is_replay ctxt rec_name p_name p_term
          flexible_prefix Locality_Attribute
          footprint num_args rec_namex false
          (length disjoint_fields) 0 false

       fun wrapup ctxt =
         let
           val entry : locality_entry =
             make_locality_entry rec_name Locality_Attribute
               p_name p_term flexible_prefix footprint num_args rec_namex
               false (Proof_Context.get_thms ctxt cancellation_thm_name)
               [] NONE
         in
           add_record_locality_entry ctxt rec_name entry ctxt
         end
    in
      if replay then
        locality_registration_replay_proof ctxt
      else
        let
          val (_, _, ctxt0) =
            check_create_named_theorems
              (default_named_theorems_for_record rec_name) ctxt
          val (cancellation_thms_name, ctxt') =
            ctxt0
            |> Named_Theorems.declare
                (Binding.make (cancellation_thms_name, \<^here>)) ""
          fun start_core_proof ctxt cont =
            let
              val method_ctxt =
                locality_body_helper_method_context
                  ctxt helper_certificates
            in
              ctxt
              |> Proof.theorem NONE
                   (after_qed (SOME cancellation_thms_name)
                     cancellation_thm_name cont)
                   [map (fn t => (t, [])) commutativity_stms]
              |> apply_method (SIMPLE_METHOD all_tac)
              |> (if with_proof then
                   apply_txt method_ctxt
                     ("(auto simp add: " ^ default_simps
                       ^ " split: " ^ default_splits ^ ")?")
                 else
                   I)
            end
        in
          start_core_proof ctxt' wrapup
        end
    end

  fun register_locality_field (rec_name: string) (field: string, update: string)
        (ctxt: Proof.context) =
    let 
      val count = locality_direct_counter ctxt
      val _ = locality_count_int count
        AutoLocality_Instrumentation.Lifecycle_Registration_Attempts
        (fn () => 2)
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val field_short = field |> Long_Name.base_name
      val _ = locality_pretty_trace ctxt 1 (fn () =>
        Pretty.text ("Registering locality data for field " ^ field_short
        ^ " (full name: " ^ field
        ^ ") on record") @ [Pretty.brk 1, Syntax.pretty_typ ctxt rec_ty]
        |> Pretty.block)
      val field_entry : locality_entry =
        make_locality_entry rec_name Locality_Attribute
          field (Syntax.read_term ctxt field) [] [field_short]
          1 0 true [] [] NONE
      val update_entry : locality_entry =
        make_locality_entry rec_name Locality_Operation
          update (Syntax.read_term ctxt update) [] [field_short]
          2 1 true [] [] NONE
    in
       ctxt
       |> add_record_locality_entry ctxt rec_name field_entry
       |> add_record_locality_entry ctxt rec_name update_entry
    end

  fun locality_init_for (rec_name : string) (log: bool) (ctxt : Proof.context) : Proof.context = 
    let val (_, rec_name) = prepare_rec_name ctxt rec_name
    in
    if has_record_locality_data_for_record rec_name ctxt then 
       ((if log then
          locality_pretty_trace ctxt 1 (fn () =>
            Pretty.text ("Record " ^ rec_name ^ " already initialized")
            |> Pretty.block)
       else ());
       ctxt)
    else let 
       val _ = locality_pretty_trace ctxt 1 (fn () =>
         Pretty.text ("Initializing locality data for record " ^ rec_name)
         |> Pretty.block)
       val fields = get_fields_full rec_name ctxt 
           |> List.map (Syntax.read_input #> Input.string_of)
           |> List.map (Syntax.parse_term ctxt) |> List.map extract_const

       val field_updates_full = get_field_updates_full rec_name ctxt
       \<comment>\<open>Always declare the record's \<^verbatim>\<open>_locality_facts\<close> named-theorems bundle, even though we are not
          populating it eagerly. Downstream theories reference the name (e.g. \<^verbatim>\<open>simp add: \<dots>_locality_facts\<close>),
          so the bundle must exist after \<^verbatim>\<open>locality_init\<close>; the bundle is then filled by subsequent
          \<^verbatim>\<open>locality_lemma\<close> commands.\<close>
       val (_, _, ctxt) = check_create_named_theorems (default_named_theorems_for_record rec_name) ctxt
    in
       ctxt |> fold (register_locality_field rec_name) (fields ~~ field_updates_full)
    end end

  val record_init_argparse = ((Args.$$$ "for") |-- Parse.typ)

  val _ = Outer_Syntax.local_theory @{command_keyword "locality_init"}
          "prove locality lemma for operations and attributes on records"
             (record_init_argparse >> (fn rec_name =>
                locality_init_for rec_name true
            ))            

  fun state_locality attribs_opt (rec_name : string) (p_name: string) (footprint: string list)
      (with_proof : bool) (match_idx : int) (ctxt : Proof.context)  =
    let
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val p_term = Syntax.read_term ctxt p_name
      (* Dispatch on the type of the (possibly partially applied) term. For an operation we forward
         the ORIGINAL term string 'p_name' — NOT the bare head constant — so that a partial
         application like 'w_apply_policy policy_a' keeps its baked
         argument; stripping to the head const here is what made the generated statement abstract the
         argument into a fresh variable and become unprovable. The attribute branch already forwards
         the full 'p_term'. *)
      val p_ty = Term.type_of p_term
      val ctxt = locality_init_for rec_name false ctxt
    in
      if is_fun_ty_on rec_ty p_ty then
         state_locality_for_op attribs_opt rec_name p_name footprint with_proof ctxt
      else
        case dest_attr_term ctxt rec_ty p_term of
          NONE => [Pretty.str "Term", Syntax.pretty_term ctxt p_term, Pretty.brk 1]
                  @ Pretty.text "is neither a function nor an attribute on"
                  @ [Pretty.brk 1, Syntax.pretty_typ ctxt rec_ty]
                  |> Pretty.block |> Pretty.string_of |> Exn.error
        | SOME (_, _, idxs) =>
            (locality_pretty_trace ctxt 1 (fn () =>
               [Pretty.str "Indices:",
                Pretty.list "[" "]" (List.map (Int.toString #> Pretty.str) idxs),
                Pretty.str "Index", Pretty.str (match_idx |> Int.toString)]
               |> Pretty.breaks |> Pretty.block);
             state_locality_for_attribute attribs_opt rec_name p_term footprint with_proof
               (nth idxs match_idx) ctxt)
    end

  val record_local_op_argparse =
         ((Args.$$$ "for") |-- Parse.typ)
      -- Scan.optional (Args.parens (Args.$$$ "no_proof") >> K true) false
      -- (Scan.optional (Parse.attribs >> SOME) NONE)
      --| Args.colon
      -- Parse.term
      -- (Scan.optional ( Args.bracks Parse.int) 0)
      -- (Args.$$$ "footprint" |-- (Args.bracks (Parse.list Parse.short_ident)))

  val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "locality_lemma"}
          "prove locality lemma for operations and attributes on records"
             (record_local_op_argparse >>
                (fn (((((rec_name, no_proof), attribs_opt), p_name), match_idx), field_list) =>
                   state_locality attribs_opt rec_name p_name field_list (not no_proof) match_idx))

  val locality_check_argparse =
    Scan.optional (((Args.$$$ "for") |-- Parse.typ) >> SOME) NONE

  fun list_operations_on_record (rec_ty : typ) (ctxt : Proof.context) =
    let
      fun is_operation_on_record (_, (c_ty, _)) = is_fun_ty_on rec_ty c_ty
      fun is_record_update (c, _) = c |> Long_Name.base_name |> String.isPrefix "update"
    in ctxt
      |> Proof_Context.consts_of |> Consts.dest |> #constants
      |> Library.sort (fn ((c0, _), (c1, _)) => string_ord (c0, c1))
      |> List.filter is_operation_on_record
      |> List.filter (not o is_record_update)
    end

  fun list_attributes_on_record (rec_ty : typ) (ctxt : Proof.context) =
    let
      fun is_attribute_on_record (_, (c_ty, _)) = is_attr_ty_on rec_ty c_ty
    in ctxt
      |> Proof_Context.consts_of |> Consts.dest |> #constants
      |> Library.sort (fn ((c0, _), (c1, _)) => string_ord (c0, c1))
      |> List.filter is_attribute_on_record
    end

  (* Looks up constants involving a given record and checking if they have a locality relation
     a registered for them. *)
  fun locality_check_core (rec_name : string) (ctxt : Proof.context) =
    let
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      fun has_info (c, _) =
        has_record_locality_entry_generic rec_name c (Context.Proof ctxt)
      val special_attributes =
        (* Field projections *)
        get_fields rec_name ctxt
        (* Various standard built-in attributes *)
        @ List.map (fn t => t ^ "_" ^ (rec_name |> Long_Name.base_name))
          [ "Rep", "case", "ctor_fold", "ctor_rec",
            "dtor", "rec", "size", "term_of"]
      fun is_builtin_attr (c, _) =
        Library.member (op =) special_attributes (Long_Name.base_name c)
      fun is_builtin_op (c, _) =
        Library.member (op =) (get_field_updates_full rec_name ctxt) c
      val ops = list_operations_on_record rec_ty ctxt
        |> List.filter (not o is_builtin_op)
      val attrs = list_attributes_on_record rec_ty ctxt
        |> List.filter (not o is_builtin_attr)
      val ops_without_info = ops
        |> List.filter (not o has_info)
      val attrs_without_info = attrs
        |> List.filter (not o has_info)
      fun pretty_info (e as (c, _)) =
        [Syntax.pretty_term ctxt (Syntax.parse_term ctxt c), Pretty.str ":", Pretty.brk 1,
         if has_info e then Pretty.str "\<checkmark>" else Pretty.str "\<crossmark>"]
        |> Pretty.block
      fun pretty_warning (c, _) =
        [Pretty.text "On record"
         @ [Pretty.brk 1, Syntax.pretty_typ ctxt rec_ty]
         @ Pretty.text "," @ [Pretty.brk 1,
         Syntax.pretty_term ctxt (Syntax.parse_term ctxt c), Pretty.brk 1]
         @ Pretty.text "does not have a footprint registered." |> Pretty.block] |> Pretty.chunks
      val _ = List.map pretty_warning (ops_without_info @ attrs_without_info)
        |> Pretty.chunks |> Pretty.string_of |> warning
      val _ = Pretty.text "Operations and attributes on"
       @ [Pretty.brk 1, Syntax.pretty_typ ctxt rec_ty, Pretty.brk 1,
          List.map pretty_info (ops @ attrs) |> Pretty.list "{" "}"]
        |> Pretty.block |> Pretty.writeln
    in
      ctxt
    end

  fun locality_check (rec_name_opt : string option) (ctxt : Proof.context)  =
    case rec_name_opt of
        SOME rec_name => locality_check_core rec_name ctxt
      | NONE => (* Update all records for which at least one constant is registered *)
         let val records = get_registered_records ctxt in
           fold locality_check_core records ctxt
         end

  val _ = Outer_Syntax.local_theory @{command_keyword "locality_check"}
          "autoderive locality lemmas for constants previously registered via locality_lemma"
             (locality_check_argparse >> locality_check)

  val print_locality_data_argsparse =
      Scan.optional ((Args.$$$ "for") |-- Parse.typ >> SOME) NONE

  val _ = Outer_Syntax.local_theory @{command_keyword "print_locality_data"}
          "print all locality data previously registerd via locality_lemma"
             (print_locality_data_argsparse >> print_locality_data)

  fun locality_named_dispatchers ctxt =
    let
      fun resolve key name =
        (name, Simplifier.the_simproc ctxt name
          handle ERROR msg =>
            error ("Missing local AutoLocality named simproc "
              ^ quote name ^ " for "
              ^ describe_locality_dispatch_key key ^ ":\n" ^ msg))
      fun resolve_entry
            (key, entry : locality_dispatcher_inventory_entry) =
        let
          val alias = #alias entry
          val (_, simproc) = resolve key alias
        in
          (key, #source_name entry, alias, simproc)
        end
    in
      LocalityDispatcherInventory.get (Context.Proof ctxt)
      |> LocalityDispatchKeyTable.dest
      |> map resolve_entry
    end

  fun locality_present_raw_dispatchers ctxt named_dispatchers =
    let
      fun add_expected (key, source_name, _, _) expected =
        Symtab.map_default (source_name, key)
          (fn key' =>
            if locality_dispatch_key_eq (key, key') then key'
            else
              error ("AutoLocality source dispatcher name "
                ^ quote source_name ^ " identifies both "
                ^ describe_locality_dispatch_key key
                ^ " and "
                ^ describe_locality_dispatch_key key'))
          expected
      val expected =
        fold add_expected named_dispatchers Symtab.empty
      val raw_dispatchers =
        Raw_Simplifier.simpset_of ctxt
        |> Raw_Simplifier.dest_ss
        |> #simprocs
      fun observe (source_name, lhss) present =
        (case Symtab.lookup expected source_name of
           NONE => present
         | SOME dispatch_key =>
             (case lhss of
                [lhs] =>
                  if locality_dispatch_key_eq
                       (locality_dispatch_key_of_trigger lhs,
                        dispatch_key)
                  then
                    Symtab.map_default (source_name, 0)
                      (fn count => count + 1) present
                  else
                    error ("Local AutoLocality dispatcher "
                      ^ quote source_name
                      ^ " has the wrong trigger family for "
                      ^ describe_locality_dispatch_key dispatch_key)
              | _ =>
                  error ("Local AutoLocality dispatcher "
                    ^ quote source_name
                    ^ " does not have exactly one trigger")))
      val present =
        fold observe raw_dispatchers Symtab.empty
      val _ =
        Symtab.dest present
        |> List.app (fn (source_name, count) =>
             if count = 1 then ()
             else
               error ("Expected one local AutoLocality dispatcher "
                 ^ quote source_name ^ ", found "
                 ^ Int.toString count))
    in
      present
    end

  fun locality_cancellation_attribute enabled : attribute =
    Thm.declaration_attribute (fn _ => fn context =>
      let
        val ctxt = Context.proof_of context
        val add_dispatchers =
          if enabled then
            let
              val named_dispatchers =
                locality_named_dispatchers ctxt
              val present =
                locality_present_raw_dispatchers
                  ctxt named_dispatchers
              val missing =
                named_dispatchers
                |> filter_out (fn (_, source_name, _, _) =>
                     Symtab.defined present source_name)
              fun add_missing (_, _, _, simproc) =
                Raw_Simplifier.add_proc simproc
            in
              Raw_Simplifier.map_ss
                (fold add_missing missing)
            end
          else I
      in
        context
        |> Config.put_generic locality_cancel_enabled enabled
        |> add_dispatchers
      end)\<close>

attribute_setup locality_cancel =
  \<open>Scan.succeed (locality_cancellation_attribute true)\<close>
attribute_setup locality_no_cancel =
  \<open>Scan.succeed (locality_cancellation_attribute false)\<close>

text\<open>On-demand pairwise operation commutativity. The default-on cancellation simprocs only fire when
an \<^emph>\<open>attribute\<close> heads the telescope; a bare \<^verbatim>\<open>opA (opB R)\<close> is not rewritten. Where a proof needs the
two operations to commute, \<^verbatim>\<open>[[locality_autocommutativity A B]]\<close> derives that theorem from the
footprint data and \<^emph>\<open>returns it as a fact\<close> (generalized to schematics, so it applies as a rewrite or
rule) - nothing is registered permanently and the ambient simpset is not touched. It is used in a
\<^emph>\<open>fact position\<close>: name it with \<^verbatim>\<open>lemmas c = [[locality_autocommutativity A B]]\<close>, discharge a bare
op-over-op goal with \<^verbatim>\<open>by (rule [[locality_autocommutativity A B]])\<close>, or feed it to a tactic
with \<^verbatim>\<open>by (simp add: [[locality_autocommutativity A B]])\<close>. It is sound: operations with disjoint
footprints commute and yield a theorem; a footprint-sharing pair genuinely does not commute and
raises an error rather than fabricating a false theorem. The record type is normally inferred by
intersecting the records carrying matching registrations for both operations. The existing
\<^verbatim>\<open>(rec)\<close> prefix remains available when polymorphic constants make that intersection ambiguous.

Because the attribute ignores the theorem it is applied to and synthesises a fresh one, it works
from the empty \<^verbatim>\<open>[[\<dots>]]\<close> fact form (which seeds the attribute chain with \<^verbatim>\<open>Drule.dummy_thm\<close>): the
\<^verbatim>\<open>Thm.rule_attribute\<close> guard only short-circuits on a \<^emph>\<open>free\<close> dummy, whereas that seed is untagged, so
the rule function runs and its result becomes the fact. The generalization to schematics (via
\<^verbatim>\<open>forall_intr_frees\<close>/\<^verbatim>\<open>forall_elim_vars\<close>) is what makes the returned theorem \<^emph>\<open>storable\<close> as a named fact
and usable as a rewrite - a \<^verbatim>\<open>Goal.prove\<close> result quantifies over fixed frees, which \<^verbatim>\<open>lemmas\<close> would
reject.

The two operation arguments are parsed with \<^ML>\<open>Args.const\<close> (not \<^ML>\<open>Args.name\<close>), so the source
tokens \<^verbatim>\<open>A\<close>/\<^verbatim>\<open>B\<close> carry the usual constant PIDE markup - hover shows the type, ctrl-click jumps to the
definition - and misspelled operands are rejected at parse time. \<^ML>\<open>Args.const\<close> already resolves to
the fully-qualified constant name the footprint database is keyed under, so it is passed straight to
\<^verbatim>\<open>locality_prove_commutativity\<close>.\<close>
attribute_setup locality_autocommutativity =
  \<open>(Scan.option (Scan.lift (Args.parens Parse.typ))
     -- Args.const {proper = false, strict = false}
     -- Args.const {proper = false, strict = false}) >> (fn ((rc, a), b) =>
     Thm.rule_attribute [] (fn context => fn _ (* incoming (dummy) thm, discarded *) =>
       let
         val ctxt = Context.proof_of context
         val patternA = Syntax.read_term ctxt a
         val patternB = Syntax.read_term ctxt b
         val rc =
           (case rc of
              SOME rec_name => rec_name
            | NONE =>
                locality_infer_commutativity_record
                  ctxt patternA patternB)
       in
         case locality_prove_commutativity ctxt rc patternA patternB of
           SOME thm => Thm.forall_intr_frees thm |> Thm.forall_elim_vars 0
         | NONE => error ("locality_autocommutativity: " ^ a ^ " and " ^ b
                          ^ " do not commute on " ^ rc)
       end))\<close>
  "derive and return (generalized) the pairwise op-commutativity theorem for the named record"

text\<open>For restricted simplifier calls such as \<^verbatim>\<open>simp only\<close>, the default cancellation
simprocs are intentionally absent. The fact attribute
\<^verbatim>\<open>[[locality_autocancellation operation attribute index]]\<close> derives exactly the requested
operation/attribute projection equation on demand. The index is relative to the remaining
attribute arguments after any prefix already supplied by the proof context. In particular,
implicit locale parameters do not count. The index distinguishes registrations of one attribute
at multiple record slots. As with \<^verbatim>\<open>locality_autocommutativity\<close>, no theorem is
registered permanently. The record is normally inferred by intersecting the operation and indexed
attribute registrations. The existing \<^verbatim>\<open>(rec)\<close> prefix disambiguates polymorphic constants
registered for multiple records.\<close>
attribute_setup locality_autocancellation =
  \<open>(Scan.option (Scan.lift (Args.parens Parse.typ))
     -- Args.const {proper = false, strict = false}
     -- Args.const {proper = false, strict = false} -- Scan.lift Parse.nat)
    >> (fn (((rc, operation), attribute), attribute_idx) =>
      Thm.rule_attribute [] (fn context => fn _ =>
        let
          val ctxt = Context.proof_of context
          val operation_pattern = Syntax.read_term ctxt operation
          val attribute_pattern = Syntax.read_term ctxt attribute
          val rc =
            (case rc of
               SOME rec_name => rec_name
             | NONE =>
                 locality_infer_cancellation_record ctxt
                   operation_pattern attribute_pattern
                   attribute_idx)
        in
          case locality_prove_cancellation_fact ctxt rc
                 operation_pattern attribute_pattern attribute_idx of
            SOME thm => Thm.forall_intr_frees thm |> Thm.forall_elim_vars 0
          | NONE =>
              error ("locality_autocancellation: " ^ operation ^ " does not cancel from "
                ^ attribute ^ " at relative record argument " ^ Int.toString attribute_idx
                ^ " on " ^ rc)
        end))\<close>
  "derive and return one generalized operation/attribute cancellation theorem"

end
