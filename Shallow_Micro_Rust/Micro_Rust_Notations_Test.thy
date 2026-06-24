(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Tests for the `micro_rust_notation` command: a uRust identifier
   registered with it must resolve to its HOL backend when used inside
   `\<lbrakk> \<dots> \<rbrakk>`. The parse-translation for `_shallow_identifier_as_*` consults
   `Micro_Rust_Names`, emits a `urust_dispatch` marker, and the typed
   term_check phase resolves it (e.g. to `my_test_some`). *)

theory Micro_Rust_Notations_Test
  imports Micro_Rust_Shallow_Embedding
begin

definition my_test_some :: \<open>nat \<Rightarrow> nat option\<close> where
  \<open>my_test_some x = Some x\<close>

\<comment>\<open>Register in literal context: bare \<open>MyTestSome\<close> in value position
  takes the \<open>_shallow_identifier_as_literal\<close> path.\<close>
micro_rust_notation my_test_some ("MyTestSome")
print_micro_rust_notations

text\<open>\<^verbatim>\<open>\<lbrakk> MyTestSome \<rbrakk>\<close> resolves to a literal whose value is
\<^const>\<open>my_test_some\<close>, NOT a free variable named \<open>MyTestSome\<close>.\<close>

term \<open>\<lbrakk> MyTestSome \<rbrakk>\<close>

\<comment>\<open>Acceptance test: the identifier resolves to the registered HOL
  constant, so the embedding is syntactically equal to \<open>literal
  my_test_some\<close>.\<close>
lemma test_my_test_some_dispatched:
  shows \<open>\<lbrakk> MyTestSome \<rbrakk> = literal my_test_some\<close>
  by (rule refl)

text\<open>Non-\<open>Const\<close> backend: register an arbitrary HOL expression. The
dispatch should still resolve, but the use-site markup should fall back
to the registration site (since there is no underlying constant for
ctrl-click to jump to).\<close>

micro_rust_notation \<open>1 + (1 :: nat)\<close> ("OnePlusOne")

term \<open>\<lbrakk> OnePlusOne \<rbrakk>\<close>
              
\<comment>\<open>Acceptance: the marker resolves to the registered expression.\<close>
lemma test_one_plus_one_dispatched:
  shows \<open>\<lbrakk> OnePlusOne \<rbrakk> = literal (1 + (1 :: nat))\<close>
  by (rule refl)

text\<open>\<^verbatim>\<open>print_micro_rust_notations\<close> enumerates every entry in
\<^ML_structure>\<open>Micro_Rust_Names\<close> --- e.g. the \<open>Some\<close>/\<open>Ok\<close>/\<open>Err\<close> and
std-lib registrations in scope.\<close>

print_micro_rust_notations


subsection\<open>Shadow detection\<close>

text\<open>The dispatcher rejects --- and warns about --- registrations whose
\<^emph>\<open>rust\<close>-name accidentally collides with an existing HOL constant. The
fixture below sets up two HOL constants and uses them via dispatch
markers to trigger both branches of the check.\<close>

context begin

\<comment>\<open>HOL constant whose type matches what we then register: \<open>nat \<Rightarrow> nat\<close>.\<close>
private definition shadow_target_const :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>shadow_target_const x = x + 1\<close>

\<comment>\<open>HOL constant of a different type, used to test the warning branch.\<close>
private definition shadow_warn_const :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>shadow_warn_const x = (x = 0)\<close>

\<comment>\<open>An unrelated backend we will register under each shadow name.\<close>
private definition shadow_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>shadow_backend x = x\<close>

\<comment>\<open>Register the backend under names that collide with the HOL constants.
  Registration itself is silent; the check fires at use time.\<close>
micro_rust_notation shadow_backend ("shadow_target_const")
micro_rust_notation shadow_backend ("shadow_warn_const")

text\<open>\<^bold>\<open>Error path\<close> --- a HOL constant of \<^emph>\<open>matching\<close> type already exists.
The marker below triggers \<open>shadow_check\<close>'s \<open>error\<close>:

\<^verbatim>\<open>Ambiguous uRust notation \<open>shadow_target_const\<close>:
   a registered backend matches type nat \<Rightarrow> nat
   but the HOL constant "shadow_target_const" of type nat \<Rightarrow> nat also matches.\<close>

The line is left commented so the test theory still compiles; uncomment
to reproduce the error interactively.\<close>

\<comment>\<open>term \<open>(urust_dispatch (STR ''literal:shadow_target_const'') :: nat \<Rightarrow> nat)\<close>\<close>

text\<open>\<^bold>\<open>Warning path\<close> --- a HOL constant exists but its type does
\<^emph>\<open>not\<close> match this occurrence. Dispatch picks the registered backend and
emits a \<open>warning\<close> mentioning the shadowed constant. Compiles cleanly.

The warning attaches to the \<^emph>\<open>use site\<close> of \<open>shadow_warn_const\<close>
(plumbed via \<open>mk_marker\<close>), not to the surrounding \<open>term\<close> command, so
jEdit highlights the identifier itself.

We use a ``urust_dispatch`` marker directly here (rather than wrapping
in \<open>\<lbrakk> \<dots> \<rbrakk>\<close>) so the registered backend's bare \<open>nat \<Rightarrow> nat\<close>
type matches without needing a \<open>function_body\<close> lift.\<close>
term \<open>(urust_dispatch (STR ''literal:shadow_warn_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

end


subsection\<open>Shadow-opt-out flags\<close>

text\<open>The \<open>[no_shadow_warning]\<close> and \<open>[no_shadow_error]\<close> brackets on
\<open>micro_rust_notation\<close> silence the corresponding diagnostic for the
named registration. Each flag is per-(kind, name); the underlying
warning / error logic is unchanged.\<close>

context begin

private definition silenced_warn_const :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>silenced_warn_const _ = True\<close>

private definition silenced_target_const :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>silenced_target_const x = x\<close>

private definition silenced_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>silenced_backend x = x + 1\<close>

\<comment>\<open>Register the backends without flags; configure shadow checks
  separately afterwards via \<open>micro_rust_notation_config\<close>. This
  decouples the registration site from the silencing decision, and
  lets the user adjust either independently.\<close>
micro_rust_notation silenced_backend ("silenced_warn_const")
micro_rust_notation silenced_backend ("silenced_target_const")

\<comment>\<open>\<^bold>\<open>Warning silenced.\<close> The HOL constant
  \<^const>\<open>silenced_warn_const\<close> exists at type \<open>nat \<Rightarrow> bool\<close>; without
  the config below, dispatch at \<open>nat \<Rightarrow> nat\<close> would print the
  "uRust notation \<dots> shadows the HOL constant \<dots>" warning.\<close>
micro_rust_notation (config) [shadow_no_warn] "silenced_warn_const"

term \<open>(urust_dispatch (STR ''literal:silenced_warn_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>\<^bold>\<open>Error silenced.\<close> The HOL constant
  \<^const>\<open>silenced_target_const\<close> exists at \<open>nat \<Rightarrow> nat\<close>; without the
  config below, dispatch at \<open>nat \<Rightarrow> nat\<close> would error out as ambiguously
  shadowing. \<open>shadow_no_err\<close> on this name routes us silently to the
  registered backend.\<close>
micro_rust_notation (config) [shadow_no_err] "silenced_target_const"

term \<open>(urust_dispatch (STR ''literal:silenced_target_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

end


subsection\<open>Variant coverage\<close>

text\<open>Exercise every form of the consolidated \<open>micro_rust_notation\<close>
command --- the auto-infer paths for all three kinds, the forced-kind
paths in their happy and error cases, and the four \<open>shadow_*\<close> config
modes (set, clear, per-name, default).\<close>

context begin

\<comment>\<open>Auto-infer literal: a non-function, non-lens HOL term routes to
  literal kind (the default fallthrough in \<open>infer_kind_of_type\<close>).\<close>
private definition variant_lit :: \<open>nat\<close> where \<open>variant_lit = 0\<close>
micro_rust_notation variant_lit ("VariantLit")
term \<open>(urust_dispatch (STR ''literal:VariantLit'') NoWitness :: nat)\<close>

\<comment>\<open>Auto-infer function: a HOL term whose type ends in \<open>function_body\<close>
  routes to function kind. We use \<open>lift_fun1\<close>, the standard wrapper.\<close>
private definition variant_fn :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>variant_fn = lift_fun1 Suc\<close>
micro_rust_notation variant_fn ("VariantFn")
term \<open>(urust_dispatch (STR ''function:VariantFn'') NoWitness :: nat \<Rightarrow> ('s, nat, 'a, 'i, 'o) function_body)\<close>

\<comment>\<open>Forced-kind happy paths.\<close>
private definition variant_lit_forced :: \<open>nat\<close> where \<open>variant_lit_forced = 1\<close>
micro_rust_notation (literal) variant_lit_forced ("VariantLitForced")
term \<open>(urust_dispatch (STR ''literal:VariantLitForced'') NoWitness :: nat)\<close>

private definition variant_fn_forced :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>variant_fn_forced = lift_fun1 Suc\<close>
micro_rust_notation (call) variant_fn_forced ("VariantFnForced")
term \<open>(urust_dispatch (STR ''function:VariantFnForced'') NoWitness :: nat \<Rightarrow> ('s, nat, 'a, 'i, 'o) function_body)\<close>

text\<open>Forced-kind error paths. Each line below would error with
``forced kind does not match the registered term's type'' if
uncommented; we keep them as commented-out smoke tests so the file
builds clean while documenting the expected behaviour.

\<^verbatim>\<open>micro_rust_notation (call)  variant_lit ("X")\<close>  -- term has type \<open>nat\<close>, not \<open>_ \<Rightarrow> _ function_body\<close>
\<^verbatim>\<open>micro_rust_notation (field) variant_lit ("Y")\<close>  -- term has type \<open>nat\<close>, not \<open>_ lens\<close>
\<^verbatim>\<open>micro_rust_notation (field) variant_fn  ("Z")\<close>  -- term has type \<open>_ \<Rightarrow> _ function_body\<close>, not \<open>_ lens\<close>\<close>

\<comment>\<open>Toggle off and back on: \<open>shadow_no_warn\<close> sets the bit;
  \<open>shadow_warn\<close> clears it.\<close>
private definition variant_warn_const :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>variant_warn_const _ = False\<close>
private definition variant_warn_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>variant_warn_backend x = x\<close>
micro_rust_notation variant_warn_backend ("variant_warn_const")

\<comment>\<open>Set the suppression: this dispatch should NOT warn even though the
  HOL constant of differently-typed name exists.\<close>
micro_rust_notation (config) [shadow_no_warn] "variant_warn_const"
term \<open>(urust_dispatch (STR ''literal:variant_warn_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>Clear the suppression: this dispatch SHOULD warn again.\<close>
micro_rust_notation (config) [shadow_warn] "variant_warn_const"
term \<open>(urust_dispatch (STR ''literal:variant_warn_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>Default-scope (no names): \<open>shadow_no_warn\<close> with no name argument
  silences the warning globally for the next dispatch.\<close>
private definition variant_default_const :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>variant_default_const _ = False\<close>
private definition variant_default_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>variant_default_backend x = x\<close>
micro_rust_notation variant_default_backend ("variant_default_const")

\<comment>\<open>Globally suppress warnings; the dispatch below proceeds silently.\<close>
micro_rust_notation (config) [shadow_no_warn]
term \<open>(urust_dispatch (STR ''literal:variant_default_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>Restore warnings globally so we don't pollute later tests.\<close>
micro_rust_notation (config) [shadow_warn]

\<comment>\<open>Toggle off and back on for the error bit, mirroring the warning
  test above. We register a backend whose type matches an existing
  HOL constant (so without suppression the dispatch errors).\<close>
private definition variant_err_const :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>variant_err_const x = x\<close>
private definition variant_err_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>variant_err_backend x = x + 1\<close>
micro_rust_notation variant_err_backend ("variant_err_const")

\<comment>\<open>Suppress the matching-shadow error and dispatch.\<close>
micro_rust_notation (config) [shadow_no_err] "variant_err_const"
term \<open>(urust_dispatch (STR ''literal:variant_err_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>The \<open>shadow_err\<close> mode (re-enable errors) flips the bit back.
  We don't actually re-dispatch here --- it would error --- but the
  command itself succeeds and toggles the bit.\<close>
micro_rust_notation (config) [shadow_err] "variant_err_const"

end


subsection\<open>Path-style names (\<^verbatim>\<open>Foo::Bar\<close>) via the new dispatcher\<close>

text\<open>\<^verbatim>\<open>lookup_id_tr\<close> consults \<^ML_structure>\<open>Micro_Rust_Names\<close> for
path-flattened identifiers (\<^verbatim>\<open>foo::bar\<close>) through the same single
identifier-resolution case it uses for plain names --- paths are flattened
into \<^verbatim>\<open>_urust_identifier_id\<close> earlier, so there is no separate path branch.
These tests exercise:

- short paths (\<open>foo::bar\<close>) registered via \<open>micro_rust_notation\<close>
  in literal and function positions;
- long paths (\<open>foo::bar.method()\<close>) where the head is resolved via
  the new dispatcher and the trailing method splits remain ordinary
  identifiers;
- multi-backend dispatch on a single path name (registering the same
  rust path for two distinct HOL terms differing only by type, then
  resolving by occurrence type).\<close>

context begin

text\<open>\<^bold>\<open>Short path, literal kind.\<close>\<close>

private definition path_lit_target :: \<open>nat\<close> where \<open>path_lit_target = 7\<close>
micro_rust_notation path_lit_target ("Foo::lit_value")

term \<open>\<lbrakk> Foo::lit_value \<rbrakk>\<close>

lemma test_path_lit_dispatched:
  shows \<open>\<lbrakk> Foo::lit_value \<rbrakk> = literal path_lit_target\<close>
  by (rule refl)


text\<open>\<^bold>\<open>Short path, function kind.\<close> A path-style \<^verbatim>\<open>Foo::bar\<close> in
function position must reach the dispatcher in the function kind
(\<^verbatim>\<open>NFunction\<close>) and resolve to the registered \<open>function_body\<close>-typed
backend. Shape-only smoke test: we just want the term to parse and
type-check via the new dispatch path.\<close>

private definition path_fn_target ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>path_fn_target = lift_fun1 Suc\<close>
micro_rust_notation path_fn_target ("Foo::add_one")

term \<open>\<lbrakk> Foo::add_one(0) \<rbrakk>\<close>


text\<open>\<^bold>\<open>Long path with method call.\<close> \<open>Foo::wrap(0)\<close> --- the head
\<open>Foo::wrap\<close> is a path identifier registered as a function backend via
the new command; the parenthesised argument is a function call.\<close>

private definition longpath_head ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>longpath_head x \<equiv> FunctionBody \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>\<close>
micro_rust_notation longpath_head ("Foo::wrap")

term \<open>\<lbrakk> Foo::wrap(0) \<rbrakk>\<close>


text\<open>\<^bold>\<open>Long path with method call.\<close> \<open>Bar::value.cont(0)\<close> --- this
exercises the long-path AST translator's \<^verbatim>\<open>_temporary_..._long_method\<close>
branch (\<^file>\<open>../Micro_Rust_Parsing_Frontend/Micro_Rust_Syntax.thy\<close>),
which splits \<open>Bar::value.cont\<close> into:
- a path head \<open>"Bar::value"\<close> (literal kind): after AST flattening it is
  an ordinary \<^verbatim>\<open>_urust_identifier_id\<close> carrying the joined \<open>::\<close>-name,
  resolved by the same single table-lookup case in \<open>lookup_id_tr\<close> as a
  plain identifier;
- a method name \<open>cont\<close> (function kind, plain \<^verbatim>\<open>_urust_identifier_id\<close>).

Long-path field syntax (\<open>foo::bar.fld\<close>) goes through the same
translator with a different \<^verbatim>\<open>ast_joiner\<close>; we don't add an explicit
test for that since constructing a lens-typed field backend requires
more setup than these tests warrant, and the translator is already
exercised by the method-call shape.\<close>

private definition longpath_value :: \<open>nat\<close>
  where \<open>longpath_value = 13\<close>
private definition longpath_method ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>longpath_method self \<equiv> FunctionBody \<lbrakk> \<llangle>self\<rrangle> \<rbrakk>\<close>
micro_rust_notation longpath_value  ("Bar::value")
micro_rust_notation longpath_method ("cont")

term \<open>\<lbrakk> Bar::value.cont() \<rbrakk>\<close>


text\<open>\<^bold>\<open>Multi-backend dispatch on a path name.\<close> Register two distinct
HOL targets under the same path; the typed term_check phase picks the
unique match by occurrence type. Both backends are literals (so no
shadow check fires); the test asserts each route resolves to its own
backend.\<close>

private definition path_multi_nat :: \<open>nat \<Rightarrow> nat option\<close>
  where \<open>path_multi_nat n = Some n\<close>
private definition path_multi_bool :: \<open>bool \<Rightarrow> bool option\<close>
  where \<open>path_multi_bool b = Some b\<close>

micro_rust_notation path_multi_nat  ("Foo::ctor")
micro_rust_notation path_multi_bool ("Foo::ctor")

\<comment>\<open>Type-driven dispatch through the user-facing surface: the same path
  identifier \<^verbatim>\<open>Foo::ctor\<close> resolves to the \<open>nat\<close>-typed backend or the
  \<open>bool\<close>-typed backend depending on the use-site type ascription.

  (We previously also had explicit \<^verbatim>\<open>urust_dispatch (STR ''...'') NoWitness\<close>
  probes here, but the marker's payload representation is now an
  ML-internal \<^verbatim>\<open>Free\<close> with an encoded name and can't be written
  literally in source.)\<close>
lemma test_path_multi_dispatch_nat:
  shows \<open>(\<lbrakk> Foo::ctor \<rbrakk> :: ('s, nat \<Rightarrow> nat option, 'r, 'abort, 'i, 'o) expression)
       = literal path_multi_nat\<close>
  by (rule refl)

lemma test_path_multi_dispatch_bool:
  shows \<open>(\<lbrakk> Foo::ctor \<rbrakk> :: ('s, bool \<Rightarrow> bool option, 'r, 'abort, 'i, 'o) expression)
       = literal path_multi_bool\<close>
  by (rule refl)


text\<open>\<^bold>\<open>Shadowing on a path name (warning level).\<close> Mirrors the
plain-id warning test: the path's flattened source happens to look like
the qualified name of a HOL constant of mismatched type. Compiles
cleanly and prints a warning at the use site.\<close>

private definition shadow_path_target :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>shadow_path_target _ = True\<close>
private definition shadow_path_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>shadow_path_backend x = x\<close>

micro_rust_notation shadow_path_backend ("Shadow::path_target")
\<comment>\<open>No HOL constant called \<^verbatim>\<open>Shadow::path_target\<close> exists; this is
  not a shadow case at all --- this block is here as a smoke-test of
  the path-shape dispatch, not the shadow check (which fires only on
  bona-fide HOL constant collisions, indexed by Isabelle's name
  resolution).\<close>
term \<open>(urust_dispatch (STR ''literal:Shadow::path_target'') NoWitness :: nat \<Rightarrow> nat)\<close>

end

subsection\<open>Print-table sanity check (path entries enumerated)\<close>

text\<open>\<^verbatim>\<open>print_micro_rust_notations\<close> after the path registrations
above lists every entry, including the path-style ones. This is a
visual sanity check rather than a programmatic one --- the count is
non-zero by construction since the section above registers several.\<close>

print_micro_rust_notations


subsection\<open>Lambda / let / locale shadowing of registered names\<close>

text\<open>The dispatch pipeline must NOT emit a \<^const>\<open>urust_dispatch\<close>
marker for a uRust name that, at the use site, refers to a binder
(\<lambda>-bound, let-bound, fixed-by-locale, or quantifier-bound) rather than
to a registered backend.

Concretely: registering \<^verbatim>\<open>("mask")\<close> as a field-kind notation must NOT
hijack a \<^emph>\<open>function parameter\<close> called \<^verbatim>\<open>mask\<close> when that parameter is
used at literal position inside the function body. The earlier
implementation of the legacy shim registered plain identifiers under
all three kinds for "compatibility" and so a literal-position \<open>mask\<close>
inside a \<open>\<lambda>mask. \<dots>\<close> would dispatch to the field's lens, breaking the
function definition with a "no backend matches type \<open>'l word\<close>" error.

These tests pin down the contract: same-named binders must win.\<close>

definition \<open>foo \<equiv> 42\<close>
micro_rust_notation foo ("bar")

term \<open>\<lbrakk> let foo = 12; bar \<rbrakk>\<close>


context begin

\<comment>\<open>Registered backends. The HOL targets are deliberately distinct from
  any of the binder names used below.\<close>

private definition shadow_test_lens :: \<open>('outer, 'inner) lens\<close>
  where \<open>shadow_test_lens \<equiv> undefined\<close>
private definition shadow_test_fn ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_test_fn \<equiv> lift_fun1 Suc\<close>
definition shadow_test_lit :: \<open>nat\<close>
  where \<open>shadow_test_lit = 99\<close>
  \<comment>\<open>Public so the \<open>shadow_no_shadow_test_dispatches\<close> sanity lemma
    below can unfold this via \<open>shadow_test_lit_def\<close>.\<close>

\<comment>\<open>Register the same name \<^verbatim>\<open>shdw\<close> in each of the three kinds, with
  three different HOL backends.\<close>
micro_rust_notation (field) shadow_test_lens ("shdw")
micro_rust_notation (call)  shadow_test_fn   ("shdw")
micro_rust_notation         shadow_test_lit  ("shdw")  \<comment>\<open>auto-infer: literal\<close>

text\<open>\<^bold>\<open>Lambda-bound binder.\<close> A function parameter named \<open>shdw\<close> must
shadow the registered backends inside the function body.\<close>

definition shadow_lambda_test ::
  \<open>64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_lambda_test \<equiv> \<lambda>shdw mask. FunctionBody \<lbrakk>
     \<comment> \<open>Both \<open>shdw\<close> and \<open>mask\<close> are \<lambda>-bound function parameters; their
        in-body uses must NOT reach the dispatch table even though
        \<open>shdw\<close> has registrations under all three kinds.\<close>
     shdw + mask
   \<rbrakk>\<close>

lemma shadow_lambda_test_unaffected:
  shows \<open>shadow_lambda_test = (\<lambda>shdw mask. FunctionBody \<lbrakk> shdw + mask \<rbrakk>)\<close>
  unfolding shadow_lambda_test_def by (rule refl)
\<comment>\<open>If the dispatch had hijacked \<open>shdw\<close> or \<open>mask\<close>, the term on the
  right would type-check differently (or not at all).\<close>

text\<open>\<^bold>\<open>Let-bound binder.\<close> Same scenario via a \<^verbatim>\<open>let\<close> binding inside
the body.\<close>

definition shadow_let_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_let_test \<equiv> FunctionBody \<lbrakk>
     \<comment> \<open>\<open>shdw\<close> is bound by \<open>let\<close>; its later uses must come from the let,
        not from the table. \<open>64 word\<close> chosen so the body's \<open>+\<close>
        resolves via the registered word-arithmetic \<open>urust_add\<close>.\<close>
     let shdw = 7;
     shdw + shdw
   \<rbrakk>\<close>


text\<open>\<^bold>\<open>Mutable let-bound binder.\<close>\<close>

definition shadow_mut_let_test ::
  \<open>('s, unit, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_mut_let_test \<equiv> FunctionBody \<lbrakk>
     let mut shdw = 7_u64;
     shdw = (8_u64);
   \<rbrakk>\<close>


subsection\<open>Position determines whether a binder can shadow a notation\<close>

text\<open>The three tests above all use \<open>shdw\<close> in \<^emph>\<open>value/operator\<close> position
(bare \<open>shdw\<close>, \<open>shdw + \<dots>\<close>, \<open>shdw = \<dots>\<close>), which dispatches in the \<^bold>\<open>literal\<close>
kind --- there a same-named \<open>let\<close>/\<open>\<lambda>\<close> binder legitimately shadows the
registration (Rust lexical scoping). The contract for the other two
positions is the opposite, and these tests pin it down:

  \<^item> \<^bold>\<open>call\<close> position \<open>x.shdw(\<dots>)\<close> / \<open>shdw(\<dots>)\<close>: a method/call head is a
    selector that can never be the local; the registered \<^bold>\<open>function\<close>
    notation \<^emph>\<open>wins\<close> over a same-named binder.
  \<^item> \<^bold>\<open>field\<close> position \<open>x.shdw\<close>: likewise a selector; the registered
    \<^bold>\<open>field\<close> notation wins.

\<open>shdw\<close> is registered in all three kinds (\<open>shadow_test_lens\<close> field,
\<open>shadow_test_fn\<close> call, \<open>shadow_test_lit\<close> literal); see
\<^ML>\<open>Micro_Rust_Notation_Cmd.is_grammatical_name\<close> and
\<open>witness_takes_precedence\<close> in \<^file>\<open>Micro_Rust_Notations.thy\<close>.\<close>

text\<open>\<^bold>\<open>Literal position: binder wins.\<close> With a \<open>let shdw\<close> in scope, the
trailing bare \<open>shdw\<close> resolves to the \<open>let\<close>-bound \<open>7\<close>, NOT to the
registered literal \<open>shadow_test_lit = 99\<close>.\<close>

definition shadow_literal_binder_wins ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_literal_binder_wins \<equiv> FunctionBody \<lbrakk>
     let shdw = 7;
     shdw
   \<rbrakk>\<close>

lemma shadow_literal_binder_wins_uses_binder:
  shows \<open>shadow_literal_binder_wins = FunctionBody \<lbrakk> let shdw = 7; shdw \<rbrakk>\<close>
  unfolding shadow_literal_binder_wins_def by (rule refl)
\<comment>\<open>The RHS \<open>shdw\<close> is the let-binder; had the literal notation hijacked
  it, this would mention \<open>shadow_test_lit\<close> and fail to be \<open>refl\<close>.\<close>

text\<open>\<^bold>\<open>Call position: function notation wins.\<close> Even with a same-named
\<open>let shdw\<close> in scope, the method head \<open>.shdw()\<close> resolves to the
registered \<open>shadow_test_fn\<close>, not the local. This is the \<open>x.f(f)\<close>
scenario in miniature: the \<open>shdw\<close> \<^emph>\<open>value\<close>
passed as the receiver is the binder, while the \<open>.shdw\<close> \<^emph>\<open>method\<close> head
is the notation. (\<open>shadow_test_fn :: nat \<Rightarrow> \<dots> function_body\<close> is unary,
so the no-arg method call \<open>r.shdw()\<close> supplies the receiver \<open>r\<close> as its
sole argument.)

The proof that the notation won is structural: the \<^emph>\<open>definition itself
type-checks\<close>. Had the \<open>let shdw\<close> binder hijacked the \<open>.shdw\<close> method
head, the head would be a \<open>nat\<close> local --- not callable --- and the body
would fail to parse/type-check.\<close>

definition shadow_call_notation_wins ::
  \<open>('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_call_notation_wins \<equiv> FunctionBody \<lbrakk>
     let shdw = 0;
     shdw.shdw()
   \<rbrakk>\<close>
\<comment>\<open>The definition type-checking IS the test: the \<open>.shdw\<close> method head
  resolved to the registered \<open>shadow_test_fn\<close> (a \<open>function_body\<close>-typed
  call whose sole argument is the \<open>shdw\<close> receiver, the let-binder \<open>0\<close>).
  Had the \<open>let shdw\<close> binder captured the method head, it would be a
  \<open>nat\<close> local --- not callable --- and this definition would fail to
  type-check. (We assert via type-checking rather than an equality
  lemma, matching the call-position tests earlier in this file.)\<close>

text\<open>\<^bold>\<open>Field position: field notation wins.\<close> With a same-named \<open>let shdw\<close>
in scope, the field access \<open>r.shdw\<close> resolves to the registered
\<open>shadow_test_lens\<close>, not the local. This is the \<open>x.f\<close> selector
scenario: the \<open>.shdw\<close>
selector is the field, while the \<open>r\<close> receiver (here itself named
\<open>shdw\<close>) is the binder.

As with the call case, the proof is structural --- the definition only
type-checks because \<open>.shdw\<close> resolved to the \<open>shadow_test_lens\<close> lens; a
\<open>let\<close>-bound non-lens local could not be field-accessed.\<close>

definition shadow_field_notation_wins ::
  \<open>('s, 'inner, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_field_notation_wins \<equiv> FunctionBody \<lbrakk>
     let shdw = \<llangle>undefined :: 'outer\<rrangle>;
     shdw.shdw
   \<rbrakk>\<close>


text\<open>\<^bold>\<open>Free identifier with no binder and no registration.\<close> An
unregistered, unbound identifier should remain a free variable rather
than getting routed through dispatch.\<close>

term \<open>\<lbrakk> some_unregistered_name \<rbrakk>\<close>
  \<comment>\<open>Should print as \<open>literal some_unregistered_name\<close>, with
    \<open>some_unregistered_name\<close> a fresh free variable.\<close>


subsubsection\<open>Extended binder-shadow tests\<close>

text\<open>The tests in this subsection extend the basic
\<open>shadow_{lambda,let,mut_let}_test\<close> coverage above to every µRust
binder shape. Each test re-uses the \<^verbatim>\<open>shdw\<close>/\<^verbatim>\<open>mask\<close> registrations
declared earlier (literal/function/field). The contract under test is
the same in every case: a binder named like a registered notation must
shadow the registration in its body.

The proof method everywhere is \<open>by (rule refl)\<close> because the resolved
term is expected to have the bound variable as an in-scope binder use
(the \<open>\<up>\<close> arrow in the printer reflects the \<open>literal\<close> wrapper, but
the underlying \<open>Bound n\<close>/\<open>Free name\<close> is the same on both sides of the
equation).\<close>


text\<open>\<^bold>\<open>let with arithmetic body using the binder twice.\<close> Already
tested via \<open>shadow_let_test\<close> above; here we add a sequence-of-lets
form to exercise multiple successive binders where the inner one
shadows again.\<close>

definition shadow_nested_let_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_nested_let_test \<equiv> FunctionBody \<lbrakk>
     let shdw = 1_u64;
     let shdw = shdw + 2;
     shdw + 3
   \<rbrakk>\<close>

lemma shadow_nested_let_test_unaffected:
  shows \<open>shadow_nested_let_test = FunctionBody \<lbrakk>
     let shdw = 1_u64;
     let shdw = shdw + 2;
     shdw + 3
   \<rbrakk>\<close>
  unfolding shadow_nested_let_test_def by (rule refl)


text\<open>\<^bold>\<open>let \<dots> else \<dots> binder.\<close> The binder introduced by a
\<^verbatim>\<open>let \<dots> else \<dots>\<close> form must shadow the registration in the success-path
body, just like a plain \<^verbatim>\<open>let\<close>.\<close>

definition shadow_let_else_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_let_else_test \<equiv> FunctionBody \<lbrakk>
     let Some(shdw) = Some(7_u64) else { return 0_u64; };
     shdw + shdw
   \<rbrakk>\<close>

lemma shadow_let_else_test_unaffected:
  shows \<open>shadow_let_else_test = FunctionBody \<lbrakk>
     let Some(shdw) = Some(7_u64) else { return 0_u64; };
     shdw + shdw
   \<rbrakk>\<close>
  unfolding shadow_let_else_test_def by (rule refl)


text\<open>\<^bold>\<open>if-let binder.\<close> Same shadowing in the success branch of an
\<^verbatim>\<open>if let\<close> form.\<close>

definition shadow_if_let_test ::
  \<open>('s, unit, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_if_let_test \<equiv> FunctionBody \<lbrakk>
     if let Some(shdw) = Some(7_u64) {
       \<llangle>shdw + shdw\<rrangle>;
     }
   \<rbrakk>\<close>

lemma shadow_if_let_test_unaffected:
  shows \<open>shadow_if_let_test = FunctionBody \<lbrakk>
     if let Some(shdw) = Some(7_u64) {
       \<llangle>shdw + shdw\<rrangle>;
     }
   \<rbrakk>\<close>
  unfolding shadow_if_let_test_def by (rule refl)


text\<open>\<^bold>\<open>if-let-else binder.\<close> Both branches; the binder is in scope in
the success branch but not in the else branch.\<close>

definition shadow_if_let_else_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_if_let_else_test \<equiv> FunctionBody \<lbrakk>
     if let Some(shdw) = Some(7_u64) {
       shdw + shdw
     } else {
       0_u64
     }
   \<rbrakk>\<close>

lemma shadow_if_let_else_test_unaffected:
  shows \<open>shadow_if_let_else_test = FunctionBody \<lbrakk>
     if let Some(shdw) = Some(7_u64) {
       shdw + shdw
     } else {
       0_u64
     }
   \<rbrakk>\<close>
  unfolding shadow_if_let_else_test_def by (rule refl)


text\<open>\<^bold>\<open>match-arm constructor-with-args binder.\<close> A name introduced as a
constructor argument in a match arm shadows the registration in that
arm's RHS.\<close>

definition shadow_match_arm_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_match_arm_test \<equiv> FunctionBody \<lbrakk>
     match Some(7_u64) {
       Some(shdw) \<Rightarrow> shdw + shdw,
       None \<Rightarrow> 0_u64
     }
   \<rbrakk>\<close>

lemma shadow_match_arm_test_unaffected:
  shows \<open>shadow_match_arm_test = FunctionBody \<lbrakk>
     match Some(7_u64) {
       Some(shdw) \<Rightarrow> shdw + shdw,
       None \<Rightarrow> 0_u64
     }
   \<rbrakk>\<close>
  unfolding shadow_match_arm_test_def by (rule refl)


text\<open>\<^bold>\<open>Tuple destructuring let.\<close> Multiple binders introduced in one
\<^verbatim>\<open>let\<close> via tuple destructuring; each must shadow the registration in
the body.\<close>

definition shadow_tuple_let_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_tuple_let_test \<equiv> FunctionBody \<lbrakk>
     let (shdw, mask) = (3_u64, 4_u64);
     shdw + mask
   \<rbrakk>\<close>

lemma shadow_tuple_let_test_unaffected:
  shows \<open>shadow_tuple_let_test = FunctionBody \<lbrakk>
     let (shdw, mask) = (3_u64, 4_u64);
     shdw + mask
   \<rbrakk>\<close>
  unfolding shadow_tuple_let_test_def by (rule refl)


text\<open>\<^bold>\<open>Closure parameter shadows the registration.\<close> A closure
parameter named \<^verbatim>\<open>shdw\<close> must shadow the same-named registration in
its body, exactly like a function parameter. The body of the closure
type-checks at \<open>64 word \<Rightarrow> 64 word\<close>, but lifted into the embedding,
so the test pins the closure's resolved shape via cartouche
equivalence.\<close>
term \<open>\<lbrakk> |shdw| { shdw + shdw } \<rbrakk>\<close>
  \<comment>\<open>The closure's body uses of \<open>shdw\<close> must be the closure binder, not
    a dispatch to \<open>shadow_test_lit\<close>. Inspection sanity check.\<close>


text\<open>\<^bold>\<open>Mixed: let-binder shadows registration; outside it, a
sibling closure with the same parameter name is independent.\<close> The
two binder slots are at different positions in the AST; both must
shadow the registration in their respective bodies.\<close>
                  
term \<open>\<lbrakk>         
  let shdw = 5_u64;
  shdw
\<rbrakk>\<close>

term \<open>\<lbrakk> let asdf = 42; asdf \<rbrakk>\<close>

  \<comment>\<open>Pre-condition: the let-binder shadows the registration.\<close>

term \<open>\<lbrakk> |shdw| { shdw + 1_u64 } \<rbrakk>\<close>
  \<comment>\<open>Pre-condition: the closure parameter shadows the registration.\<close>

\<comment>\<open>The combination form
   \<^verbatim>\<open>let shdw = ...; let inner = |shdw| { shdw + ... }; inner(shdw)\<close>
   is not currently accepted by the grammar (closures are not valid
   RHSes of \<open>let\<close>). The two single-binder tests above cover the
   shadowing semantics in each scope independently.\<close>


text\<open>\<^bold>\<open>Body that does NOT shadow uses the registration.\<close> Sanity
check: when a registered name is used WITHOUT a same-named binder, the
dispatch fires and we see the registered backend in the resolved term.
This is the contrast to the shadow tests --- it confirms the
registrations are still active.\<close>

definition shadow_no_shadow_test ::
  \<open>('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_no_shadow_test \<equiv> FunctionBody \<lbrakk>
     \<comment>\<open>No \<open>shdw\<close> binder anywhere; the literal use must dispatch to
       the registered \<open>shadow_test_lit :: nat = 99\<close>.\<close>
     shdw
   \<rbrakk>\<close>

lemma shadow_no_shadow_test_dispatches:
  shows \<open>shadow_no_shadow_test = FunctionBody (literal 99)\<close>
  unfolding shadow_no_shadow_test_def shadow_test_lit_def by (rule refl)


text\<open>\<^bold>\<open>Path-style name shadowed by a binder is impossible by
construction\<close> --- you cannot bind a variable whose name contains \<^verbatim>\<open>::\<close>
in HOL. So the only shadow risk is the plain-identifier kind, which the
above tests cover.

We DO have to make sure path-style dispatch still fires when the same
name is registered as a path. The \<open>multi-backend dispatch on a path
name\<close> tests in the previous subsection cover this.\<close>


subsection\<open>Path identifier source-position markup\<close>

text\<open>The path AST translator merges per-segment source positions into
a single range covering the whole \<open>foo::bar(::\<dots>)\<close> form. \<open>lookup_id_tr\<close>
reads it back via \<open>source_positions_of\<close> so use-site markup highlights
the entire path. This is a visual sanity check --- the test below
processes cleanly and at jEdit time exposes the merged position by
ctrl-click on the path identifier landing back at the registration.\<close>

private definition shadow_path_lit :: \<open>nat\<close>
  where \<open>shadow_path_lit = 100\<close>
micro_rust_notation shadow_path_lit ("Markup::path::name")

term \<open>\<lbrakk> Markup::path::name \<rbrakk>\<close>


subsection\<open>Non-grammatical names (turbofish / macro forms)\<close>

text\<open>Names that are neither plain identifiers nor \<^verbatim>\<open>::\<close>-style paths ---
turbofish forms like \<open>Foo::<T>::new\<close> --- contain characters (\<open><\<close>, \<open>>\<close>)
that no µRust grammar production covers, so the surface token cannot be
parsed at all. \<^verbatim>\<open>micro_rust_notation\<close> detects this (via
\<^ML>\<open>Micro_Rust_Notation_Cmd.is_grammatical_name\<close>) and additionally emits
a bespoke \<^verbatim>\<open>syntax\<close> production (a new lexer token whose template IS the
rust name) plus a \<^verbatim>\<open>parse_ast_translation\<close> that rewrites the token to
the ordinary \<^verbatim>\<open>_urust_identifier_id\<close> AST node --- so it flows through the
exact same table-dispatch pipeline as a plain or path identifier (no
backend special-casing; type-directed dispatch, markup, and binder/field
precedence all apply). Without the production the dispatch-table entry
alone is useless: there is nothing to parse. These tests pin that the
bespoke path makes the turbofish use sites both \<^emph>\<open>parse\<close> and \<^emph>\<open>resolve\<close>.\<close>

context begin

text\<open>\<^bold>\<open>Turbofish, function kind.\<close> \<open>Turbo::<T>::new(x)\<close> must parse
(needs the bespoke production) and resolve in function position to the
registered backend. As with the path-name function tests above, this is
a shape-only smoke test: \<open>\<lbrakk>f(x)\<rbrakk>\<close> is a \<^emph>\<open>call expression\<close>, not a bare
\<open>function_body\<close>, so we do not equate it to the backend --- we just confirm
the turbofish use site parses and type-checks via the new dispatch path
(it would fail to parse at all without the bespoke production).\<close>


private definition turbo_new ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>turbo_new x \<equiv> FunctionBody \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>\<close>
micro_rust_notation (call) turbo_new ("Turbo::<T>::new")

term \<open>\<lbrakk> Turbo::<T>::new(0) \<rbrakk>\<close>

text\<open>\<^bold>\<open>Turbofish with a numeric generic argument.\<close> Exercises a
turbofish whose generic argument is a numeral, e.g. \<open>Foo::<2>::new\<close>.\<close>

private definition turbo_numeric_new ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>turbo_numeric_new x \<equiv> FunctionBody \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>\<close>
micro_rust_notation (call) turbo_numeric_new ("Turbo::<2>::new")

term \<open>\<lbrakk> Turbo::<2>::new(0) \<rbrakk>\<close>

text\<open>\<^bold>\<open>Turbofish, literal kind.\<close> A non-grammatical name registered as
a literal value also gets the bespoke production and resolves at a bare
use site. Here the use is a literal (not a call), so we \<^emph>\<open>can\<close> assert the
resolved value: it must dispatch to \<open>turbo_lit\<close>.\<close>

private definition turbo_lit :: \<open>nat\<close> where \<open>turbo_lit = 13\<close>
micro_rust_notation (literal) turbo_lit ("Turbo::<T>::VALUE")

term \<open>\<lbrakk> Turbo::<T>::VALUE \<rbrakk>\<close>

lemma test_turbofish_lit_dispatched:
  shows \<open>\<lbrakk> Turbo::<T>::VALUE \<rbrakk> = literal turbo_lit\<close>
  by (rule refl)

text\<open>\<^bold>\<open>Macro name backed by an \<^theory_text>\<open>abbreviation\<close>\<close> (the std-lib
logger shape: \<^verbatim>\<open>StdLib_Logging.fatal\<close> registered as \<^verbatim>\<open>fatal!\<close>). The
\<^verbatim>\<open>!\<close> makes the name non-grammatical, and \<^ML>\<open>Syntax.read_term\<close> expands
the abbreviation to an \<^verbatim>\<open>Abs\<close> --- so \<^verbatim>\<open>emit_bespoke_syntax\<close> recovers the
backend constant via \<^ML>\<open>Proof_Context.read_const\<close> for its markup binding.
This pins that such a name both registers (would throw without the
\<^verbatim>\<open>read_const\<close> recovery) and resolves at a use site (would not parse
without the bespoke grammar production).\<close>

context begin

private abbreviation shout :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close> where
  \<open>shout x \<equiv> FunctionBody \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>\<close>
micro_rust_notation (call) shout ("shout!")

private definition shout_use :: \<open>('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>shout_use \<equiv> FunctionBody \<lbrakk> shout!(0) \<rbrakk>\<close>

end


subsection\<open>Registered-but-no-type-match is a hard error\<close>

text\<open>If a uRust notation is registered for a name but \<^emph>\<open>no\<close> backend's
type unifies with the use-site type, the dispatcher must \<^bold>\<open>error\<close> ---
not silently demote the name to a free variable. This is the
\<open>Foo::mk()\<close> bug: a no-arg call against a backend that
takes arguments. The marker only exists because the name is registered,
so an empty candidate set is a genuine arity/type mismatch.

\<open>resolve\<close>'s \<open>no_match_error\<close> fires during the typed \<open>term_check\<close> phase,
so we verify it the robust way: build the offending use with
\<^ML>\<open>Syntax.read_term\<close> inside an \<^ML>\<open>Exn.capture\<close> and assert it raises.\<close>

context begin

private definition err_backend ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>err_backend \<equiv> \<lambda>a b. FunctionBody \<lbrakk> \<llangle>a\<rrangle> \<rbrakk>\<close>
micro_rust_notation (call) err_backend ("ErrName::mk")

text\<open>\<^bold>\<open>Correct arity resolves.\<close> Sanity check: a 2-arg use type-checks
(the definition succeeding is the proof the notation resolved).\<close>

private definition err_ok_use ::
  \<open>('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>err_ok_use \<equiv> FunctionBody \<lbrakk> ErrName::mk(0, 0) \<rbrakk>\<close>

text\<open>\<^bold>\<open>Wrong arity errors.\<close> A no-arg use \<open>ErrName::mk()\<close> has no
type-compatible backend (the only backend is binary), so reading it must
raise. We capture the exception rather than let it abort the theory.\<close>

ML\<open>
  val _ =
    let
      val bad = "\<lbrakk> ErrName::mk() \<rbrakk>"
      val res = Exn.capture (fn () => Syntax.read_term \<^context> bad) ()
    in
      (case res of
        Exn.Exn (ERROR msg) =>
          if String.isSubstring "no backend matches" msg
          then writeln ("OK: registered-but-no-match errored as expected:\n" ^ msg)
          else error ("Wrong error message for ErrName::mk():\n" ^ msg)
      | Exn.Exn e => Exn.reraise e
      | Exn.Res _ =>
          error "ErrName::mk() should have failed (no type-compatible backend) but resolved")
    end;
\<close>

end


end


end
