(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Basic_Micro_Rust
  imports
    Word_Lib.Many_More 
    Crush.Crush 
    Micro_Rust_Runtime.Runtime_Heap  
    Micro_Rust_Std_Lib.StdLib_References  
    Micro_Rust_Std_Lib.StdLib_Slice
    "HOL-Library.Code_Target_Numeral" \<comment> \<open>Map naturals/integers onto OCaml \<^verbatim>\<open>zarith\<close> types\<close>
    "HOL-Library.Code_Abstract_Char"  \<comment> \<open>Tidy up character and string literals a little\<close>
begin
(*>*)

section\<open>Working introduction to Micro Rust\<close>

text\<open>The purpose of this theory is to give a fast example-based introduction
to Micro Rust expressions, specifications, and proofs.\<close>

subsection\<open>Micro Rust look and feel\<close>

text\<open>Micro Rust programs are written in double-square brackets \<^verbatim>\<open>\<lbrakk> EXPRESSION \<rbrakk>\<close>
and are syntactically very similar to Rust. Here are some examples:\<close>

term \<open>\<lbrakk> x + y \<rbrakk>\<close> (* "word_add_no_wrap (\<up>x) (\<up>y)" :: "('a, 'b word, 'c, 'abort, 'd, 'e) expression" *)

term \<open>\<lbrakk> 
  if x == 42 { 
    true
  } else {
    panic!("I thought the answer was always 42!")
  } 
\<rbrakk>\<close>

text\<open>A function definition, then used in a Micro Rust expression:\<close>

definition some_function :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> (_, 64 word, _, _, _) function_body\<close> where
  \<open>some_function a b \<equiv> FunctionBody \<lbrakk>
     return a + b;
  \<rbrakk>\<close>

term \<open>\<lbrakk> 
  if some_function(1,2) == 42 { 
    true
  } else {
    panic!("I thought the answer was always 42!")
  } 
\<rbrakk>\<close>

experiment
fixes a :: \<open>nat list\<close>
begin
term \<open>\<lbrakk> 
  for i in 0..\<llangle>10::64 word\<rrangle> { \<comment>\<open>The \<^verbatim>\<open>\<llangle>\<dots>\<rrangle>\<close> will be explained below\<close>
    if a[i] == 42 {
      return True;
    }
  };
  return False; 
\<rbrakk>\<close>
end

subsection\<open>Shallow embedding\<close>

text\<open>We call \<^verbatim>\<open>\<lbrakk> \<dots> \<rbrakk>\<close> the \<^emph>\<open>shallow embedding bracket\<close> as it shallowly embeds the given Micro Rust
expression into HOL, producing a HOL value of type \<^verbatim>\<open>expression\<close>. Note that there is, at present,
no Micro Rust AST in HOL, and Micro Rust programs do not exist "on their own" outside of Isabelle's 
parsing frontend: They are always immediately interpreted as their denotation w.r.t. \<^verbatim>\<open>\<lbrakk> ... \<rbrakk>\<close>. If 
we were to switch to a deep embedding of Micro Rust at some point, one would want to introduce a 
deep embedding bracket targeting the type of Micro Rust AST's, and factor the shallow embedding bracket
as the composition of the deep embedding bracket and an evaluation function defined \<^emph>\<open>within HOL\<close>.\<close>

text\<open>Shallow embeddings of Micro Rust programs into HOL are values of type
\<^verbatim>\<open>expression\<close>, which is effectively a state monad: Elements of \<^verbatim>\<open>('s, 'v, 'r, \<dots>) expression\<close>
are state-transforming functions on the state-type \<^verbatim>\<open>'s\<close>, plus information about how the
computation concluded. Quoting the definition of \<^verbatim>\<open>expression\<close> from \<^file>\<open>../Shallow_Micro_Rust/Core_Expression.thy\<close>:\<close>

\<comment>\<open>\<^verbatim>\<open>
datatype ('s, 'v, 'r, 'abort, 'i, 'o) continuation
  = Success \<open>'v\<close> \<open>'s\<close>
  | Return \<open>'r\<close> \<open>'s\<close>
  | Abort \<open>abort\<close> \<open>'s\<close>
  | Yield \<open>'i\<close> \<open>'s\<close> \<open>'o \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  and ('s, 'v, 'r, 'abort, 'i, 'o) expression
  = Expression \<open>'s \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) continuation\<close>
\<close>\<close>

text\<open>Micro Rust computations can terminate with a value, a return, an abort, or a yield. We
ignore the yield for now, and with it the \<^verbatim>\<open>'i\<close> and \<^verbatim>\<open>'o\<close> type parameters. The \<^verbatim>\<open>'s\<close>, \<^verbatim>\<open>'v\<close>
and \<^verbatim>\<open>'r\<close> type parameters are the state type, value type, and return type, respectively. 
For example, within a \<^verbatim>\<open>let\<close>-binding \<^verbatim>\<open>let a = b + c; \<dots>\<close>, the sub-expression 
\<^verbatim>\<open>b + c\<close> terminates with the \<^emph>\<open>value\<close> of \<^verbatim>\<open>x+y\<close>, allowing it to be bound and reused in the rest of
the computation. Computations terminating with a return correspond to Micro Rust expressions using
the \<^verbatim>\<open>return\<close> keyword, while computations terminating with an abort correspond to Micro Rust expressions
that panic or otherwise enter a condition which stops the program irrespective of the call chain.

Extensionally, the different types of computation results correspond to different binding behaviour
in the Micro Rust monad: Expressions computing values bind to subsequent expressions by passing on
their value. Expressions computing returns bind to subsequent expressions by jumping to the caller,
while expressions computing aborts bind by ignoring their continuation and stopping the computation
immediately.\<close>

subsection\<open>Evaluating Micro Rust\<close>

text\<open>To see Micro Rust programs in action, you can use the \<^verbatim>\<open>evaluate\<close> function which takes 
(the denotation of) a Micro Rust program, an initial state, and produces the state and condition 
in which the computation terminated. For the stateless examples considered here, any value will 
do as the state.\<close>

value \<open>evaluate \<lbrakk> 1 + 2 \<rbrakk> ()
  :: (unit, 64 word, 64 word, unit, unit, unit) continuation\<close>
(* "Success 3 ()"
  :: "(unit, 64 word, 64 word, unit, unit, unit) continuation" *)

definition some_constant :: \<open>64 word\<close>
  where \<open>some_constant \<equiv> 42\<close>

value \<open>evaluate \<lbrakk> 
  if some_constant == 42 { 
    True
  } else {
    panic!("I thought the answer was always 42!")
  } 
\<rbrakk> () :: (unit, bool, bool, unit, unit, unit) continuation\<close>

(* "Success True ()"
  :: "(unit, bool, bool, unit, unit, unit) continuation" *)

definition another_constant :: \<open>64 word\<close>
  where \<open>another_constant \<equiv> 43\<close>

value \<open>evaluate \<lbrakk>
 if another_constant == 42 { 
   True
 } else {
   panic!("I thought the answer was always 42!")
 } 
\<rbrakk> () :: (unit, bool, bool, unit, unit, unit) continuation\<close>

(* "Abort (Panic STR ''I thought the answer was always 42!'') ()"
  :: "(unit, bool, bool, unit, unit, unit) continuation" *)

value [simp] \<open>evaluate \<lbrakk> True  || panic!("oh dear") \<rbrakk> ()
  :: (unit, bool, bool, unit, unit, unit) continuation\<close> (* "Success True ()" *)
value [simp] \<open>evaluate \<lbrakk> False || panic!("oh dear") \<rbrakk> ()\<close> (* "Abort (Panic STR ''oh dear'') ()" *)
value [simp] \<open>evaluate \<lbrakk> True  && panic!("oh dear") \<rbrakk> ()\<close> (* "Abort (Panic STR ''oh dear'') ()" *)
value [simp] \<open>evaluate \<lbrakk> False && panic!("oh dear") \<rbrakk> ()\<close> (* "Success False ()" *)

subsection\<open>Anti-Quotations\<close>

text\<open>Since Micro Rust is shallowly embedded into HOL, it is possible to directly embed arbitrary
HOL expressions into Micro Rust through \<^emph>\<open>anti-quotations\<close>.

The most basic antiquotation is \<^verbatim>\<open>\<epsilon>\<open>\<dots>\<close>\<close>, which embeds HOL terms of type \<^verbatim>\<open>expression\<close> into a
Micro Rust program. For example:\<close>

term \<open>\<lbrakk> 4 + \<epsilon>\<open>literal (sum id {0,1,2,3})\<close> \<rbrakk>\<close>
value \<open>evaluate \<lbrakk> 4 + \<epsilon>\<open>literal (sum id {0,1,2,3})\<close> \<rbrakk> () 
   :: (unit, 64 word, unit, unit, unit, unit) continuation\<close>
(* "Success 10 ()"
  :: "(unit, 64 word, unit, unit, unit, unit) continuation" *)

text\<open>\<^verbatim>\<open>\<up>\<close> is an abbreviation for \<^verbatim>\<open>literal\<close>:\<close>

term \<open>\<lbrakk> 4 + \<epsilon>\<open>literal (sum id {0,1,2,3})\<close> \<rbrakk>\<close>
value \<open>evaluate \<lbrakk> 4 + \<epsilon>\<open>\<up> (sum id {0,1,2,3})\<close> \<rbrakk> () 
   :: (unit, 64 word, unit, unit, unit, unit) continuation\<close>
(* "Success 10 ()"
  :: "(unit, 64 word, unit, unit, unit, unit) continuation" *)

text\<open>Since the pattern \<^verbatim>\<open>\<epsilon>\<open>\<up>(\<dots>)\<close>\<close> is so common, it has an abbreviation itself:
The antiquotation \<^verbatim>\<open>\<llangle>\<dots>\<rrangle>\<close> embeds HOL terms as Micro Rust \<^emph>\<open>literals\<close>:\<close>

term \<open>\<lbrakk> \<llangle>4 :: 32 word\<rrangle> + \<llangle>12 :: 32 word\<rrangle> \<rbrakk>\<close>

text\<open>The \<^verbatim>\<open>literal\<close> and \<^verbatim>\<open>\<up>\<close> antiquotation is automatic for numerals and identifiers
in Micro Rust: So if you wrtite\<close>

term \<open>\<lbrakk> x \<rbrakk>\<close> (* "\<up>x"
  :: "('b, 'a, 'c, 'abort, 'd, 'e) expression" *)

text\<open>you see that it is automatically interpreted as the literal lift of the (free)
variable \<^verbatim>\<open>x\<close> to a Micro Rust expression. Similarly for numerals:\<close>

experiment
begin  
declare [[show_sorts]] \<comment>\<open>Just so we can see type constraints\<close>
term \<open>\<lbrakk> 2 \<rbrakk>\<close> (* "\<up>(2::'a::numeral)"
  :: "('b::type, 'a::numeral, 'c::type, 'd::type, 'e::type) expression" *)
end

text\<open>It is also common to embed HOL \<^emph>\<open>functions\<close> as Micro Rust functions: That is,
given say \<^verbatim>\<open>f :: 'a \<Rightarrow> 'b\<close>, interpret it as \<^verbatim>\<open>'a \<Rightarrow> (_, 'b, _, _) function_body\<close> so
it can be used in normal Micro Rust function application.  This is facilitated using
the antiquotations \<^verbatim>\<open>\<llangle>_\<rrangle>\<^sub>1\<close>,  \<^verbatim>\<open>\<llangle>_\<rrangle>\<^sub>2\<close>, ..., where the index indicates the number of arguments:\<close>

term \<open>\<lbrakk> \<llangle>sum\<rrangle>\<^sub>2(id, \<llangle>{1,2,3,4}\<rrangle>) \<rbrakk>\<close> (* "lift_fun2 sum \<langle>\<up>id, \<up>{1, 2, 3, 4}\<rangle>"
  :: "('b, 'a, 'e, 'c, 'd) expression" *)

subsection\<open>Stateful Micro Rust\<close>

text\<open>All examples above are stateless, so let's look at how stateful computation could be
modelled. Let's say the underlying state is a list of \<^verbatim>\<open>nat\<close>s which we want to multiply up and
store in the state. The minimal state type supporting this would be \<^verbatim>\<open>64 word list \<times> 64 word\<close>:\<close>

datatype_record s = 
  arr :: \<open>64 word list\<close>
  acc :: \<open>64 word\<close>

text\<open>To read/write the components of \<^verbatim>\<open>s\<close>, we lift the respective pure getter/setter functions
in HOL to Micro Rust functions using anti-quotations:\<close>

definition get_arr :: \<open>(s, 64 word list, _, _, _) function_body\<close> where 
  \<open>get_arr \<equiv> FunctionBody (get arr)\<close>

text\<open>This builds on the \<^verbatim>\<open>get\<close> primitive from \<^file>\<open>../Shallow_Micro_Rust/Core_Expression.thy\<close>,
which unfolds to this:\<close>

\<comment>\<open>get_arr \<equiv> FunctionBody (Expression (\<lambda>(\<sigma>::s). Success (arr \<sigma>) \<sigma>))\<close>

definition get_acc :: \<open>(s, 64 word, _, _, _) function_body\<close> where 
  \<open>get_acc \<equiv> FunctionBody (get acc)\<close>

text\<open>Similarly, there's the \<^verbatim>\<open>put\<close> primitive which lifts an endofunction on the underlying
state to a Micro Rust function. Here, we use \<^verbatim>\<open>update_acc (\<lambda>_. val)\<close>, which is the 
update function for the record field \<^verbatim>\<open>acc\<close>:\<close>

definition set_acc :: \<open>64 word \<Rightarrow> (s, unit, _, _, _) function_body\<close> where 
  \<open>set_acc val \<equiv> FunctionBody (put (update_acc (\<lambda>_. val)))\<close>

text\<open>Under the hood, this is just:\<close>

\<comment>\<open>set_acc val \<equiv> FunctionBody (Expression (\<lambda>\<sigma>. Success () (update_acc (\<lambda>_. val) \<sigma>)))\<close>

text\<open>With the getters and setters in place, we can write the desired multiplication function:\<close>

definition multiply_it_up :: \<open>(s, 64 word, _, _, _, _) expression\<close> where
  \<open>multiply_it_up \<equiv> \<lbrakk>
     let data = get_arr();
     \<comment>\<open>Micro Rust wants a \<^verbatim>\<open>64 word\<close> as the loop bound, so we resort to antiquotations
     to construct this.\<close>
     set_acc(1);
     for i in 0..data.len() {
        set_acc(get_acc() * data[i]);
     };
     get_acc()
  \<rbrakk>\<close>

text\<open>Let's try it out:\<close>

value [nbe] \<open>evaluate multiply_it_up (make_s [1,2,3,4,5,6,7,8] 42)
  :: (s, 64 word, 64 word, unit, unit, unit) continuation\<close>
(* "Success 40320 (make_s [1, 2, 3, 4, 5, 6, 7, 8] 40320)"
  :: "(s, 64 word, 64 word, unit, unit, unit) continuation" *)

text\<open>For the fun of it, let's choose values which will make the multiplications
overflow:\<close>

value [nbe] \<open>evaluate multiply_it_up (make_s [100,200,300,400,500,600,700,800] 42)
  :: (s, 64 word, 64 word, unit, unit, unit) continuation\<close>

(* "Abort (Panic STR ''arithmetic overflow'')
  (make_s [100, 200, 300, 400, 500, 600, 700, 800] 504000000000000000)"
  :: "(s, 64 word, 64 word, unit, unit, unit) continuation" *)

subsection \<open>Mutable locals\<close>

text\<open>The previous example is slightly unnatural in that we modelled the accumulator
as part of the underlying state rather than a mutable local variable.

Let's try to use a mutable \<^verbatim>\<open>let\<close> binding in a Micro Rust expression:\<close>

term \<open>\<lbrakk>
     let mut acc = \<llangle>1 :: 64 word\<rrangle>;
     acc
  \<rbrakk>\<close>
(* "bind (Ref::new \<langle>\<up>1\<rangle>) literal"
  :: "('a, (('b, 'c) gref, 'c, 64 word) focused, 'd, 'e, 'f) expression" *)

value [simp] \<open>evaluate \<lbrakk>
     let mut acc = \<llangle>1 :: 64 word\<rrangle>;
     acc
  \<rbrakk> (make_s [100,200,300,400,500,600,700,800] 42)\<close>
(* "case case case Ref::new 1 of FunctionBody x \<Rightarrow> call_function_body x of
      Expression f \<Rightarrow> f (make_s [100, 200, 300, 400, 500, 600, 700, 800] 42) of
 Success v x \<Rightarrow> evaluate (\<up>v) x | Return x xa \<Rightarrow> Return x xa | Abort x xa \<Rightarrow> Abort x xa
 | Yield \<pi> \<sigma>' e' \<Rightarrow> Yield \<pi> \<sigma>' (\<lambda>\<rho>. bind (e' \<rho>) literal)"
  :: "(s, (('a, 'b) gref, 'b, 64 word) focused, 'c, 'abort, 'd, 'e) continuation" *)

text\<open>This may not be what we expected: The \<^verbatim>\<open>let mut ...\<close> binding is transformed into
a call to \<^verbatim>\<open>Ref::new\<close>, which however is not evaluated further. The reason is the following:

In Micro Rust, mutable let bindings are implemented via references: When you establish
a mutable variable, a reference is allocated, and when you read/write it subsequently,
that reference is dereferenced / updated accordingly.

Importantly, dereferencing of references associated with mutable let bindings is
\<^emph>\<open>explicit\<close>, which is the biggest syntactic difference between Rust and Micro Rust.
That is, in the above example, we should really have written \<^verbatim>\<open>*acc\<close> if our intent 
was to return the value of \<^verbatim>\<open>acc\<close>. Indeed, if you look at the return type of the
expression above, you will find \<^verbatim>\<open>('b, 'c) gref, 'c, 64 word) focused\<close> rather than
the expected \<^verbatim>\<open>64 word\<close> -- without going into details, what is being returned here
is the reference associated with \<^verbatim>\<open>acc\<close>, rather than the value.

So, let's try to return the value instead -- comment out the following:
\<close>

\<comment>\<open>
term \<open>\<lbrakk>
     let mut acc = \<llangle>1 :: 64 word\<rrangle>;
     *acc
  \<rbrakk>\<close>
\<close>
(*
Unresolved adhoc overloading of constant
  store_dereference_const ::
    "((??'b, ??'c) gref, ??'c, 64 word) focused \<Rightarrow> (??'a, ??'g, ??'e, ??'f) function_body"
  in term "let acc = Ref::new \<langle>\<up>1\<rangle>; \<^sup>\<star>\<up>acc"
no instances
*)

text\<open>This doesn't work, and the reason is that there is actually no in-built notion of heap
that Micro Rust could use to allocate, dereference and update references. Instead, \<^verbatim>\<open>let mut\<close>
and \<^verbatim>\<open>*\<close> are mapped to uninterpreted constants \<^verbatim>\<open>Ref::new\<close> and \<^verbatim>\<open>store_dereference_const\<close>
which need to be defined first before mutable locals can be used.\<close>

text\<open>Ignoring the details for now, the \<^verbatim>\<open>Reference\<close> locale captures the interface that
Micro Rust uses to read and write references. If we assume that we work in the context 
of \<^verbatim>\<open>Reference\<close>, we can indeed write functions operating on references:\<close>

context reference
begin

definition add_one_to_ref :: \<open>(_, _, 64 word) Global_Store.ref \<Rightarrow> ('s, unit, _, _, _) function_body\<close> where
  \<open>add_one_to_ref ptr \<equiv> FunctionBody \<lbrakk>
     let val = *ptr; \<comment>\<open>Reading requires explicit dereferencing\<close>
     let new_val = val + 1;
     ptr = new_val; \<comment>\<open>Updating does not require explicit dereferencing\<close>
  \<rbrakk>\<close>
thm add_one_to_ref_def
(* add_one_to_ref ?ptr \<equiv>
FunctionBody
 (let val = bind (\<up>?ptr) (call_deep1 dereference_fun);
  let new_val = word_add_no_wrap (\<up>val) (\<up>1);  \<star>\<up>?ptr \<leftarrow> \<up>new_val ; \<up>() ) *)

end

text\<open>The \<^verbatim>\<open>reference\<close> locale only captures the interface for reading/writing references,
but \<^emph>\<open>not\<close> for allocating them. In particular, within \<^verbatim>\<open>reference\<close> alone you cannot use
\<^verbatim>\<open>let mut\<close>, since mutable let bindings are reference allocations.

To support reference allocation, you must work in the context of the
\<^verbatim>\<open>reference_allocatable\<close> locale, which extends \<^verbatim>\<open>reference\<close>. More precisely, you need
to inherit one instance of \<^verbatim>\<open>reference_allocatable\<close> per type you need to allocate references
for -- welcome to the joy of locales!

Here is an example -- ignore the prism stuff for now.\<close>

locale "experiment" =
  \<comment> \<open>Reference interface\<close>
    reference reference_types +
    \<comment> \<open>Import \<^verbatim>\<open>reference_allocatable\<close> so we can allocate references for \<^verbatim>\<open>64 word\<close>.\<close>
    ref_word64: reference_allocatable reference_types _ _ _ _ _ _ _ word64_prism
  for reference_types :: \<open>'s::sepalg \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'abort \<Rightarrow> 'i prompt \<Rightarrow> 'o prompt_output \<Rightarrow> unit\<close>
  \<comment> \<open>Ignore for now\<close>
  and word64_prism :: \<open>('b, 64 word) prism\<close>

begin

\<comment>\<open>Overload the -- a priori uninterpreted -- constant \<^verbatim>\<open>Ref::new\<close> with the allocation
function for \<^verbatim>\<open>64 word\<close> that comes from the \<^verbatim>\<open>ref_word64\<close> instance of \<^verbatim>\<open>reference_allocatable\<close>
that we have assumed above.\<close>
adhoc_overloading store_reference_const \<rightleftharpoons> ref_word64.new
\<comment>\<open>Similar for the reference-update function:\<close>
adhoc_overloading store_update_const \<rightleftharpoons>
  update_fun

term ref_word64.new

text\<open>Now we can rewrite our product function from above using a local accumulator:\<close>

definition multiply_it_up :: \<open>64 word list \<Rightarrow> ('s, 64 word, _, _, _, _) expression\<close> where
  \<open>multiply_it_up data \<equiv> \<lbrakk>
     let mut acc = \<llangle>1 :: 64 word\<rrangle>;
     for i in 0..data.len() {
        acc = *acc * data[i];
     };
     *acc
  \<rbrakk>\<close>

definition add_local :: \<open>('s, 64 word, _, _, _, _) expression\<close> where
  \<open>add_local \<equiv> \<lbrakk>
    let len = \<llangle>5 :: 64 word\<rrangle>;
    let mut acc = \<llangle>1 :: 64 word\<rrangle>;
    acc = *acc + len; \<comment> \<open>Need to explicitly dereference the mutable local, but not the local.\<close>
    *acc
  \<rbrakk>\<close>

(*<*)
end

text\<open>You may have noted that we didn't run any experimental evaluations. To be able to conduct
such, we would first need to exhibit a concrete \<^emph>\<open>implementation\<close> of the interfaces exposed
by \<^verbatim>\<open>reference\<close> and \<^verbatim>\<open>reference_allocatable\<close>. So far, we have two such implementations: One based
on a dedicated heap for references, the other based on references rooted in raw memory. You find
examples of how to use them in the \<^verbatim>\<open>Linked_List_*.thy\<close> theories: Those theories define and prove 
the correctness of a linked list reversal in an abstract reference setting first, and then instantiate
it with the heap-backed vs. memory-backed reference implementations.\<close>

(*<*)
end
(*>*)