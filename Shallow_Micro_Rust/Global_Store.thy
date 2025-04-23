(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Global_Store
  imports Lenses_And_Other_Optics.Lenses_And_Other_Optics Misc.Array Misc.Vector
      Core_Expression Result_Type (* Range_Type *)
begin
(*>*)

section\<open>References, and the global store\<close>

subsection\<open>References\<close>

text\<open>References \<^emph>\<open>references\<close> are basically pointers that carry around an address that points-into a
global store, such as physical memory or a logical runtime heap.
References of this sort are familiar from functional programming languages like Standard ML and OCaml,
and allow us to introduce a structured form of mutability into our Micro Rust language without having
to deal with how values are encoded into a byte-addressable memory.

References come in two flavors: untyped and typed. \<^emph>\<open>Untyped references\<close> (or \<^emph>\<open>raw references\<close>) are essentially pointers
into a monomorphic global store, without information of how the global value behind the reference is to be
interpreted. For example, a raw reference to a memory-backed global store would dereference to a list
of raw bytes.

\<^emph>\<open>Typed references\<close> are constructed as "focused raw references": They attach to a raw reference a focus
specifying how the raw global value behind the reference can be interpreted as a concrete value type.
For example, the focus attached to a typed reference into a memory-backed global store encapsulates
the byte-level presentation of the reference's value type.

Below, the fixed type typ\<open>'b\<close> represents the "global" values that the global store holds, while the
typ\<open>'v\<close> represents the type of the value actually stored by this reference. When creating a typed
reference one must provide a focus between \<^typ>\<open>'b\<close> and \<^typ>\<open>'v\<close>.\<close>

text\<open>Untyped/raw references are just wrappers around raw addresses. The global value type is
encoded in the global reference's type.\<close>
datatype_record ('a, 'b) gref =
  gref_address :: \<open>'a\<close>

text\<open>A wrapper around a reference which only allows dereference, not update.\<close>
datatype ('a, 'b) ro_gref =
  ROGRef (unsafe_gref_from_ro_gref: \<open>('a, 'b) gref\<close>)

text\<open>Typed references are references paired with a focus onto a subquotient of the global value
type.\<close>
type_synonym ('a, 'b, 'v) ref = \<open>(('a, 'b) gref, 'b, 'v) focused\<close>
type_synonym ('a, 'b, 'v) ro_ref = \<open>(('a, 'b) ro_gref, 'b, 'v) focused\<close>

abbreviation untype_ref where \<open>untype_ref \<equiv> unwrap_focused\<close>
abbreviation untype_roref where \<open>untype_roref \<equiv> unwrap_focused\<close>

translations
  "CONST unwrap_focused" \<leftharpoondown> "CONST untype_ref"
  "CONST unwrap_focused" \<leftharpoondown> "CONST untype_roref"                                                        

definition ro_ref_from_ref :: \<open>('a, 'b, 'v) ref \<Rightarrow> ('a, 'b, 'v) ro_ref\<close> where
  \<open>ro_ref_from_ref \<equiv> update_unwrap_focused ROGRef\<close>

definition unsafe_ref_from_ro_ref :: \<open>('a, 'b, 'v) ro_ref \<Rightarrow> ('a, 'b, 'v) ref\<close> where
  \<open>unsafe_ref_from_ro_ref \<equiv> update_unwrap_focused unsafe_gref_from_ro_gref\<close>

abbreviation ref_address :: \<open>('a, 'b, 'v) ref \<Rightarrow> 'a\<close> where
  \<open>ref_address r \<equiv> gref_address (unwrap_focused r)\<close>

abbreviation ro_address :: \<open>('a,'b,'v) ro_ref \<Rightarrow> 'a\<close> where
  \<open>ro_address r \<equiv> gref_address (unsafe_gref_from_ro_gref (unwrap_focused r))\<close>

consts
  address :: \<open>'a \<Rightarrow> 'b\<close>
adhoc_overloading
  address \<rightleftharpoons> gref_address ref_address ro_address

definition make_untyped_ref :: \<open>'a \<Rightarrow> ('a, 'v) gref\<close> where
  \<open>make_untyped_ref addr \<equiv> make_gref addr\<close>

abbreviation make_ref_typed_from_untyped ::
    \<open>('a, 'v) gref \<Rightarrow> ('v,'w) focus \<Rightarrow> ('a, 'v, 'w) ref\<close> where
  \<open>make_ref_typed_from_untyped \<equiv> make_focused\<close>

definition make_ro_ref_typed_from_untyped ::
    \<open>('a, 'v) ro_gref \<Rightarrow> ('v,'w) focus \<Rightarrow> ('a, 'v, 'w) ro_ref\<close> where
  \<open>make_ro_ref_typed_from_untyped \<equiv> make_focused\<close>

subsection \<open>Using optics to focus references and values\<close>

abbreviation focus_reference :: \<open>('v, 'w) focus \<Rightarrow> ('a, 'b, 'v) ref \<Rightarrow> ('a, 'b, 'w) ref\<close> where
  \<open>focus_reference \<equiv> focus_focused\<close>

abbreviation \<open>focus_reference_via_lens l \<equiv> focus_reference (lens_to_focus l)\<close>

lemmas focus_reference_def = focus_focused_def

\<comment>\<open>This empty type class serves as an annotation for types which can appear as the global type
  of a lens. The main example are records, and the main non-example are references. In fact, the
  sole purpose of this class is to help disambiguate the overloaded \<^verbatim>\<open>.\<close>-operator in uRust in case
  the LHS is a reference. In this case, it is a priori not clear if we're focusing the LHS with respect
  to a lens between reference types, or with respect to the lifting of a lens on the value type of the ref.
  We always want the latter, and the \<^verbatim>\<open>localizable\<close> typeclass helps to enforce it.\<close>
class localizable
abbreviation (input) focus_lens_value :: \<open>('v::localizable, 'w) lens \<Rightarrow> 'v \<Rightarrow> 'w\<close> where
  \<open>focus_lens_value \<equiv> lens_view\<close>

consts
  focus_lens_const :: \<open>('v, 'w) lens \<Rightarrow> 'vp \<Rightarrow> 'wp\<close>

adhoc_overloading
  focus_lens_const \<rightleftharpoons> focus_reference_via_lens focus_lens_value

subsection\<open>Focusing references inside structured values\<close>

abbreviation (input) focus_option :: \<open>('a,'b,'v option) ref \<Rightarrow> ('a,'b,'v) ref\<close> where
  \<open>focus_option \<equiv> focus_focused option_focus\<close>

abbreviation (input) focus_result_ok :: \<open>('a,'b, ('v,'e) result) ref \<Rightarrow> ('a,'b,'v) ref\<close> where
  \<open>focus_result_ok \<equiv> focus_focused result_ok_focus\<close>

abbreviation (input) focus_result_err :: \<open>('a,'b, ('v,'e) result) ref \<Rightarrow> ('a,'b,'e) ref\<close> where
  \<open>focus_result_err \<equiv> focus_focused result_err_focus\<close>

abbreviation (input) focus_nth :: \<open>nat \<Rightarrow> ('a,'b,'v list) ref \<Rightarrow> ('a,'b,'v) ref\<close>
  where \<open>focus_nth n \<equiv> focus_focused (nth_focus n)\<close>

abbreviation (input) focus_nth_array :: \<open>nat \<Rightarrow> ('a,'b,('v, 'l::len) array) ref \<Rightarrow> ('a,'b,'v) ref\<close>
  where \<open>focus_nth_array n \<equiv> focus_focused (nth_focus_array n)\<close>

abbreviation (input) focus_nth_vector :: \<open>nat \<Rightarrow> ('a,'b,('v, 'l::len) vector) ref \<Rightarrow> ('a,'b,'v) ref\<close>
  where \<open>focus_nth_vector n \<equiv> focus_focused (nth_focus_vector n)\<close>

subsection\<open>States with a global store\<close>

named_theorems global_store_simps

text\<open>The following \<^emph>\<open>locale\<close> describes a class of abstract machine states that have a \<^emph>\<open>global
store\<close>, basically an abstraction of physical memory, which maps memory addresses, of type \<^typ>\<open>'a\<close>
to values of type \<^typ>\<open>'b\<close>.  As part of this abstraction, we also need an \<^emph>\<open>allocation function\<close>
which identifies memory addresses currently unoccupied by any value.  Note that this model is an
abstraction of physical memory in two senses:
\begin{enumerate*}
\item
Our global store contains values stored at addresses, rather than byte-representations of values,
\item
Allocation of a fresh address never fails, so in a sense we adopt an infinite memory.
\end{enumerate*}

TODO: Should the functions fixed below have type \<^type>\<open>function_body\<close>?  The
\<^type>\<open>function_body\<close> monad may be a misnomer, but functionally it offers what we need. We're
currently lifting those manually to \<^type>\<open>function_body\<close> later on, and then have to invent a mapping
from \<^term>\<open>None\<close> to \<^type>\<open>abort\<close>.\<close>
locale global_store =
  fixes
    \<comment> \<open>Read a value from the global store, at a given address.  This may fail.\<close>
    read_store :: \<open>'s \<Rightarrow> 'a \<rightharpoonup> 'b\<close> and
    \<comment> \<open>Write a value to an address in the store.\<close>
    write_store :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 's option\<close> and
    \<comment> \<open>Allocate a fresh address for a new slot in the global store.\<close>
    allocate_store :: \<open>'s \<Rightarrow> ('a \<times> 's) option\<close>
  assumes
    \<comment> \<open>Reads from an address, immediately after a write, succeed with the value written.\<close>
    \<comment> \<open>TODO: What about locations we can write but not read from For such, the read-after-write
              rule below would be violated.\<close>
    write_store_read_store [global_store_simps]: \<open>write_store \<sigma> k v = Some \<sigma>' \<Longrightarrow> read_store \<sigma>' k = Some v\<close> and
    \<comment> \<open>Write commute with each other if they are to diffebrent addresses.\<close>
    write_store_rearrange [global_store_simps]:
        \<open>k \<noteq> k' \<Longrightarrow> Option.bind (write_store \<sigma> k v) (\<lambda>\<sigma>'. write_store \<sigma>' k' v') =
                     Option.bind (write_store \<sigma> k' v') (\<lambda>\<sigma>'. write_store \<sigma>' k v)\<close> and
    \<comment> \<open>Writes to the same address collapse, with only the latter write kept.\<close>
    write_store_write_store [global_store_simps]:
      \<open>write_store \<sigma> k v = Some \<sigma>' \<Longrightarrow> write_store \<sigma>' k v' = write_store \<sigma> k v'\<close> and
    allocate_write_succeeds: \<open>allocate_store \<sigma> = Some (f, \<sigma>') \<Longrightarrow> \<exists>\<sigma>''. write_store \<sigma>' f v = Some \<sigma>''\<close>
begin

text\<open>The following definition \<^emph>\<open>takes a reference to\<close> an existing value.  As a side-effect, it
\<^emph>\<open>allocates\<close> a fresh location in the state's global store, writes the value to that slot, and then
returns a reference to that slot. As part of the reference definition, one must also give
functions for injecting values of typ\<open>'v\<close> into typ\<open>'b\<close> and for extracting in the other direction.\<close>
definition reference_raw :: \<open>'b \<Rightarrow> ('s, ('a, 'b) gref, 't, 'abort, 'i, 'o) expression\<close> where
  \<open>reference_raw g \<equiv> Expression (\<lambda>\<sigma>.
     case allocate_store \<sigma> of
       None \<Rightarrow> Abort AssertionFailed \<sigma>
     | Some (addr,\<sigma>') \<Rightarrow>
        (case write_store \<sigma>' addr g of
          None \<Rightarrow> Abort AssertionFailed \<sigma>'
         | Some \<sigma>'' \<Rightarrow> Success (make_gref addr) \<sigma>''))\<close>

definition reference_raw_fun :: \<open>'b \<Rightarrow> ('s, ('a, 'b) gref, 'abort, 'i, 'o) function_body\<close> where
  \<open>reference_raw_fun g \<equiv> FunctionBody (reference_raw g)\<close>

text\<open>The following definition \<^emph>\<open>modifies\<close> the value pointed-to by a reference by applying the
given function. Note that this method will panic if an attempt is made to write to an unallocated
reference.\<close>
definition modify_raw :: \<open>('a, 'b) gref \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('s, unit, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>modify_raw ref f \<equiv> bind (get read_store) (\<lambda>store.
     case store (address ref) of
       None \<Rightarrow> abort DanglingPointer
     | Some old \<Rightarrow> put_assert (\<lambda>\<sigma>. write_store \<sigma> (address ref) (f old)) DanglingPointer)\<close>

definition modify_raw_fun :: \<open>('a, 'b) gref \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>modify_raw_fun ref f \<equiv> FunctionBody (modify_raw ref f)\<close>

text\<open>The following definition \<^emph>\<open>updates\<close> the value pointed-to by a reference to a new value. Note
that this method will panic if an attempt is made to write to an unallocated reference, or
if the value stored in this reference is of the wrong type.\<close>

definition update_raw :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> ('s, unit, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>update_raw ref v \<equiv> modify_raw ref (\<lambda>_. v)\<close>

definition update_raw_fun :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close> where
  \<open>update_raw_fun ref v \<equiv> FunctionBody (update_raw ref v)\<close>

definition dereference_by_value_raw :: \<open>('a, 'b) gref \<Rightarrow> ('s, 'b, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>dereference_by_value_raw ref \<equiv>
     bind (get (\<lambda>\<sigma>. read_store \<sigma>)) (\<lambda>store.
          case store (address ref) of
            None   \<Rightarrow> abort DanglingPointer
          | Some b \<Rightarrow> literal b)
        \<close>

definition dereference_by_value_raw_fun :: \<open>('a, 'b) gref \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body\<close> where
  \<open>dereference_by_value_raw_fun ref \<equiv> FunctionBody (dereference_by_value_raw ref)\<close>

end

(*<*)
end
(*>*)
