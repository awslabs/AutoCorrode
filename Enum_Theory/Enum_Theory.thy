(*  Title:      AutoCorrode/Enum_Theory/Enum_Theory.thy
    Author:     AutoCorrode Project

    Enum datatype support for AutoCorrode.
    Provides infrastructure for working with enumeration types.
*)

theory Enum_Theory
imports Main
keywords "enum" :: thy_decl
begin

text \<open>
  This theory provides support for enumeration types,
  including:
  - The @{text enum} command for defining monomorphic, non-recursive enumerations
  - Automatic generation of introduction rules (constructors)
  - Automatic generation of elimination rules (case combinators)
  - Distinctness theorems for different constructors
  - Exhaustiveness theorems

  Syntax:
    enum <type_name> =
      <constructor1> [<type1> ... <typeN>]
    | <constructor2> [<type1> ... <typeM>]
    | ...

  Example:
    enum color = Red | Green | Blue
    enum option_nat = None | Some nat
    enum result = Ok nat | Error string
    enum pair = Pair nat string
\<close>

definition the_map_of :: \<open>('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b\<close> where
  \<open>the_map_of l k \<equiv> option.the (map_of l k)\<close>

lemma the_map_of_Cons_eq: \<open>k = k' \<Longrightarrow> the_map_of ((k, v) # t) k' = v\<close>
  by (simp add:the_map_of_def)

lemma the_map_of_Cons_neq: \<open>k' \<noteq> k \<Longrightarrow> the_map_of ((k, v) # t) k' = the_map_of t k'\<close>
  by (simp add:the_map_of_def)

ML_file "enum_cmd.ML"

end
