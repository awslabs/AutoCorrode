(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory AutoLocality
  imports Main
    AutoCommon AutoLens
  keywords "locality_lemma" "locality_autoderive"
    "locality_check" "print_locality_data" :: thy_goal
      and "footprint" :: quasi_command
begin

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
considered, which quickly burdensome.

At the end of this section, the user has commands \<^verbatim>\<open>locality_footprint\<close> and \<^verbatim>\<open>locality_autoderive\<close>
at hand which allow them to register the footprint of operations/attributes, and have commutativity
lemmas such as the above derived automatically.\<close>

subsection\<open>Data Structures\<close>

text\<open>The following is the core datastructure that this theory maintains:
A record binding an attribute/operation on a record to its footprint.\<close>

ML\<open>
  type locality_entry = {
    const_name: string,  \<comment>\<open>The name of the attribute/operation\<close>
    const_type: string,  \<comment>\<open>"attribute" or "operation"\<close>
    footprint: string list,  \<comment>\<open>The list of record fields affecting the attribute/operation\<close>
    args : int, \<comment>\<open>The number of arguments to the attribute/operation\<close>
    idx: int,   \<comment>\<open>The index of the argument that matches the target record.
                   This is not redundant since a term may be an attribute in
                   more than one way if there are repeating argument types.\<close>
    sp : simproc option 
  }

  \<comment>\<open>Type used to store pairs of attributes/operations that operate on disjoint footprints\<close>
  type disjoint_pair = string * string

  \<comment>\<open>Global data for tracking footprints of operations\<close>
  structure RecordLocalityData = Generic_Data
  (
    type T = (locality_entry list Symtab.table *  \<comment>\<open>record-indexed table of footprint data\<close>
              disjoint_pair list Symtab.table);   \<comment>\<open>record-indexed table of names of disjoint attributes/operations\<close>
    val empty = (Symtab.empty, Symtab.empty);
    fun merge ((tA0, tA1), (tB0, tB1)) =
       (Symtab.merge_list (fn ({const_name=t0, ...},{const_name=t1,...}) => t0 = t1) (tA0, tB0),
        Symtab.merge_list (fn (t0,t1) => t0 = t1) (tA1, tB1));
  );

  \<comment>\<open>Register the footprint for a new attribute/operation.\<close>
  fun add_record_locality_entry_generic ctxt (rec_name : string) (ty : string) (f : string)
    (footprint : string list) (args : int) (idx : int) (sp : simproc option) =
    let
      val entry = {const_name = f, const_type=ty, footprint=footprint, args=args, idx=idx, sp=sp}
      val g = Symtab.map_default (rec_name, []) (fn ls => ls @ [entry])
      val _ = Pretty.text "Registering footprint" @ [Pretty.brk 1, Pretty.list "[" "]" (List.map Pretty.str footprint), Pretty.brk 1]
              @ Pretty.text "for constant" @ [Pretty.brk 1, Pretty.str f, Pretty.brk 1]
              @ Pretty.text "for record" @ [Pretty.brk 1, Pretty.str rec_name] |> Pretty.block
              |> locality_pretty_trace ctxt 1
    in
      RecordLocalityData.map (g |> apfst)
    end

  fun order_pair (a,b) = if a < b then (a,b) else (b,a)

  \<comment>\<open>Generic context transformation for registerins a disoint pair of attributes/operations on a record.\<close>
  fun add_record_disjoint_pair_generic (rec_name : string) (cA : string) (cB : string)
    : Context.generic -> Context.generic =
    let
      val (cA, cB) = order_pair (cA, cB)
      val f = Symtab.map_default (rec_name, []) (fn ls => ls @ [(cA, cB)])
    in
      RecordLocalityData.map (f |> apsnd)
    end

  \<comment>\<open>Theory transformation adding a new footprint entry\<close>
  fun add_record_locality_entry ctxt (rec_name : string) (ty : string) (f : string)
    (footprint : string list) (args : int) (idx : int) (sp : simproc option) : local_theory -> local_theory =
    Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none} 
       (K (add_record_locality_entry_generic ctxt rec_name ty f footprint args idx sp))

  \<comment>\<open>Theory transformation adding a new disjoint pair\<close>
  fun add_record_disjoint_pair (rec_name : string) (cA : string) (cB : string) =
    Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none}
       (K (add_record_disjoint_pair_generic rec_name cA cB))

  \<comment>\<open>Lookup the footprint and disjointness data associated with a record, each as an association list.\<close>
  val get_record_locality_data_generic : Context.generic ->
      (Symtab.key * locality_entry) list *
      (Symtab.key * disjoint_pair) list
   = RecordLocalityData.get #> (apfst Symtab.dest_list o apsnd Symtab.dest_list)

  val get_record_locality_data = Context.Proof #>  get_record_locality_data_generic
  val get_record_locality_data_raw_generic = RecordLocalityData.get

  \<comment>\<open>Get list of records that we manage any footprint information about\<close>
  val get_registered_records = Context.Proof #> RecordLocalityData.get #> fst #> Symtab.keys
  
  \<comment>\<open>Lookup footprint data for record\<close>
  fun get_record_locality_data_for_record_generic r ctxt :
    (locality_entry list * disjoint_pair list) option = 
    let
      val (consts, pairs) = get_record_locality_data_raw_generic ctxt
       val (x_opt, y_opt) = (Symtab.lookup consts r, Symtab.lookup pairs r)
    in
      case (x_opt, y_opt) of
        (NONE, NONE) => NONE
       | _ => SOME (Option.getOpt (x_opt, []), Option.getOpt (y_opt, []))
    end

  fun get_record_locality_data_for_record r = Context.Proof #> get_record_locality_data_for_record_generic r

  \<comment>\<open>Lookup all registered attributes for a record\<close>
  fun get_attributes ctxt = ctxt
     |> get_record_locality_data
     |> fst
     |> List.filter (fn (_, e : locality_entry) => #const_type e = "attribute")

  \<comment>\<open>Lookup all registered operations for a record\<close>
  fun get_operations ctxt = ctxt
     |> get_record_locality_data
     |> fst
     |> List.filter (fn (_, e : locality_entry) => #const_type e = "operation")

  fun get_record_locality_entry_generic (r : string) (c : string) ctxt =
    case get_record_locality_data_for_record_generic r ctxt of
       NONE => NONE
     | SOME (consts, _) =>
         List.find (fn {const_name = c0, ...} => c0 = c) consts

  fun get_record_locality_entry (r : string) (c : string) =
     Context.Proof #> get_record_locality_entry_generic r c

  val has_record_locality_entry_generic = Option.isSome ooo get_record_locality_entry_generic

  fun prepare_rec_name (ctxt : Proof.context) (rec_name : string) =
    let
      (* Assumes a type of the form (_, _,..., _) ty and replaces the dummys with free type variables *)
      fun prepare_typ ty =
        let
          val (base, args) = Term.dest_Type ty
          val argnum = length args
          val tvars = Library.map_range (fn i => (TVar (("?'a", i), []))) argnum
        in
          Type (base, tvars)
        end
      val rec_ty = rec_name
        |> Proof_Context.read_type_name {proper = true, strict = false} ctxt
        |> prepare_typ
      val (rec_name_full, _) = rec_ty |> dest_Type
    in
       (rec_ty, rec_name_full)
    end

  \<comment>\<open>Pretty printing helper\<close>
  fun pretty_locality_entry ctxt rec_name {const_name=c, const_type=_, footprint=fp, idx=idx, args=_, sp=_} =
    let val (rec_ty, _) = prepare_rec_name ctxt rec_name in
      Pretty.text "On record"
       @ [Pretty.brk 1, Syntax.pretty_typ ctxt rec_ty]
       @ Pretty.text "," @ [Pretty.brk 1,
       Syntax.pretty_term ctxt (Syntax.parse_term ctxt c), Pretty.brk 1]
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
                  |> Option.map fst |> curry Option.getOpt) []
         val _ = List.map (pretty_locality_entry ctxt rec_name) data |> Pretty.chunks |> Pretty.writeln
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

  fun list_prod xs = List.map (fn x => List.map (rpair x) xs) #> Library.flat

  \<comment>\<open>Lookup pairs of disjoint attributes/operators for a given record\<close>
  fun find_disjoint_pairs_for_record_generic r ctxt =
    case get_record_locality_data_for_record_generic r ctxt of
      NONE => []
    | SOME (consts, _) => (let
        \<comment>\<open>Go through all pairs and check if they are disjoint\<close>
        val const_pairs = list_prod consts consts
        val disjoint_pairs = List.filter
          (fn (({const_name = cA, footprint = footprintA, ...},
                {const_name = cB, footprint = footprintB, ...})) =>
                  cA < cB andalso
                  List.length (Library.inter (op =) footprintA footprintB) = 0)
          const_pairs
        in
          disjoint_pairs
        end)

  \<comment>\<open>Checks if there is a commutativity lemma registered for constants \<^verbatim>\<open>cA\<close> and \<^verbatim>\<open>cB\<close>
     operating on record \<^verbatim>\<open>r\<close>.\<close>
  fun has_commutativity_lemma_generic ctxt r cA cB =
    let
      val pairs_with_lemma = (get_record_locality_data_for_record_generic r ctxt
        |> Option.map snd |> curry Option.getOpt) []
      val (cA, cB) = order_pair (cA, cB)
    in
      Library.member (op =) pairs_with_lemma (cA, cB)
    end

  \<comment>\<open>List all pairs of constants operating on a given record and having disjoint footprints,
     for which no commutativity lemma has not yet been proved.\<close>
  fun find_disjoint_pairs_without_commutativity_lemma_generic r ctxt =
    let
      val disjoint_pairs = find_disjoint_pairs_for_record_generic r ctxt
    in
      List.filter (fn ({const_name=cA, const_type=tyA, ...},{const_name=cB, const_type=tyB, ...}) =>
        (tyA = "operation" orelse tyB = "operation") andalso
        (not (has_commutativity_lemma_generic ctxt r cA cB)))
        disjoint_pairs
    end

  fun string_to_identifier s = s
    |> String.explode |> List.map (fn c => if c = #" " orelse c = #"." then #"_" else c)
                      |> List.map (fn c => if c = #"'" then #"P" else c)
    |> List.filter (fn c => Char.isAlphaNum c orelse c = #"_")
    |> String.implode

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
  fun register_locality_attr_simproc_name rec_name c i =
    (rec_name |> string_to_identifier) ^ "_local_attr_" ^ c ^ "_" ^ (Int.toString i) ^ "_simproc"

  fun default_named_theorems_for_record (rec_name : string) =
    (rec_name |> string_to_identifier) ^ "_locality_facts"

  fun commutativity_theorems_for_record (rec_name : string) =
    (rec_name |> string_to_identifier) ^ "_commutativity_facts"

  fun strip_prefix (prefix : string) (s : string) : string option =
     if String.isPrefix prefix s then
        SOME (String.extract (s, size prefix, NONE))
     else
        NONE

  val strlist_to_str = String.concatWith ", "
  fun field_update rec_name field = rec_name ^ "." ^ "update_" ^ field
  fun dest_field_update const = strip_prefix "update_" const

  fun fieldlist_to_str fs = "[" ^ (strlist_to_str fs) ^ "]"

  fun is_update_commutativity_thm (t : thm) =
    let
      val (lhs, rhs) = t |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      val lhs_hd = lhs |> Term.strip_comb |> fst |> Term.dest_Const |> fst |> Long_Name.base_name
      val rhs_hd = rhs |> Term.strip_comb |> fst |> Term.dest_Const |> fst |> Long_Name.base_name
    in
      case (dest_field_update lhs_hd, dest_field_update rhs_hd) of
        (SOME f0, SOME f1) => f0 <> f1
       | _ => false
      end handle TERM _ => false

   fun check_create_commutativity_theorems (rec_name : string) ctxt =
     case check_create_named_theorems (commutativity_theorems_for_record rec_name) ctxt of
        (false, name', ctxt) => (name', ctxt)
      | (true, name', ctxt') => let
         (* Lookup built-in theorems for record and filter update commutativity relations *)
         val record_simps = lookup_thms ctxt' (rec_name ^ ".record_simps")
         val update_commutativity_facts = List.filter is_update_commutativity_thm record_simps
         val ctxt'' = fold (fn t => Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none} (Named_Theorems.add_thm name' t |> K))
                           update_commutativity_facts ctxt'
         in
           (name', ctxt'')
         end

  fun unpack_attributes_default (ctxt : Proof.context) (rec_name : string) attribs_opt =
     (("unpack: " ^ rec_name |> tracing);
     tap (fn _ => "done") (case attribs_opt of
         SOME attribs => attribs
       | NONE => let val default_thms = default_named_theorems_for_record rec_name
                     val attr = Token.explode0 (Thy_Header.get_keywords' ctxt) default_thms
                 in [attr] end))

  exception CommutativitySkipException

  fun prove_commutativity_lemma_for_disjoint_operators  attribs_opt
      (rec_name : string) (cA : string) (cB : string) (ctxt : Proof.context)  =
    (let
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val (_, _, ctxt) = check_create_named_theorems (default_named_theorems_for_record rec_name) ctxt
      val (pA, pB) = (Syntax.read_term ctxt cA, Syntax.read_term ctxt cB)
      val _ =
         [Pretty.str "Auto-deriving commutativity",
          Syntax.pretty_term ctxt pA,
          Pretty.str "\<longleftrightarrow>",
          Syntax.pretty_term ctxt pB,
          Pretty.enclose "(" ")" [Pretty.str "on", Pretty.brk 1, Syntax.pretty_typ ctxt rec_ty],
          Pretty.str "..."] |> Pretty.breaks |> Pretty.block |> locality_pretty_trace ctxt 0

      (* Get rid of positioning information that's inherent in p_name since they
         are produced by Parse.typ and Parse.term, respectively. Otherwise, the proposition-strings
         built below won't be recognized. *)
      val (cA, cB) = (cA, cB) |> ((Syntax.read_input #> Input.string_of) |> apply2)
      (* Check that the given term is indeed a function on the given record *)
      val (_, num_argsA, rec_namexA) =  dest_fun_term ctxt rec_ty pA |> Option.valOf
      val (_, num_argsB, rec_namexB) =  dest_fun_term ctxt rec_ty pB |> Option.valOf

      fun arglist_with_prefix prefix num idx x =
            make_arglist_with_prefix prefix num
         |> list_set_nth idx x
         |> String.concatWith " "
      val argsA = arglist_with_prefix "argsA" num_argsA rec_namexA
      val argsB = arglist_with_prefix "argsB" num_argsB rec_namexB

      fun call_with_special_arg c prefix num idx x =
         c ^ " " ^ arglist_with_prefix prefix num idx ("(" ^ x ^ ")")
      val callA = call_with_special_arg cA "argsA" num_argsA rec_namexA
      val callB = call_with_special_arg cB "argsB" num_argsB rec_namexB

      (* Build statements of locality lemmas *)
      val commutativity_str =
          "\<And>" ^ argsA ""  ^ " " ^ argsB ""  ^ " R . " ^ callA (callB "R") ^ " = " ^ callB (callA "R")
      val commutativity_stm = commutativity_str |> Syntax.read_prop ctxt
        handle ERROR _ => (let val pre_term = Syntax.parse_term ctxt commutativity_str in
          ([Pretty.text "Commutativity proposition" |> Pretty.block,
            Syntax.pretty_term ctxt pre_term,
            Pretty.text "is ill-typed, probably because of mismatching type arguments in polymorphic record -- ignore" |> Pretty.block]
            |> Pretty.breaks |> Pretty.block |> Pretty.string_of |> warning;
           raise CommutativitySkipException) end)

      val commutativity_thm_name = (rec_name |> string_to_identifier) ^ "_" ^ cA ^ "_" ^ cB ^ "_commute"

      fun after_qed (named_thm_list_opt) name (cont : Proof.context -> Proof.context) thms ctxt =
        let val thms = thms |> flat
          val _ = "after qed" |> tracing
          val attribs = unpack_attributes_default ctxt rec_name attribs_opt
           |> List.map (Attrib.check_src ctxt)
        in ctxt
           |> (case named_thm_list_opt of
               SOME n => fold (fn t => Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none} (Named_Theorems.add_thm n t |> K)) thms
             | NONE => I)
           |> Local_Theory.note (((Binding.name name), []), thms) |> snd
           |> Local_Theory.note ((Binding.empty,attribs), thms) |> snd
           |> cont
        end
      val cA_id = string_to_identifier cA
      val cB_id = string_to_identifier cB

      val cA_local = register_locality_op_local_action_thm_name rec_name cA_id
      val cB_local = register_locality_op_local_action_thm_name rec_name cB_id
      val cA_comm = register_locality_op_commutativity_thm_name rec_name cA_id
      val cB_comm = register_locality_op_commutativity_thm_name rec_name cB_id

      fun get_thm (ctxt : Proof.context) = Facts.named #> Proof_Context.get_fact_single ctxt

      val cA_local_thm = cA_local |> get_thm ctxt
      val cB_local_thm = cB_local |> get_thm ctxt

      val commutativity_thms = Named_Theorems.check ctxt
         (commutativity_theorems_for_record rec_name, Position.none)

      fun start_core_proof ctxt cont = (ctxt
           |> Proof.theorem NONE (after_qed (SOME commutativity_thms) commutativity_thm_name cont) [map (fn t => (t,[])) [commutativity_stm]]
           |> apply_context_tactic (K all_tac)
           |> apply_context_tactic (fn ctxt => CONVERSION (Conv.bottom_rewrs_conv [cA_local_thm RS eq_reflection] ctxt) 1)
           |> apply_context_tactic (fn ctxt => CONVERSION (Conv.bottom_rewrs_conv [cB_local_thm RS eq_reflection] ctxt) 1)
           |> apply_txt ctxt ("simp only: " ^ cA_comm ^ " " ^ cB_comm)
           |> apply_txt ctxt ("simp")
           |> Proof.global_done_proof)
           handle ERROR e =>
            ([[Pretty.str "Something went wrong proving derived commutativity theorem for",
               Syntax.pretty_term ctxt pA,
               Pretty.str "and",
               Syntax.pretty_term ctxt pB,
               Pretty.str "."] |> Pretty.breaks |> Pretty.block,
              Pretty.str "This can happen if one of the operators is an abbreviation, but otherwise shouldn't.",
              ([Pretty.str "This is what I tried to prove (see",
                Pretty.here \<^here> |> List.last, Pretty.str "for the ML code)"] |> Pretty.breaks |> Pretty.block),
              Syntax.pretty_term ctxt commutativity_stm,
              Pretty.str "Original error message:",
              Pretty.str e] |> Pretty.chunks |> Pretty.string_of |> warning; raise CommutativitySkipException)
    in
      start_core_proof ctxt (add_record_disjoint_pair rec_name cA cB)
    end) handle CommutativitySkipException => ctxt

  fun prove_commutativity_lemma_for_disjoint_operator_and_attribute attribs_opt
      (rec_name : string) (c_op : string) (c_attr : string)  (rec_namex_attr : int) (ctxt : Proof.context) =
    (let                                       
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val (_, _, ctxt) = check_create_named_theorems (default_named_theorems_for_record rec_name) ctxt
      val (p_op, p_attr) = (Syntax.read_term ctxt c_op, Syntax.read_term ctxt c_attr)
      val _ =
         [Pretty.str "Auto-deriving commutativity",
          Syntax.pretty_term ctxt p_op,
          Pretty.str "\<longleftrightarrow>",
          Syntax.pretty_term ctxt p_attr,
          Pretty.enclose "(" ")" [Pretty.str "index", Pretty.brk 1, Pretty.str (rec_namex_attr |> Int.toString)],
          Pretty.enclose "(" ")" [Pretty.str "on", Pretty.brk 1, Syntax.pretty_typ ctxt rec_ty],
          Pretty.str "..."] |> Pretty.breaks |> Pretty.block |> locality_pretty_trace ctxt 0

      (* Get rid of positioning information that's inherent in p_name and rec_name since they
         are produced by Parse.typ and Parse.term, respectively. Otherwise, the proposition-strings
         built below won't be recognized. *)
      val (c_op, c_attr) = (c_op, c_attr) |> ((Syntax.read_input #> Input.string_of) |> apply2)
      (* Check that the given term is indeed a function on the given record *)
      val (_, num_args_op, rec_namex_op) = dest_fun_term ctxt rec_ty p_op |> Option.valOf
      val (_, num_args_attr, rec_namexs_attr) = dest_attr_term ctxt rec_ty p_attr |> Option.valOf

      val _ = if not (Library.member (op =) rec_namexs_attr rec_namex_attr) then
        error ("Illegal argument index " ^ (rec_namex_attr |> Int.toString) ^
               " passed to prove_commutativity_lemma_for_disjoint_operator_and_attribute")
        else ()

      fun arglist_with_prefix prefix num idx x =
            make_arglist_with_prefix prefix num
         |> list_set_nth idx x
         |> String.concatWith " "
      val args_op = arglist_with_prefix "args_op" num_args_op rec_namex_op
      val args_attr = arglist_with_prefix "args_attr" num_args_attr rec_namex_attr

      fun call_with_special_arg c prefix num idx x =
         c ^ " " ^ arglist_with_prefix prefix num idx ("(" ^ x ^ ")")
      val call_op = call_with_special_arg c_op "args_op" num_args_op rec_namex_op
      val call_attr = call_with_special_arg c_attr "args_attr" num_args_attr rec_namex_attr

      (* Build statements of locality lemmas *)
      val commutativity_str =
          "\<And>" ^ args_op ""  ^ " " ^ args_attr ""  ^ " R . " ^ call_attr (call_op "R") ^ " = " ^ call_attr "R"

      (* The commutativity relation might be ill-typed because for polymorphic types, we only index
         by their base type, regardless of the arguments. In case of a type mismatch, print a warning
         and skip the pair. *)
      val commutativity_stm = commutativity_str |> Syntax.read_prop ctxt
        handle ERROR _ => (let val pre_term = Syntax.parse_term ctxt commutativity_str in
          ([Pretty.text "Commutativity proposition" |> Pretty.block,
            Syntax.pretty_term ctxt pre_term,
            Pretty.text "is ill-typed, probably because of mismatching type arguments in polymorphic record -- ignore" |> Pretty.block]
            |> Pretty.breaks |> Pretty.block |> Pretty.string_of |> warning;
           raise CommutativitySkipException) end)
      val commutativity_thm_name = (rec_name |> string_to_identifier) ^ "_" ^ c_op ^ "_" ^ c_attr ^ "_" ^
         (rec_namex_attr |> Int.toString) ^ "_commute"

      fun after_qed (named_thm_list_opt) name (cont : Proof.context -> Proof.context) thms ctxt =
        let val thms = thms |> flat
          val _ = "after qed2" |> tracing
          val attribs = unpack_attributes_default ctxt rec_name attribs_opt
           |> List.map (Attrib.check_src ctxt)
        in ctxt
           |> (case named_thm_list_opt of
               SOME n => fold (fn t => Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none} (Named_Theorems.add_thm n t |> K)) thms
             | NONE => I)
           |> Local_Theory.note (((Binding.name name), []), thms) |> snd
           |> Local_Theory.note ((Binding.empty,attribs), thms) |> snd
           |> cont
        end

      val c_op_id = string_to_identifier c_op
      val c_attr_id = string_to_identifier c_attr

      val c_op_local = register_locality_op_local_action_thm_name rec_name c_op_id
      val c_attr_cancel_core = register_locality_attr_cancellation_thm_name rec_name c_attr_id rec_namex_attr
      val c_attr_cancel_thms = register_locality_attr_cancellation_thm_list_name rec_name c_attr_id rec_namex_attr
      val c_attr_cancel_thms = Named_Theorems.check ctxt (c_attr_cancel_thms, Position.none)

      fun do_proof ctxt cont = (ctxt
           |> Proof.theorem NONE (after_qed (SOME c_attr_cancel_thms) commutativity_thm_name cont) [map (fn t => (t,[])) [commutativity_stm]]
           |> apply_method (SIMPLE_METHOD all_tac)
           |> apply_txt ctxt ("subst " ^ c_op_local)
           |> apply_txt ctxt ("simp add: " ^ c_attr_cancel_core)
           |> Proof.global_done_proof)
           handle ERROR e =>
            ([[Pretty.str "Something went wrong proving derived commutativity theorem for",
               Syntax.pretty_term ctxt p_op,
               Pretty.str "and",
               Syntax.pretty_term ctxt p_attr,
               Pretty.str "."] |> Pretty.breaks |> Pretty.block,
              Pretty.str "This can happen if one of the operators is an abbreviation, but otherwise shouldn't.",
              ([Pretty.str "This is what I tried to prove (see",
                Pretty.here \<^here> |> List.last, Pretty.str "for the ML code)"] |> Pretty.breaks |> Pretty.block),
              Syntax.pretty_term ctxt commutativity_stm,
              Pretty.str "Original error message:",
              Pretty.str e] |> Pretty.chunks |> Pretty.string_of |> warning; raise CommutativitySkipException)
    in
      do_proof ctxt (add_record_disjoint_pair rec_name c_op c_attr)
    end) handle CommutativitySkipException => ctxt
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

  See \<^file>\<open>AutoLocality_Test0.thy\<close> for an example of the resulting simproc \<^verbatim>\<open>locality_cancel\<close>.
\<close>

ML\<open>
  type 'a op_term_with_gap = 'a * (term * term list * term list)

  \<comment>\<open>Recursively zooms into an argument of a term, according to a picker function, retaining
     the previous and following arguments.\<close>
  fun strip_comb_iter (picker : term -> term list -> (int * 'a) option) (t : term) : 'a op_term_with_gap list * term =
    let
      fun core (acc : 'a op_term_with_gap list) (t : term) =
         let
           val (head, args) = t |> Term.strip_comb
           val iter = picker head args
         in
           case iter of
              NONE => (acc, t)
            | SOME (idx, data) => core (acc @ [(data, (head, List.take (args, idx), 
                   List.drop (args, idx+1)))]) (List.nth (args, idx))
         end
    in
      core [] t
    end

  \<comment>\<open>This is a left inverse to \<^verbatim>\<open>strip_comb_iter\<close>\<close>
  fun recombine_decomposed_comb ([], body) = body
    | recombine_decomposed_comb (((_, (head, pre, suf)) :: inner), body) =
        let val r = recombine_decomposed_comb (inner, body) in
          Term.list_comb (head, pre @ [r] @ suf)
        end
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
  \<comment>\<open>Term picker for use with \<^verbatim>\<open>strip_comb_iter\<close> which zooms into an operation on a record
  for which footprint data has been defined. For example, if \<^verbatim>\<open>f a b r c d\<close> is an operation
  on \<^verbatim>\<open>r :: 'rec\<close> whose type is a datatype record \<^verbatim>\<open>'rec\<close>, and if \<^verbatim>\<open>f\<close> has footprint data 
  registered for \<^verbatim>\<open>'rec\<close>, then this picker would select argument 2 (which is \<^verbatim>\<open>r\<close>) to zoom into.\<close>
  fun locality_picker (ctxt : Proof.context) (rec_name : string) (head : term) (_ : term list) =
    (let
       val _ = [Pretty.str "Locality simproc, check:", Pretty.str rec_name, Syntax.pretty_term ctxt head]
               |> Pretty.breaks |> Pretty.block |> locality_pretty_trace ctxt 1
       val head_str = head |> Term.dest_Const |> fst |> Long_Name.base_name
       val lookup =
         case get_record_locality_entry rec_name head_str ctxt of
           SOME e => SOME e
         | NONE => (* Check if we're looking at an in-built update function *)
             case dest_field_update head_str of
                NONE => NONE
              | SOME field => SOME ({ const_name = head_str, const_type = "operation",
                                args = 2, footprint = [field], idx = 1, sp = NONE } : locality_entry)
       in case lookup of
          NONE => (Pretty.text ("Could not find entry " ^ head_str ^ " in footprint db for " ^ rec_name)
                   |> Pretty.block |> locality_pretty_trace ctxt 1; NONE)
        | SOME e => (Pretty.text "Found locality entry with footprint"
                     @ [Pretty.brk 1, Pretty.list "(" ")" (List.map Pretty.str (#footprint e))]
                     |> Pretty.block |> locality_pretty_trace ctxt 1;
                    SOME (#idx e, e))
       end)
    handle TERM _ => NONE

  fun disjoint_footprint (fpA : string list) (fpB : string list) =
     length (Library.inter (op =) fpA fpB) = 0

  fun disjoint_entries (e : locality_entry) (f : locality_entry) =
     disjoint_footprint (#footprint e) (#footprint f)

  fun merge_footprints (fpA : string list) (fpB : string list) =
    Library.merge (op =) (fpA, fpB)

  fun lift_redundant_operations_core front back _ [] = (front, back)
   | lift_redundant_operations_core front back fp ((e : locality_entry, f) :: efs) =
        if disjoint_footprint fp (#footprint e) then
           lift_redundant_operations_core (front @ [(e,f)]) back fp efs
        else
           lift_redundant_operations_core front (back @ [(e,f)]) (merge_footprints fp (#footprint e)) efs

  \<comment>\<open>If the toplevel term is an attribute on a record, look for operations applied to the
  record argument that can be hoisted out and cancelled.

  For example, if \<^verbatim>\<open>attr ?x (?r :: 'rec) ?y\<close> is an attribute on record \<^verbatim>\<open>'rec\<close> with footprint
  \<^verbatim>\<open>{a,b}\<close>, say, \<^verbatim>\<open>opA ?r ?z\<close> is an operation on \<^verbatim>\<open>'rec\<close> with footprint \<^verbatim>\<open>{a, c}\<close>, and \<^verbatim>\<open>opB ?w ?r\<close>
  is another operation on \<^verbatim>\<open>'rec\<close> with footprintb \<^verbatim>\<open>{d, e}\<close>, then \<^verbatim>\<open>opB\<close> can be hoisted in the
  term \<^verbatim>\<open>attr x (opA (opB w r) z) y\<close>, giving \<^verbatim>\<open>attr x (opB w (opA r z) y\<close>.

  Note if \<^verbatim>\<open>opB\<close> had footprint \<^verbatim>\<open>{c, d}\<close>, say, then it could not be hoisted because it does not
  commute with \<^verbatim>\<open>opA\<close>; hence, as we descend into the term, we have to maintain the union of the
  footprints of terms we looked at.\<close>
  fun hoist_redundant_operations_core
     ((e : locality_entry as {const_type = "attribute", ...}, f) :: inner) =
        let val (front, back) = lift_redundant_operations_core [] [] (#footprint e) inner in
             (length front = 0, (e,f) :: (front @ back))
        end
    | hoist_redundant_operations_core x = (true, x)

  fun hoist_redundant_operations (x,y) =
    let val (action, xp) = hoist_redundant_operations_core x in
      (action, (xp, y))
    end

  \<comment>\<open>simproc identifying cancellable or hoistable subexpressions in a term, and
     eliminating them.\<close>
  fun locality_cancellation_simproc rec_name attr_name attr_idx ctxt ctm =
    let
       val _ =
         [Pretty.text "Locality simproc for"
          @ [Pretty.brk 1, Pretty.list "(" ")" [Pretty.str rec_name, Pretty.str attr_name],
             Pretty.brk 1, Pretty.str "called"] |> Pretty.block,
          [Pretty.str "Term:", Pretty.brk 1, Syntax.pretty_term ctxt (Thm.term_of ctm)] |> Pretty.block]
          |> Pretty.chunks |> Pretty.writeln
       val ctxt' = Simplifier.clear_simpset ctxt
       val lookup_facts = (fn s => (s, Position.none)) #> Named_Theorems.check ctxt #> Named_Theorems.get ctxt

       (* Identify redundant operations in the body of the attribute and hoist them out *)
       val (no_op, ctm_decomposed_hoisted) = ctm
         |> Thm.term_of
         \<comment>\<open>Build up 'telescope' of operations on \<^verbatim>\<open>rec_name\<close>\<close>
         |> strip_comb_iter (locality_picker ctxt rec_name)
         |> hoist_redundant_operations

    in if no_op then NONE else let

       val ctm_hoisted = ctm_decomposed_hoisted
         |> recombine_decomposed_comb
         |> Thm.cterm_of ctxt

       val _ = [ Pretty.str "Hoisted:", Pretty.brk 1, Syntax.pretty_term ctxt (Thm.term_of ctm_hoisted)]
         |> Pretty.block |> locality_pretty_trace ctxt 1

       (* Simplifying the original and hoisted term should lead to the same result. The resulting
          equalities are connected to give an equality between the original and the hoisted term. *)

      val commutativity_thms = Named_Theorems.check ctxt
         (commutativity_theorems_for_record rec_name, Position.none)

       val locality_facts = commutativity_thms |> lookup_facts
       val ctm_reduce_eq = Simplifier.rewrite (ctxt' |> Simplifier.add_simps locality_facts) ctm
       val ctm_hoisted_reduce_eq =
         Simplifier.rewrite (ctxt' |> Simplifier.add_simps locality_facts) ctm_hoisted RS @{thm Pure.symmetric}

       val _ = [ Pretty.str "Simplification original:", Pretty.brk 1,
                 Syntax.pretty_term ctxt (Thm.prop_of ctm_reduce_eq)]
         |> Pretty.block |> locality_pretty_trace ctxt 1
       val _ = [ Pretty.str "Simplification hoisted:", Pretty.brk 1,
                 Syntax.pretty_term ctxt (Thm.prop_of ctm_hoisted_reduce_eq)]
         |> Pretty.block |> locality_pretty_trace ctxt 1

       val ctm_to_ctm_hoisted_eq = ctm_hoisted_reduce_eq RS (ctm_reduce_eq RS @{thm Pure.transitive})

       val _ = [ Pretty.str "Original -> Hoisted:",
                 Pretty.brk 1, Syntax.pretty_term ctxt (Thm.prop_of ctm_to_ctm_hoisted_eq)]
         |> Pretty.block |> locality_pretty_trace ctxt 1

       (* Now, cancel the hoisted operations. It's important that we don't pass the locality_factss here,
          as that might undo the hoisting. *)
       val cancellation_facts = register_locality_attr_cancellation_thm_list_name rec_name attr_name attr_idx |> lookup_facts
       val _ = "Cancellation facts:" |> tracing
       val _ = List.map (Thm.prop_of #> Syntax.pretty_term ctxt #> Pretty.writeln) cancellation_facts
       val _ = "Done" |> tracing
       val ctm_hoisted_cancel_eq = Simplifier.rewrite (ctxt' |> Simplifier.add_simps cancellation_facts) ctm_hoisted
    in
       SOME (ctm_hoisted_cancel_eq RS (ctm_to_ctm_hoisted_eq RS @{thm Pure.transitive}))
    end end
        handle ERROR e => (Pretty.text "locality_cancellation_simproc for"
                            @ [Pretty.brk 1, Pretty.str rec_name, Pretty.brk 1, Pretty.str attr_name, Pretty.brk 1]
                            @ Pretty.text "failed with error" @ [Pretty.brk 1, Pretty.str e]
                          |> Pretty.block |> Pretty.string_of |> warning; NONE)

  fun arglist num idx x =
       make_arglist num
    |> list_set_nth idx x
    |> String.concatWith " "

  fun make_locality_simproc_pattern attr_name num_args idx =
     attr_name ^ " " ^ arglist num_args idx "(f X)"

  fun make_locality_simproc ctxt rec_name attr_name num_args idx : simproc =
    let
      val _ = Pretty.text ("Creating simproc for attribute " ^ attr_name ^ " on record " ^ rec_name)
            |> Pretty.block |> locality_pretty_trace ctxt 0
      val simproc_name = (register_locality_attr_simproc_name rec_name attr_name idx)
      val ptrn_str = make_locality_simproc_pattern attr_name num_args idx
      val ptrn = Syntax.read_term ctxt ptrn_str
    in
       Simplifier.make_simproc ctxt {name = simproc_name, kind = Simplifier.Simproc, identifier = [],
          lhss = [ptrn], proc = K (locality_cancellation_simproc rec_name attr_name idx) }
    end

  \<comment>\<open>End of the simproc code\<close>

  fun state_locality_for_op attribs_opt (rec_name : string) (p_name: string)
    (footprint: string list) (with_proof : bool) (ctxt : Proof.context)  =
    let
      (* Lookup fields from record *)
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val (_, _, ctxt) = check_create_named_theorems (default_named_theorems_for_record rec_name) ctxt
      val fields = get_fields rec_name ctxt

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

      val p_term = Syntax.read_term ctxt p_name

      (* Get rid of positioning information that's inherent in p_name and rec_name since they
         are produced by Parse.typ and Parse.term, respectively. Otherwise, the proposition-strings
         built below won't be recognized. *)
      val p_name = Syntax.read_input p_name |> Input.string_of
      val rec_name = Syntax.read_input rec_name |> Input.string_of
      (* Check that the given term is indeed a function on the given record *)
      val (_, num_args, rec_namex) =  dest_fun_term ctxt rec_ty p_term |> Option.valOf
      val p_id = string_to_identifier p_name

      fun arglist_with x =
            make_arglist num_args
         |> list_set_nth rec_namex x
         |> String.concatWith " "
      val argsA = arglist_with "R"
      fun argsB field = arglist_with ("(" ^ field_update rec_name field ^ " f R)")

      (* Build statements of locality lemmas *)
      fun commutativity_str (prop : string) (field : string) =
          "\<And>f " ^ argsA ^ " . " ^ prop ^ " " ^ argsB field ^ " = " ^
                               (field_update rec_name field) ^ " f (" ^ prop ^ " " ^ argsA ^ ")"
      fun get_commutativity_stm prop field = commutativity_str prop field |> Syntax.read_prop ctxt
      val commutativity_stms = List.map (get_commutativity_stm p_name) disjoint_fields

      (* Build statements of disjointness lemmas *)
      fun disjoint_str (prop : string) (field : string) =
         let val field_proj = rec_name ^ "." ^ field in
           "\<And>f " ^ argsA ^ ". " ^ field_proj ^ " (" ^ prop ^ " " ^ argsA ^ ") = " ^
                               field_proj ^ " R"
         end
      fun get_disjoint_stm prop field = disjoint_str prop field |> Syntax.read_prop ctxt
      val disjoint_stms = List.map (get_disjoint_stm p_name) disjoint_fields

      fun make_iterated_field_update rec_name fields_with_vals arg =
         fold (fn (f,v) => fn s => (field_update rec_name f) ^ " (\<lambda>_. " ^ v ^ ") (" ^ s ^ ")")
              fields_with_vals
              ("(" ^ arg ^ ")")

      fun field_proj field = rec_name ^ "." ^ field

      fun make_noop_iterated_field_update fields arg =
         let
             val fields_with_vals = List.map (fn f => (f, field_proj f ^ " (" ^ arg ^ ")")) fields
         in
            make_iterated_field_update rec_name fields_with_vals arg
         end

      (* Build statements of 'local action' lemmas *)
      fun local_action_str (prop : string) =
         let
             fun new_field_val f = field_proj f ^ "( " ^ prop ^ " " ^ argsA ^ ")"
             val footprint_with_vals = List.map (fn f => (f, new_field_val f)) footprint
             val field_updates = make_iterated_field_update rec_name footprint_with_vals "R"
         in
           "\<And>f " ^ argsA ^ ". " ^ prop ^ " " ^ argsA ^ " = " ^ field_updates
         end
      val local_action_stm = local_action_str p_name |> Syntax.read_prop ctxt

      val commutativity_thm_name = register_locality_op_commutativity_thm_name rec_name p_id
      val disjointness_thm_name = register_locality_op_disjointness_thm_name rec_name p_id
      val local_action_thm_name = register_locality_op_local_action_thm_name rec_name p_id

      fun after_qed (apply_attribs : bool) (named_thm_list_opt) name (cont : Proof.context -> Proof.context) thms ctxt =
        let val thms = thms |> flat
          val _ = "after_qed3" |> tracing
          val attribs = unpack_attributes_default ctxt rec_name attribs_opt
           |> List.map (Attrib.check_src ctxt)
        in ctxt
           |> (case named_thm_list_opt of
               SOME n => fold (fn t => Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none} (fn _ => Named_Theorems.add_thm n t)) thms
             | NONE => I)
           |> Local_Theory.note (((Binding.name name), []), thms) |> snd
           |> (if apply_attribs then
                 (Local_Theory.note ((Binding.empty,attribs), thms) #> snd)
               else
                 I)
           |> cont
        end

      val default_simps =
        let val found_def = is_const_with_def ctxt p_name
            val const_unfold = if found_def then [Thm.def_name p_name] else []
            val _ = if not found_def then
               Pretty.text "Could not find definitional theorem for:" @ [Pretty.brk 1, Pretty.str p_name]
               |> Pretty.block |> locality_pretty_trace ctxt 1 else ()
            val locality_facts = if Option.isSome attribs_opt then [] else [default_named_theorems_for_record rec_name]
            val all_simps = ["Let_def"] @ const_unfold @ locality_facts
        in
          String.concatWith " " all_simps
        end

      val (named_thms, ctxt') = check_create_commutativity_theorems rec_name ctxt

      fun start_core_proof ctxt cont = ctxt
           |> Proof.theorem NONE (after_qed true (SOME named_thms) commutativity_thm_name cont) [map (fn t => (t,[])) commutativity_stms]
           |> apply_method (SIMPLE_METHOD all_tac)
           |> (if with_proof then
                apply_txt ctxt ("(auto simp add: " ^ default_simps ^ ")?")
              else
                I)

      fun derive_locality cont ctxt =
         let val _ =
            [Pretty.str "Autoderive locality theorem: ",
             Syntax.pretty_term ctxt local_action_stm]
            |> Pretty.breaks |> Pretty.block |> locality_pretty_trace ctxt 0 in
           (   ctxt
            |> Proof.theorem NONE (after_qed false NONE local_action_thm_name cont) [map (fn t => (t,[])) [local_action_stm]]
            |> apply_method (SIMPLE_METHOD all_tac)
            |> apply_txt ctxt ("(auto intro: " ^ rec_name ^ ".expand simp add: " ^ disjointness_thm_name ^ ")")
            |> Proof.global_done_proof)
           handle ERROR _ =>
              ([Pretty.str "Something went wrong proving locality theorem: ",
                Syntax.pretty_term ctxt local_action_stm]
               |> Pretty.breaks |> Pretty.block |> Pretty.string_of |> warning; ctxt)
         end

      fun derive_disjointness cont ctxt =
        let val subgoal = p_name ^ " " ^ argsA ^ " = " ^
               p_name ^ " " ^ arglist_with ("(" ^ make_noop_iterated_field_update disjoint_fields "R" ^ ")")
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

    in
       start_core_proof ctxt' (derive_disjointness (derive_locality
        (add_record_locality_entry ctxt' rec_name "operation" p_name footprint num_args rec_namex NONE)))
    end

  fun state_locality_for_attribute attribs_opt (rec_name : string) (p_name: string)
      (footprint: string list) (with_proof : bool) (rec_namex : int) (ctxt : Proof.context)  =
    let
      (* Lookup fields from record *)
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val (_, _, ctxt) = check_create_named_theorems (default_named_theorems_for_record rec_name) ctxt
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

      val p_term = Syntax.read_term ctxt p_name
      (* Get rid of positioning information that's inherent in p_name and rec_name since they
         are produced by Parse.typ and Parse.term, respectively. Otherwise, the proposition-strings
         built below won't be recognized. *)
      val p_name = Syntax.read_input p_name |> Input.string_of
      (* Check that the given term is indeed a function on the given record *)
      val (_, num_args, rec_namexs) =  dest_attr_term ctxt rec_ty p_term |> Option.valOf
      val p_id = string_to_identifier p_name

      val _ = if not (Library.member (op =) rec_namexs rec_namex) then
        error ("Illegal argument index " ^ (rec_namex |> Int.toString) ^
               " passed to state_locality_for_attribute")
        else ()

      fun arglist_with x =
            make_arglist num_args
         |> list_set_nth rec_namex x
         |> String.concatWith " "
      val argsA = arglist_with "R"
      fun argsB field = arglist_with ("(" ^ field_update rec_name field ^ " f R)")

      (* Build statements of locality lemmas *)
      fun commutativity_str (prop : string) (field : string) =
          "\<And>f " ^ argsA ^ ". " ^ prop ^ " " ^ argsB field ^ " = " ^ prop ^ " " ^ argsA
      fun get_commutativity_stm prop field = commutativity_str prop field |> Syntax.read_prop ctxt
      val commutativity_stms = List.map (get_commutativity_stm p_name) disjoint_fields

      fun after_qed (named_thm_list_opt) name (cont : Proof.context -> Proof.context) thms ctxt =
        let val thms = thms |> flat
          val attribs = unpack_attributes_default ctxt rec_name attribs_opt
           |> List.map (Attrib.check_src ctxt)
        in ctxt
           |> (case named_thm_list_opt of
               SOME n => fold (fn t => Local_Theory.declaration {pervasive=false, syntax=false, pos=Position.none} (Named_Theorems.add_thm n t |> K)) thms
             | NONE => I)
           |> Local_Theory.note (((Binding.name name), []), thms) |> snd
           |> Local_Theory.note ((Binding.empty,attribs), thms) |> snd
           |> cont
        end

      val default_simps =
        let val const_unfold = if is_const_with_def ctxt p_name then [Thm.def_name p_name] else []
            val locality_facts = if Option.isSome attribs_opt then [] else [default_named_theorems_for_record rec_name]
            val all_simps = ["Let_def"] @ const_unfold @ locality_facts
        in
          String.concatWith " " all_simps
        end

      val cancellation_thm_name = register_locality_attr_cancellation_thm_name rec_name p_id rec_namex
      val cancellation_thms_name = register_locality_attr_cancellation_thm_list_name rec_name p_id rec_namex

      val (cancellation_thms_name, ctxt') = ctxt
         |> Named_Theorems.declare (Binding.make (cancellation_thms_name, \<^here>)) ""

      fun start_core_proof ctxt cont = ctxt
           |> Proof.theorem NONE (after_qed (SOME cancellation_thms_name) cancellation_thm_name cont) [map (fn t => (t,[])) commutativity_stms]
           |> apply_method (SIMPLE_METHOD all_tac)
           |> (if with_proof then
                apply_txt ctxt ("(auto simp add: " ^ default_simps ^ ")?")
              else
                I)
    in
      start_core_proof ctxt' (add_record_locality_entry ctxt' rec_name "attribute"
                              p_name footprint num_args rec_namex
                              (SOME (make_locality_simproc ctxt' rec_name p_name num_args rec_namex)))
    end

  fun state_locality attribs_opt (rec_name : string) (p_name: string) (footprint: string list)
      (with_proof : bool) (match_idx : int) (ctxt : Proof.context)  =
    let
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val p_term = Syntax.read_term ctxt p_name
      val p_ty = Term.type_of p_term
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
            ([Pretty.str "Indices:", Pretty.list "[" "]" (List.map (Int.toString #> Pretty.str) idxs),
             Pretty.str "Index", Pretty.str (match_idx |> Int.toString)]
            |> Pretty.breaks |> Pretty.block |> locality_pretty_trace ctxt 1;
             state_locality_for_attribute attribs_opt rec_name p_name footprint with_proof
               (nth idxs match_idx) ctxt)
    end

  val record_local_op_argparse =
         ((Args.$$$ "for") |-- Parse.typ)
      -- Scan.optional (Args.parens (Args.$$$ "no_proof") >> K true) false
      -- (Scan.optional (Parse.attribs >> SOME) NONE --| Args.colon)
      -- Parse.term
      -- (Scan.optional ( Args.bracks Parse.int) 0)
      -- (Args.$$$ "footprint" |-- (Args.bracks (Parse.list Parse.short_ident)))

  val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "locality_lemma"}
          "prove locality lemma for operations and attributes on records"
             (record_local_op_argparse >>
                (fn (((((rec_name, no_proof), attribs_opt), p_name), match_idx), field_list) =>
                   state_locality attribs_opt rec_name p_name field_list (not no_proof) match_idx))

  fun remove_todo attribs rec_name ({const_name = cA, const_type = typeA, footprint=_, idx=idxA, args=_, sp=_},
                                    {const_name = cB, const_type = typeB, footprint=_, idx=idxB, args=_, sp=_}) =
    case (typeA, typeB) of
       ("operation", "operation") => prove_commutativity_lemma_for_disjoint_operators attribs rec_name cA cB
     | ("attribute", "operation") => prove_commutativity_lemma_for_disjoint_operator_and_attribute attribs rec_name cB cA idxA
     | ("operation", "attribute") => prove_commutativity_lemma_for_disjoint_operator_and_attribute attribs rec_name cA cB idxB
     | _ => "Invalid type combination (" ^ typeA ^ ", " ^ typeB ^ ") for commutativity proof" |> error

  fun locality_autoderive_core attribs_opt (rec_name : string) (ctxt : Proof.context)  =
    let
      val (rec_ty, rec_name) = prepare_rec_name ctxt rec_name
      val todo = find_disjoint_pairs_without_commutativity_lemma_generic rec_name (Context.Proof ctxt)
    in
      if length todo = 0 then
         ((Pretty.text "Nothing to do for" @ [Pretty.brk 1, Syntax.pretty_typ ctxt rec_ty]
           |> Pretty.block |> Pretty.string_of |> Output.information); ctxt)
      else
          ctxt
       |> fold (remove_todo attribs_opt rec_name) todo
    end

  fun locality_autoderive attribs_opt (rec_name_opt : string option) (ctxt : Proof.context)  =
    case rec_name_opt of
        SOME rec_name => locality_autoderive_core attribs_opt rec_name ctxt
      | NONE => (* Update all records for which at least one constant is registered *)
         let val records = get_registered_records ctxt in
           fold (locality_autoderive_core attribs_opt) records ctxt
         end

  val locality_autoderive_argparse =
         Scan.optional (((Args.$$$ "for") |-- Parse.typ) >> SOME) NONE
      -- Scan.optional (Parse.attribs >> SOME) NONE

  val _ = Outer_Syntax.local_theory @{command_keyword "locality_autoderive"}
          "autoderive locality lemmas for constants previously registered via locality_lemma"
             (locality_autoderive_argparse >>
                (fn (rec_name_opt, attribs_opt) => locality_autoderive attribs_opt rec_name_opt))

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
        has_record_locality_entry_generic rec_name (Long_Name.base_name c) (Context.Proof ctxt)
      val special_attributes =
        (* Field projections *)
        get_fields rec_name ctxt
        (* Various standard built-in attributes *)
        @ List.map (fn t => t ^ "_" ^ rec_name)
          [ "Rep", "case", "ctor_fold", "ctor_rec",
            "dtor", "rec", "size", "term_of"]
      fun is_builtin_attr (c, _) =
        Library.member (op =) special_attributes (Long_Name.base_name c)
      fun is_builtin_op (c, _) =
        Library.member (op =) (
           (* Field updates *)
           List.map (field_update rec_name) (get_fields rec_name ctxt)
        ) (Long_Name.base_name c)
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

  fun locality_cancellation_simprocs_add_all ctxt : attribute =
    let
      val attrs = get_attributes ctxt |> map snd
      val attr_simprocs = attrs |> List.map (#sp #> Option.valOf)
    in
      Thm.declaration_attribute (K (Simplifier.map_simpset (fold Simplifier.add_proc attr_simprocs)))
    end

  fun locality_cancellation_simprocs_del_all ctxt : attribute =
    let
      val attr_simprocs = get_attributes ctxt |> map snd |> List.map (#sp #> Option.valOf)
    in
      Thm.declaration_attribute (K (Simplifier.map_simpset (fold Simplifier.del_proc attr_simprocs)))
    end\<close>

attribute_setup locality_cancel    = \<open>Args.context >> locality_cancellation_simprocs_add_all\<close>
attribute_setup locality_no_cancel = \<open>Args.context >> locality_cancellation_simprocs_del_all\<close>

end
