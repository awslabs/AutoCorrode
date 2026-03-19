theory C_Translation_Engine
  imports
    C_Ast_Utilities
    "Shallow_Micro_Rust.Core_Expression"
    "Shallow_Micro_Rust.Prompts_And_Responses"
    "Shallow_Micro_Rust.Core_Syntax"
    "Shallow_Micro_Rust.Bool_Type"
    "Shallow_Micro_Rust.Rust_Iterator"
    "Shallow_Micro_C.C_Translation_Model"
begin

subsection \<open>Translation Context\<close>

text \<open>
  The translation context tracks information accumulated during AST traversal:
  variable bindings (mapping C variable names to Isabelle free variables),
  function signatures, and diagnostics.
\<close>

ML \<open>
structure C_Trans_Ctxt : sig
  datatype var_kind = Param | ParamListPtr | Local | LocalPtr  (* Param = by-value, ParamListPtr = by-value list-backed pointer alias, Local = mutable reference, LocalPtr = mutable raw-pointer reference *)
  type t
  val make : Proof.context -> (string * C_Ast_Utils.c_numeric_type) list Symtab.table
             -> int Symtab.table -> C_Ast_Utils.c_numeric_type Symtab.table
             -> C_Ast_Utils.c_numeric_type Symtab.table Unsynchronized.ref
             -> C_Ast_Utils.c_numeric_type list Symtab.table Unsynchronized.ref
             -> typ -> typ -> t
  val get_ctxt : t -> Proof.context
  val get_ref_addr_ty : t -> typ
  val get_ref_gv_ty : t -> typ
  val add_var : string -> var_kind -> term -> C_Ast_Utils.c_numeric_type -> t -> t
  val lookup_var : t -> string -> (var_kind * term * C_Ast_Utils.c_numeric_type) option
  val add_global_const : string -> term -> C_Ast_Utils.c_numeric_type -> t -> t
  val lookup_global_const : t -> string -> (term * C_Ast_Utils.c_numeric_type) option
  val get_struct_names : t -> string list
  val set_struct_type : string -> string -> t -> t
  val get_struct_type : t -> string -> string option
  val get_struct_fields : t -> string -> (string * C_Ast_Utils.c_numeric_type) list option
  val lookup_struct_field_type : t -> string -> string -> C_Ast_Utils.c_numeric_type option
  val set_array_decl : string -> C_Ast_Utils.c_numeric_type -> int -> t -> t
  val lookup_array_decl : t -> string -> (C_Ast_Utils.c_numeric_type * int) option
  val lookup_enum_const : t -> string -> int option
  val add_enum_consts : (string * int) list -> t -> t
  val get_typedef_tab : t -> C_Ast_Utils.c_numeric_type Symtab.table
  val register_func_return_type : string -> C_Ast_Utils.c_numeric_type -> t -> unit
  val lookup_func_return_type : t -> string -> C_Ast_Utils.c_numeric_type option
  val register_func_param_types : string -> C_Ast_Utils.c_numeric_type list -> t -> unit
  val lookup_func_param_types : t -> string -> C_Ast_Utils.c_numeric_type list option
  val get_break_ref : t -> term option
  val get_continue_ref : t -> term option
  val set_break_ref : term -> t -> t
  val set_continue_ref : term -> t -> t
  val clear_break_ref : t -> t
  val get_goto_refs : t -> (string * term) list
  val set_goto_refs : (string * term) list -> t -> t
  val lookup_goto_ref : t -> string -> term option
  val get_active_goto_labels : t -> string list
  val set_active_goto_labels : string list -> t -> t
end =
struct
  datatype var_kind = Param | ParamListPtr | Local | LocalPtr
  type t = {
    ctxt : Proof.context,
    vars : (var_kind * term * C_Ast_Utils.c_numeric_type) Symtab.table,
    global_consts : (term * C_Ast_Utils.c_numeric_type) Symtab.table,
    struct_types : string Symtab.table,         (* var_name -> c_struct_name *)
    struct_fields : (string * C_Ast_Utils.c_numeric_type) list Symtab.table,
    array_decls : (C_Ast_Utils.c_numeric_type * int) Symtab.table,  (* var_name -> (elem_cty, size) *)
    enum_consts : int Symtab.table,             (* enum_name -> int_value *)
    typedef_tab : C_Ast_Utils.c_numeric_type Symtab.table,
    func_ret_types : C_Ast_Utils.c_numeric_type Symtab.table Unsynchronized.ref,
    func_param_types : C_Ast_Utils.c_numeric_type list Symtab.table Unsynchronized.ref,
    ref_addr_ty : typ,
    ref_gv_ty : typ,
    break_ref : term option,
    continue_ref : term option,
    goto_refs : (string * term) list,           (* label_name -> flag ref variable *)
    active_goto_labels : string list             (* labels that are valid forward goto targets from here *)
  }

  fun make ctxt struct_fields enum_consts typedef_tab func_ret_types func_param_types
      ref_addr_ty ref_gv_ty : t =
    { ctxt = ctxt, vars = Symtab.empty, global_consts = Symtab.empty, struct_types = Symtab.empty,
      struct_fields = struct_fields, array_decls = Symtab.empty,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types, ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = NONE, continue_ref = NONE,
      goto_refs = [], active_goto_labels = [] }

  fun get_ctxt ({ ctxt, ... } : t) = ctxt
  fun get_ref_addr_ty ({ ref_addr_ty, ... } : t) = ref_addr_ty
  fun get_ref_gv_ty ({ ref_gv_ty, ... } : t) = ref_gv_ty

  fun add_var name kind tm cty ({ ctxt, vars, global_consts, struct_types, struct_fields,
                                   array_decls, enum_consts, typedef_tab, func_ret_types,
                                   func_param_types, ref_addr_ty, ref_gv_ty, break_ref, continue_ref, goto_refs,
                                   active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = Symtab.update (name, (kind, tm, cty)) vars,
      global_consts = global_consts,
      struct_types = struct_types, struct_fields = struct_fields,
      array_decls = array_decls,
      enum_consts = enum_consts, typedef_tab = typedef_tab,
      func_ret_types = func_ret_types,
      func_param_types = func_param_types, ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = break_ref, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = active_goto_labels }

  fun lookup_var ({ vars, ... } : t) name =
    Symtab.lookup vars name

  fun add_global_const name tm cty
      ({ ctxt, vars, global_consts, struct_types, struct_fields, array_decls, enum_consts,
         typedef_tab, func_ret_types, func_param_types, ref_addr_ty, ref_gv_ty, break_ref, continue_ref, goto_refs,
         active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars,
      global_consts = Symtab.update (name, (tm, cty)) global_consts,
      struct_types = struct_types, struct_fields = struct_fields,
      array_decls = array_decls, enum_consts = enum_consts, typedef_tab = typedef_tab,
      func_ret_types = func_ret_types, func_param_types = func_param_types,
      ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = break_ref, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = active_goto_labels }

  fun lookup_global_const ({ global_consts, ... } : t) name =
    Symtab.lookup global_consts name

  fun get_struct_names ({ struct_fields, ... } : t) =
    Symtab.keys struct_fields

  fun set_struct_type var_name struct_name
      ({ ctxt, vars, global_consts, struct_types, struct_fields, array_decls, enum_consts, typedef_tab,
         func_ret_types, func_param_types, ref_addr_ty, ref_gv_ty, break_ref, continue_ref, goto_refs,
         active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, global_consts = global_consts,
      struct_types = Symtab.update (var_name, struct_name) struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types, ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = break_ref, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = active_goto_labels }

  fun get_struct_type ({ struct_types, ... } : t) name =
    Symtab.lookup struct_types name

  fun get_struct_fields ({ struct_fields, ... } : t) name =
    Symtab.lookup struct_fields name

  fun lookup_struct_field_type tctx struct_name field_name =
    case get_struct_fields tctx struct_name of
      SOME fields => (case List.find (fn (n, _) => n = field_name) fields of
                        SOME (_, cty) => SOME cty | NONE => NONE)
    | NONE => NONE

  fun set_array_decl var_name elem_cty size
      ({ ctxt, vars, global_consts, struct_types, struct_fields, array_decls, enum_consts,
         typedef_tab, func_ret_types, func_param_types, ref_addr_ty, ref_gv_ty, break_ref, continue_ref,
         goto_refs, active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, global_consts = global_consts, struct_types = struct_types,
      struct_fields = struct_fields,
      array_decls = Symtab.update (var_name, (elem_cty, size)) array_decls,
      enum_consts = enum_consts, typedef_tab = typedef_tab,
      func_ret_types = func_ret_types, func_param_types = func_param_types,
      ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = break_ref, continue_ref = continue_ref, goto_refs = goto_refs,
      active_goto_labels = active_goto_labels }

  fun lookup_array_decl ({ array_decls, ... } : t) name =
    Symtab.lookup array_decls name

  fun lookup_enum_const ({ enum_consts, ... } : t) name =
    Symtab.lookup enum_consts name

  fun add_enum_consts entries ({ ctxt, vars, struct_types, struct_fields,
                                 global_consts, array_decls, enum_consts, typedef_tab, func_ret_types,
                                 func_param_types, ref_addr_ty, ref_gv_ty, break_ref, continue_ref, goto_refs,
                                 active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, global_consts = global_consts, struct_types = struct_types,
      struct_fields = struct_fields,
      array_decls = array_decls,
      enum_consts = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                      enum_consts entries,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types, ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = break_ref, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = active_goto_labels }

  fun get_typedef_tab ({ typedef_tab, ... } : t) = typedef_tab

  fun register_func_return_type name cty ({ func_ret_types, ... } : t) =
    func_ret_types := Symtab.update (name, cty) (! func_ret_types)

  fun lookup_func_return_type ({ func_ret_types, ... } : t) name =
    Symtab.lookup (! func_ret_types) name

  fun register_func_param_types name ctys ({ func_param_types, ... } : t) =
    func_param_types := Symtab.update (name, ctys) (! func_param_types)

  fun lookup_func_param_types ({ func_param_types, ... } : t) name =
    Symtab.lookup (! func_param_types) name

  fun get_break_ref ({ break_ref, ... } : t) = break_ref
  fun get_continue_ref ({ continue_ref, ... } : t) = continue_ref

  fun set_break_ref ref_term ({ ctxt, vars, struct_types, struct_fields,
                                 global_consts, array_decls, enum_consts, typedef_tab, func_ret_types,
                                 func_param_types, ref_addr_ty, ref_gv_ty, break_ref = _, continue_ref,
                                 goto_refs, active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, global_consts = global_consts, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types, ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = SOME ref_term,
      continue_ref = continue_ref, goto_refs = goto_refs,
      active_goto_labels = active_goto_labels }

  fun set_continue_ref ref_term ({ ctxt, vars, struct_types, struct_fields,
                                    global_consts, array_decls, enum_consts, typedef_tab, func_ret_types,
                                    func_param_types, ref_addr_ty, ref_gv_ty, break_ref, continue_ref = _,
                                    goto_refs, active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, global_consts = global_consts, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types, ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = break_ref,
      continue_ref = SOME ref_term, goto_refs = goto_refs,
      active_goto_labels = active_goto_labels }

  fun clear_break_ref ({ ctxt, vars, struct_types, struct_fields,
                          global_consts, array_decls, enum_consts, typedef_tab, func_ret_types,
                          func_param_types, ref_addr_ty, ref_gv_ty, break_ref = _, continue_ref, goto_refs,
                          active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, global_consts = global_consts, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types, ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = NONE, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = active_goto_labels }

  fun get_goto_refs ({ goto_refs, ... } : t) = goto_refs

  fun set_goto_refs refs ({ ctxt, vars, struct_types, struct_fields,
                             global_consts, array_decls, enum_consts, typedef_tab, func_ret_types,
                             func_param_types, ref_addr_ty, ref_gv_ty, break_ref, continue_ref, goto_refs = _,
                             active_goto_labels } : t) : t =
    { ctxt = ctxt, vars = vars, global_consts = global_consts, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts,
      typedef_tab = typedef_tab, func_ret_types = func_ret_types,
      func_param_types = func_param_types, ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = break_ref,
      continue_ref = continue_ref, goto_refs = refs,
      active_goto_labels = active_goto_labels }

  fun lookup_goto_ref ({ goto_refs, ... } : t) name =
    case List.find (fn (n, _) => n = name) goto_refs of
      SOME (_, ref_term) => SOME ref_term
    | NONE => NONE

  fun get_active_goto_labels ({ active_goto_labels, ... } : t) =
    active_goto_labels

  fun set_active_goto_labels labels ({ ctxt, vars, struct_types, struct_fields,
                                       global_consts, array_decls, enum_consts, typedef_tab, func_ret_types,
                                       func_param_types, ref_addr_ty, ref_gv_ty, break_ref, continue_ref, goto_refs,
                                       active_goto_labels = _ } : t) : t =
    { ctxt = ctxt, vars = vars, global_consts = global_consts, struct_types = struct_types,
      struct_fields = struct_fields, array_decls = array_decls,
      enum_consts = enum_consts, typedef_tab = typedef_tab,
      func_ret_types = func_ret_types, func_param_types = func_param_types,
      ref_addr_ty = ref_addr_ty, ref_gv_ty = ref_gv_ty,
      break_ref = break_ref, continue_ref = continue_ref,
      goto_refs = goto_refs, active_goto_labels = distinct (op =) labels }
end
\<close>

subsection \<open>Array Indexing Helper\<close>

text \<open>
  The @{text unat} function from the Word library is an abbreviation, not a logical
  constant, so it cannot be referenced via @{text "\<^const_name>"} in ML.
  We define a proper constant that wraps it.
\<close>

definition c_idx_to_nat :: \<open>'a::len word \<Rightarrow> nat\<close> where
  [simp]: \<open>c_idx_to_nat w = unat w\<close>

subsection \<open>Stub Constants for Unsupported C Constructs\<close>

text \<open>
  Opaque constants for C constructs that cannot be translated.
  They have no WP rules, so symbolic execution silently gets stuck
  when encountering these. The translation succeeds, and the user
  can see from the constant names which constructs need attention.
\<close>

consts c_while_stub :: "('s, 'v, 'r, 'abort, 'i, 'o) expression"
consts c_goto_stub :: "('s, 'v, 'r, 'abort, 'i, 'o) expression"
consts c_unsupported :: "('s, 'v, 'r, 'abort, 'i, 'o) expression"
consts c_uninitialized :: "'a"

definition c_bounds_abort :: "('s, 'v, 'r, 'abort, 'i, 'o) expression" where [simp]:
  "c_bounds_abort \<equiv> abort undefined"

subsection \<open>Term Construction\<close>

text \<open>
  Functions for building well-formed core monad terms. Each function
  constructs a term using the actual constants from @{theory "Shallow_Micro_Rust.Core_Expression"}.
\<close>

ML \<open>
structure C_Term_Build : sig
  val mk_literal_unit : term
  val mk_literal : term -> term
  val mk_function_body : term -> term
  val mk_sequence : term -> term -> term
  val mk_literal_num : C_Ast_Utils.c_numeric_type -> int -> term
  val mk_literal_int : int -> term
  val mk_return_func : term -> term
  val mk_bind : term -> term -> term
  val mk_var_alloc : term -> term
  val mk_var_alloc_typed : typ -> term -> term
  val mk_var_read : term -> term
  val mk_var_write : term -> term -> term
  val mk_bindlift2 : term -> term -> term -> term
  val mk_bind2 : term -> term -> term -> term
  val mk_bind2_unseq : term -> term -> term -> term
  val mk_two_armed_cond : term -> term -> term -> term
  val mk_one_armed_cond : term -> term -> term
  val mk_funcall : term -> term list -> term
  val mk_raw_for_loop : term -> term -> term
  val mk_upt_int_range : term -> term -> term
  val mk_deref : term -> term
  val mk_ptr_write : term -> term -> term
  val mk_struct_field_read : term -> term -> term
  val mk_struct_field_write : term -> term -> term -> term
  val mk_unat : term -> term
  val mk_focus_nth : term -> term -> term
  val mk_focus_field : term -> term -> term
  val mk_bounded_while : term -> term -> term -> term
  val mk_goto_stub : term
  val mk_unsupported_stub : term
end =
struct
  (* literal v *)
  fun mk_literal v =
    Const (\<^const_name>\<open>literal\<close>, dummyT --> dummyT) $ v

  (* literal () : the "skip" operation *)
  val mk_literal_unit =
    Const (\<^const_name>\<open>literal\<close>, \<^typ>\<open>unit\<close> --> dummyT) $ HOLogic.unit

  (* FunctionBody e *)
  fun mk_function_body body =
    Const (\<^const_name>\<open>FunctionBody\<close>, dummyT --> dummyT) $ body

  (* sequence e1 e2 *)
  fun mk_sequence e1 e2 =
    Const (\<^const_name>\<open>sequence\<close>, dummyT --> dummyT --> dummyT) $ e1 $ e2

  (* literal n, typed according to the given c_numeric_type *)
  fun mk_literal_num cty n =
    let val ty = C_Ast_Utils.hol_type_of cty
    in Const (\<^const_name>\<open>literal\<close>, ty --> dummyT) $ HOLogic.mk_number ty n end

  (* literal n, where n is a C integer constant.
     Uses dummyT so Isabelle infers the correct word type from context
     (e.g. 32 sword in signed expressions, 32 word in unsigned). *)
  fun mk_literal_int n =
    Const (\<^const_name>\<open>literal\<close>, dummyT --> dummyT) $ HOLogic.mk_number dummyT n

  (* return_func e : for C return statements *)
  fun mk_return_func body =
    Const (\<^const_name>\<open>return_func\<close>, dummyT --> dummyT) $ body

  (* bind e f : monadic bind *)
  fun mk_bind e f =
    Const (\<^const_name>\<open>bind\<close>, dummyT --> dummyT --> dummyT) $ e $ f

  (* Allocate a new mutable variable: funcall1 store_reference_const init_expr *)
  fun mk_var_alloc init_expr =
    Const (\<^const_name>\<open>funcall1\<close>, dummyT --> dummyT --> dummyT)
      $ Const (\<^const_name>\<open>store_reference_const\<close>, dummyT)
      $ init_expr

  (* Type-annotated variant: constrains the value type of store_reference_const
     so adhoc overloading can resolve when multiple word-type prisms exist. *)
  fun mk_var_alloc_typed val_hol_type init_expr =
    if val_hol_type = dummyT then mk_var_alloc init_expr
    else
      Const (\<^const_name>\<open>funcall1\<close>, dummyT --> dummyT --> dummyT)
        $ Const (\<^const_name>\<open>store_reference_const\<close>, val_hol_type --> dummyT)
        $ init_expr

  (* Read a mutable variable: bind (literal ref) (deep_compose1 call store_dereference_const) *)
  fun mk_var_read ref_var =
    Const (\<^const_name>\<open>bind\<close>, dummyT --> dummyT --> dummyT)
      $ mk_literal ref_var
      $ (Const (\<^const_name>\<open>deep_compose1\<close>, dummyT --> dummyT --> dummyT)
           $ Const (\<^const_name>\<open>call\<close>, dummyT --> dummyT)
           $ Const (\<^const_name>\<open>store_dereference_const\<close>, dummyT))

  (* Write a mutable variable: bind2 (deep_compose2 call store_update_const) (literal ref) val_expr *)
  fun mk_var_write ref_var val_expr =
    Const (\<^const_name>\<open>bind2\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ (Const (\<^const_name>\<open>deep_compose2\<close>, dummyT --> dummyT --> dummyT)
           $ Const (\<^const_name>\<open>call\<close>, dummyT --> dummyT)
           $ Const (\<^const_name>\<open>store_update_const\<close>, dummyT))
      $ mk_literal ref_var
      $ val_expr
  fun mk_bindlift2 f e1 e2 =
    Const (\<^const_name>\<open>bindlift2\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ f $ e1 $ e2

  (* bind2 f e1 e2 : evaluate e1 and e2, then apply monadic f *)
  fun mk_bind2 f e1 e2 =
    Const (\<^const_name>\<open>bind2\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ f $ e1 $ e2

  (* bind2_unseq f e1 e2 : evaluate e1/e2 in unspecified order, then apply monadic f *)
  fun mk_bind2_unseq f e1 e2 =
    Const (\<^const_name>\<open>bind2_unseq\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ f $ e1 $ e2

  (* two_armed_conditional test then_br else_br *)
  fun mk_two_armed_cond test then_br else_br =
    Const (\<^const_name>\<open>two_armed_conditional\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ test $ then_br $ else_br

  (* one_armed_conditional test then_br *)
  fun mk_one_armed_cond test then_br =
    Const (\<^const_name>\<open>two_armed_conditional\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ test $ then_br $ mk_literal_unit

  (* funcallN f arg0 ... argN : call a function with N arguments *)
  local
    val funcall_names = Vector.fromList [
      \<^const_name>\<open>funcall0\<close>, \<^const_name>\<open>funcall1\<close>, \<^const_name>\<open>funcall2\<close>,
      \<^const_name>\<open>funcall3\<close>, \<^const_name>\<open>funcall4\<close>, \<^const_name>\<open>funcall5\<close>,
      \<^const_name>\<open>funcall6\<close>, \<^const_name>\<open>funcall7\<close>, \<^const_name>\<open>funcall8\<close>,
      \<^const_name>\<open>funcall9\<close>, \<^const_name>\<open>funcall10\<close>,
      \<^const_name>\<open>funcall11\<close>, \<^const_name>\<open>funcall12\<close>, \<^const_name>\<open>funcall13\<close>,
      \<^const_name>\<open>funcall14\<close>, \<^const_name>\<open>funcall15\<close>, \<^const_name>\<open>funcall16\<close>
    ]
  in
  fun mk_funcall f args =
    let val n = length args
    in if n > 16 then error "mk_funcall: more than 16 arguments not supported"
       else let val cname = Vector.sub (funcall_names, n)
                val ty = Library.foldr (fn (_, t) => dummyT --> t) (args, dummyT)
            in Library.foldl (op $) (Const (cname, dummyT --> ty), f :: args) end
    end
  end

  (* raw_for_loop range_list body_fn *)
  fun mk_raw_for_loop range body =
    Const (\<^const_name>\<open>raw_for_loop\<close>, dummyT --> dummyT --> dummyT) $ range $ body

  (* Build [start..<bound] mapped through of_nat to produce an int list:
     List.map of_nat [start..<bound] *)
  fun mk_upt_int_range start_nat bound_nat =
    Const (\<^const_name>\<open>List.map\<close>, dummyT --> dummyT --> dummyT)
      $ Const (\<^const_name>\<open>of_nat\<close>, dummyT)
      $ (Const (\<^const_name>\<open>upt\<close>, dummyT --> dummyT --> dummyT) $ start_nat $ bound_nat)

  (* Dereference a pointer expression: bind ptr_expr (deep_compose1 call store_dereference_const)
     This generalizes mk_var_read from literal variables to arbitrary expressions. *)
  fun mk_deref ptr_expr =
    Const (\<^const_name>\<open>bind\<close>, dummyT --> dummyT --> dummyT)
      $ ptr_expr
      $ (Const (\<^const_name>\<open>deep_compose1\<close>, dummyT --> dummyT --> dummyT)
           $ Const (\<^const_name>\<open>call\<close>, dummyT --> dummyT)
           $ Const (\<^const_name>\<open>store_dereference_const\<close>, dummyT))

  (* Write through a pointer expression: bind2 (deep_compose2 call store_update_const) ptr_expr val_expr
     This generalizes mk_var_write from literal variables to arbitrary expressions. *)
  fun mk_ptr_write ptr_expr val_expr =
    Const (\<^const_name>\<open>bind2\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ (Const (\<^const_name>\<open>deep_compose2\<close>, dummyT --> dummyT --> dummyT)
           $ Const (\<^const_name>\<open>call\<close>, dummyT --> dummyT)
           $ Const (\<^const_name>\<open>store_update_const\<close>, dummyT))
      $ ptr_expr
      $ val_expr

  (* Struct field read: dereference pointer, then extract field via accessor.
     Generates: bind (deref ptr_expr) (\<lambda>v. literal (accessor v)) *)
  fun mk_struct_field_read accessor_const ptr_expr =
    let val v = Free ("v__struct", dummyT)
    in mk_bind (mk_deref ptr_expr)
         (Term.lambda v (mk_literal (accessor_const $ v)))
    end

  (* Struct field write: evaluate rhs, dereference pointer, update field, write back.
     Generates: bind val_expr (\<lambda>rhs. bind (deref ptr) (\<lambda>v. ptr_write ptr (updater (\<lambda>_. rhs) v))) *)
  fun mk_struct_field_write updater_const ptr_expr val_expr =
    let val rhs_var = Free ("v__rhs", dummyT)
        val struct_var = Free ("v__struct", dummyT)
        val dummy_var = Free ("_uu__", dummyT)
        val updated = updater_const $ (Term.lambda dummy_var rhs_var) $ struct_var
    in mk_bind val_expr (Term.lambda rhs_var
         (mk_bind (mk_deref ptr_expr) (Term.lambda struct_var
           (mk_ptr_write ptr_expr (mk_literal updated)))))
    end

  (* c_idx_to_nat idx : convert word to nat for array indexing (wraps unat) *)
  fun mk_unat idx_term =
    Const (\<^const_name>\<open>c_idx_to_nat\<close>, dummyT --> dummyT) $ idx_term

  (* focus_focused (nth_focus idx_nat) ref_term : focus reference to nth element *)
  fun mk_focus_nth idx_nat ref_term =
    Const (\<^const_name>\<open>focus_focused\<close>, dummyT --> dummyT --> dummyT)
      $ (Const (\<^const_name>\<open>nth_focus\<close>, dummyT --> dummyT) $ idx_nat)
      $ ref_term

  fun mk_focus_field focus_const ref_term =
    Const (\<^const_name>\<open>focus_focused\<close>, dummyT --> dummyT --> dummyT)
      $ focus_const
      $ ref_term

  (* bounded_while fuel cond body *)
  fun mk_bounded_while fuel cond body =
    Const (\<^const_name>\<open>bounded_while\<close>, dummyT --> dummyT --> dummyT --> dummyT)
      $ fuel $ cond $ body

  (* Stub constants for unsupported C constructs *)
  val mk_goto_stub = Const (\<^const_name>\<open>c_goto_stub\<close>, dummyT)
  val mk_unsupported_stub = Const (\<^const_name>\<open>c_unsupported\<close>, dummyT)
end
\<close>

subsection \<open>Statement and Expression Translation\<close>

text \<open>
  The core translation: C AST nodes are mapped to core monad expressions.
  Unsupported constructs produce explicit errors identifying the construct
  that could not be translated.
\<close>

ML \<open>
structure C_Translate : sig
  type pointer_model = {ptr_add: string option, ptr_shift_signed: string option, ptr_diff: string option}
  val translate_stmt : C_Trans_Ctxt.t -> C_Ast.nodeInfo C_Ast.cStatement -> term
  val set_decl_prefix : string -> unit
  val set_union_names : string list -> unit
  val current_union_names : string list Unsynchronized.ref
  val set_ref_universe_types : typ -> typ -> unit
  val set_ref_abort_type : typ option -> unit
  val set_pointer_model : pointer_model -> unit
  val strip_isa_fun_type : typ -> typ list
  val defined_func_consts : term Symtab.table Unsynchronized.ref
  val defined_func_fuels : int Symtab.table Unsynchronized.ref
  val current_list_backed_param_modes : bool list Symtab.table Unsynchronized.ref
  val current_struct_array_fields : string list Symtab.table Unsynchronized.ref
  val translate_fundef : (string * C_Ast_Utils.c_numeric_type) list Symtab.table
                         -> int Symtab.table
                         -> C_Ast_Utils.c_numeric_type Symtab.table
                         -> C_Ast_Utils.c_numeric_type Symtab.table Unsynchronized.ref
                         -> C_Ast_Utils.c_numeric_type list Symtab.table Unsynchronized.ref
                         -> (string * term * C_Ast_Utils.c_numeric_type *
                             (C_Ast_Utils.c_numeric_type * int) option * string option) list
                         -> Proof.context
                         -> C_Ast.nodeInfo C_Ast.cFunctionDef -> string * term
end =
struct
  type pointer_model = {ptr_add: string option, ptr_shift_signed: string option, ptr_diff: string option}

  (* Save Isabelle term constructors before C_Ast shadows them *)
  val Isa_Const = Const
  val Isa_Free = Free
  val isa_dummyT = dummyT
  val Isa_add_frees = Term.add_frees
  val Isa_Type = Type

  (* Table mapping fixed-variable names to qualified const names.
     Populated by C_Def_Gen.define_c_function using target_morphism
     (the standard Isabelle mechanism from specification.ML:269). *)
  val defined_func_consts : term Symtab.table Unsynchronized.ref =
    Unsynchronized.ref Symtab.empty

  (* Table mapping function names to their fuel parameter count.
     Populated by translate_fundef after abstracting while_fuel variables. *)
  val defined_func_fuels : int Symtab.table Unsynchronized.ref =
    Unsynchronized.ref Symtab.empty

  (* Per-translation-unit hint for parameters that should be translated as
     list-backed pointer aliases rather than raw pointers. *)
  val current_list_backed_param_modes : bool list Symtab.table Unsynchronized.ref =
    Unsynchronized.ref Symtab.empty

  val current_struct_array_fields : string list Symtab.table Unsynchronized.ref =
    Unsynchronized.ref Symtab.empty

  (* Generate a fresh variable name not occurring free in the given terms *)
  fun fresh_var terms stem typ =
    let val used = List.foldl (fn (t, acc) => Isa_add_frees t acc) [] terms
                   |> List.map fst
        val (name, _) = Name.variant stem (Name.make_context used)
    in Isa_Free (name, typ) end

  fun expr_value_type tm =
    (case fastype_of tm of
       Type (_, _ :: vty :: _) => vty
     | _ => isa_dummyT)

  (* Translation-time ambient context shared across expression/function
     translation. These must be declared before pointer-cast helpers that use
     the reference universe and expression side-type information. *)
  val current_ret_cty : C_Ast_Utils.c_numeric_type option Unsynchronized.ref =
    Unsynchronized.ref NONE
  val current_decl_prefix : string Unsynchronized.ref =
    Unsynchronized.ref "c_"
  val current_union_names : string list Unsynchronized.ref =
    Unsynchronized.ref []
  val current_loop_written_vars : string list Unsynchronized.ref =
    Unsynchronized.ref []
  val current_ref_addr_ty : typ Unsynchronized.ref =
    Unsynchronized.ref (TFree ("'addr", []))
  val current_ref_gv_ty : typ Unsynchronized.ref =
    Unsynchronized.ref (TFree ("'gv", []))
  val current_ref_expr_constraint : typ option Unsynchronized.ref =
    Unsynchronized.ref NONE
  val current_pointer_model : pointer_model Unsynchronized.ref =
    Unsynchronized.ref {ptr_add = SOME "c_ptr_add", ptr_shift_signed = SOME "c_ptr_shift_signed", ptr_diff = SOME "c_ptr_diff"}
  val current_visible_ctxt : Proof.context option Unsynchronized.ref =
    Unsynchronized.ref NONE

  fun uses_raw_pointer_model () = true

  fun require_current_visible_ctxt () =
    (case !current_visible_ctxt of
       SOME ctxt => ctxt
     | NONE => error "micro_c_translate: missing translation proof context")

  fun resolve_required_current_visible_const short_name =
    let val ctxt = require_current_visible_ctxt ()
    in
      case try (Syntax.check_term ctxt) (Free (short_name, dummyT)) of
        SOME tm => tm
      | NONE => error ("micro_c_translate: missing required visible constant: " ^ short_name)
    end

  fun constrain_expr_side_types tm =
    (case !current_ref_expr_constraint of
       SOME (Type (ename, [state_ty, _, resid_ty, abort_ty, in_ty, out_ty])) =>
         let
           val value_ty = expr_value_type tm
           val target_ty = Type (ename, [state_ty, value_ty, resid_ty, abort_ty, in_ty, out_ty])
         in Type.constraint target_ty tm end
     | _ => tm)

  fun constrain_expr_value_type value_ty tm =
    (case !current_ref_expr_constraint of
       SOME (Type (ename, [state_ty, _, resid_ty, abort_ty, in_ty, out_ty])) =>
         let val target_ty = Type (ename, [state_ty, value_ty, resid_ty, abort_ty, in_ty, out_ty])
         in Type.constraint target_ty tm end
     | _ => tm)

  fun constrain_known_expr_value_type value_ty tm =
    (case fastype_of tm of
       Type (ename, [state_ty, _, resid_ty, abort_ty, in_ty, out_ty]) =>
         let val target_ty = Type (ename, [state_ty, value_ty, resid_ty, abort_ty, in_ty, out_ty])
         in Type.constraint target_ty tm end
     | _ => constrain_expr_value_type value_ty tm)

  fun expr_value_ty_of_cty cty =
    (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) cty of
       SOME ty => ty
     | NONE => C_Ast_Utils.hol_type_of cty)

  fun constrain_expr_cty cty tm =
    let val value_ty = expr_value_ty_of_cty cty
    in
      if value_ty = isa_dummyT then constrain_expr_side_types tm
      else constrain_expr_side_types (constrain_expr_value_type value_ty tm)
    end

  fun expr_type_with_value value_ty =
    (case !current_ref_expr_constraint of
       SOME (Type (ename, [state_ty, _, resid_ty, abort_ty, in_ty, out_ty])) =>
         SOME (Type (ename, [state_ty, value_ty, resid_ty, abort_ty, in_ty, out_ty]))
     | _ => NONE)

  fun function_body_type_with_value value_ty =
    (case !current_ref_expr_constraint of
       SOME (Type (_, [state_ty, _, _, abort_ty, in_ty, out_ty])) =>
         SOME (Type (\<^type_name>\<open>function_body\<close>, [state_ty, value_ty, abort_ty, in_ty, out_ty]))
     | _ => NONE)

  fun expr_type_from_tm value_ty tm =
    (case fastype_of tm of
       Type (ename, [state_ty, _, resid_ty, abort_ty, in_ty, out_ty]) =>
         SOME (Type (ename, [state_ty, value_ty, resid_ty, abort_ty, in_ty, out_ty]))
     | _ => expr_type_with_value value_ty)

  fun function_body_type_from_tm value_ty tm =
    (case fastype_of tm of
       Type (_, [state_ty, _, _, abort_ty, in_ty, out_ty]) =>
         SOME (Type (\<^type_name>\<open>function_body\<close>, [state_ty, value_ty, abort_ty, in_ty, out_ty]))
     | _ => function_body_type_with_value value_ty)

  fun constrain_expr_arrow arg_ty value_ty tm =
    (case expr_type_with_value value_ty of
       SOME expr_ty => Type.constraint (arg_ty --> expr_ty) tm
     | NONE => tm)

  fun constrain_expr_arrow_from_tm arg_ty value_ty side_tm tm =
    (case expr_type_from_tm value_ty side_tm of
       SOME expr_ty => Type.constraint (arg_ty --> expr_ty) tm
     | NONE => tm)

  fun constrain_function_body_arrow arg_ty value_ty tm =
    (case function_body_type_with_value value_ty of
       SOME body_ty => Type.constraint (arg_ty --> body_ty) tm
     | NONE => tm)

  fun constrain_function_body_arrow_from_tm arg_ty value_ty side_tm tm =
    (case function_body_type_from_tm value_ty side_tm of
       SOME body_ty => Type.constraint (arg_ty --> body_ty) tm
     | NONE => tm)

  fun local_ref_value_ty value_ty =
    Isa_Type (\<^type_name>\<open>focused\<close>,
      [Isa_Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty]),
       !current_ref_gv_ty, value_ty])

  fun mk_typed_funcall1_from_tm arg_tm res_value_ty fn_tm =
    (case fastype_of arg_tm of
       Type (ename, [state_ty, _, resid_ty, abort_ty, in_ty, out_ty]) =>
         let
           val arg_ty = expr_value_type arg_tm
           val body_ty = Type (\<^type_name>\<open>function_body\<close>, [state_ty, res_value_ty, abort_ty, in_ty, out_ty])
           val res_expr_ty = Type (ename, [state_ty, res_value_ty, resid_ty, abort_ty, in_ty, out_ty])
           val funcall1_ty = Isa_Type (\<^type_name>\<open>fun\<close>,
             [Isa_Type (\<^type_name>\<open>fun\<close>, [arg_ty, body_ty]),
              Isa_Type (\<^type_name>\<open>fun\<close>, [fastype_of arg_tm, res_expr_ty])])
         in
           Isa_Const (\<^const_name>\<open>funcall1\<close>, funcall1_ty)
             $ Type.constraint (arg_ty --> body_ty) fn_tm
             $ arg_tm
         end
     | _ => C_Term_Build.mk_funcall fn_tm [arg_tm])

  fun mk_typed_call_deep1_from_tm arg_tm res_value_ty fn_tm =
    (case fastype_of arg_tm of
       Type (ename, [state_ty, _, resid_ty, abort_ty, in_ty, out_ty]) =>
         let
           val arg_ty = expr_value_type arg_tm
           val body_ty = Type (\<^type_name>\<open>function_body\<close>, [state_ty, res_value_ty, abort_ty, in_ty, out_ty])
           val res_expr_ty = Type (ename, [state_ty, res_value_ty, resid_ty, abort_ty, in_ty, out_ty])
           val call_ty = Isa_Type (\<^type_name>\<open>fun\<close>, [body_ty, res_expr_ty])
           val deep_compose1_ty = Isa_Type (\<^type_name>\<open>fun\<close>,
             [call_ty,
              Isa_Type (\<^type_name>\<open>fun\<close>,
                [Isa_Type (\<^type_name>\<open>fun\<close>, [arg_ty, body_ty]),
                 Isa_Type (\<^type_name>\<open>fun\<close>, [arg_ty, res_expr_ty])])])
         in
           Isa_Const (\<^const_name>\<open>deep_compose1\<close>, deep_compose1_ty)
             $ Isa_Const (\<^const_name>\<open>call\<close>, call_ty)
             $ Type.constraint (arg_ty --> body_ty) fn_tm
         end
     | _ =>
         Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
           $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
           $ fn_tm)

  fun cty_of_hol_type T =
    if T = @{typ bool} then SOME C_Ast_Utils.CBool
    else if T = \<^typ>\<open>c_int\<close> then SOME C_Ast_Utils.CInt
    else if T = \<^typ>\<open>c_uint\<close> then SOME C_Ast_Utils.CUInt
    else if T = \<^typ>\<open>c_char\<close> then SOME C_Ast_Utils.CChar
    else if T = \<^typ>\<open>c_schar\<close> then SOME C_Ast_Utils.CSChar
    else if T = \<^typ>\<open>c_short\<close> then SOME C_Ast_Utils.CShort
    else if T = \<^typ>\<open>c_ushort\<close> then SOME C_Ast_Utils.CUShort
    else if T = \<^typ>\<open>c_long\<close> then SOME C_Ast_Utils.CLong
    else if T = \<^typ>\<open>c_ulong\<close> then SOME C_Ast_Utils.CULong
    else NONE

  (* Binary operator classification: arithmetic/comparison/bitwise operators are
     monadic and compose via bind2.
     NB: Must be defined before 'open C_Ast' which shadows the term type. *)
  datatype binop_kind = Monadic of term

  (* void* cast helper: generate c_cast_from_void with type-annotated prism.
     The prism constant c_void_cast_prism_for is adhoc-overloaded; the type annotation
     on the prism (constraining 'v to the target type) lets Isabelle resolve it.
     Must be defined before 'open C_Ast' to use Const/Free/dummyT/Type. *)
  fun mk_cast_from_void target_cty void_ptr_term =
    let val target_ty = C_Ast_Utils.hol_type_of target_cty
        val prism_ty = Type (\<^type_name>\<open>prism\<close>, [!current_ref_gv_ty, target_ty])
        val prism_const = Const (\<^const_name>\<open>c_void_cast_prism_for\<close>, prism_ty)
        val cast_const = Const (\<^const_name>\<open>c_cast_from_void\<close>, dummyT)
        val v = Free ("v__void_cast", dummyT)
        val cast_expr =
          C_Term_Build.mk_bind void_ptr_term
            (Term.lambda v (C_Term_Build.mk_literal (cast_const $ prism_const $ v)))
        val cast_value_ty =
          (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) (C_Ast_Utils.CPtr target_cty) of
             SOME ty => ty
           | NONE => Type (\<^type_name>\<open>focused\<close>, [dummyT, dummyT, target_ty]))
    in constrain_expr_side_types (constrain_expr_value_type cast_value_ty cast_expr)
    end

  fun mk_cast_from_void_in _ target_cty void_ptr_term =
    mk_cast_from_void target_cty void_ptr_term

  fun typed_ref_ty_of_cty cty =
    (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) (C_Ast_Utils.CPtr cty) of
       SOME ty => ty
     | NONE => isa_dummyT)

  (* Untyped void* cast helper: keep prism target type polymorphic so later
     context (e.g. indexing vs scalar dereference) can resolve it. *)
  fun mk_cast_from_void_untyped void_ptr_term =
    let val cast_const = Const (\<^const_name>\<open>c_cast_from_void\<close>, dummyT)
        val prism_const = Const (\<^const_name>\<open>c_void_cast_prism_for\<close>, dummyT)
        val v = Free ("v__void_cast", dummyT)
    in constrain_expr_side_types
         (C_Term_Build.mk_bind void_ptr_term
           (Term.lambda v (C_Term_Build.mk_literal (cast_const $ prism_const $ v)))) end

  fun scalar_pointer_value_hol_ty (C_Ast_Utils.CPtr inner) =
        let
          val inner_ty =
            (case inner of
               C_Ast_Utils.CBool => SOME @{typ bool}
             | C_Ast_Utils.CInt => SOME \<^typ>\<open>c_int\<close>
             | C_Ast_Utils.CUInt => SOME \<^typ>\<open>c_uint\<close>
             | C_Ast_Utils.CShort => SOME \<^typ>\<open>c_short\<close>
             | C_Ast_Utils.CUShort => SOME \<^typ>\<open>c_ushort\<close>
             | C_Ast_Utils.CLong => SOME (C_Ast_Utils.hol_type_of C_Ast_Utils.CLong)
             | C_Ast_Utils.CULong => SOME (C_Ast_Utils.hol_type_of C_Ast_Utils.CULong)
             | C_Ast_Utils.CLongLong => SOME \<^typ>\<open>c_long\<close>
             | C_Ast_Utils.CULongLong => SOME \<^typ>\<open>c_ulong\<close>
             | C_Ast_Utils.CInt128 => SOME \<^typ>\<open>c_int128\<close>
             | C_Ast_Utils.CUInt128 => SOME \<^typ>\<open>c_uint128\<close>
             | _ => NONE)
          val gref_ty =
            Isa_Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])
        in
          Option.map
            (fn ty => Isa_Type (\<^type_name>\<open>focused\<close>, [gref_ty, !current_ref_gv_ty, ty]))
            inner_ty
        end
    | scalar_pointer_value_hol_ty _ = NONE

  fun pointer_expr_value_hol_ty cty =
        let
          val gref_ty =
            Isa_Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])
          fun mk_focused ty =
            Isa_Type (\<^type_name>\<open>focused\<close>, [gref_ty, !current_ref_gv_ty, ty])
        in
          case cty of
            C_Ast_Utils.CPtr C_Ast_Utils.CVoid => SOME gref_ty
          | C_Ast_Utils.CPtr (C_Ast_Utils.CUnion _) => SOME gref_ty
          | C_Ast_Utils.CPtr C_Ast_Utils.CChar =>
              if uses_raw_pointer_model () then
                SOME (mk_focused \<^typ>\<open>c_char\<close>)
              else
                SOME (mk_focused (HOLogic.listT \<^typ>\<open>c_char\<close>))
          | _ =>
              (case scalar_pointer_value_hol_ty cty of
                 SOME ty => SOME ty
               | NONE =>
                   (case cty of
                      C_Ast_Utils.CPtr inner =>
                        (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) inner of
                           SOME inner_ty => SOME (mk_focused inner_ty)
                         | NONE => SOME gref_ty)
                   | _ => NONE))
        end

  fun list_backed_pointer_value_hol_ty (C_Ast_Utils.CPtr inner) =
        let
          val gref_ty =
            Isa_Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])
          val elem_ty =
            (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) inner of
               SOME ty => ty
             | NONE => C_Ast_Utils.hol_type_of inner)
        in
          if elem_ty = isa_dummyT then NONE
          else SOME (Isa_Type (\<^type_name>\<open>focused\<close>, [gref_ty, !current_ref_gv_ty, HOLogic.listT elem_ty]))
        end
    | list_backed_pointer_value_hol_ty _ = NONE

  (* C11 implicit integer promotion cast.
     Inserts c_scast or c_ucast when from_cty <> to_cty.
     Cast direction: signed source \<rightarrow> c_scast (sign-extend), unsigned \<rightarrow> c_ucast (zero-extend).
     Both c_scast/c_ucast are fully polymorphic: 'a word \<rightarrow> ('s, 'b word, ...) expression.
     Must be defined before 'open C_Ast' to use Const/Free/dummyT. *)
  fun mk_implicit_cast (tm, from_cty, to_cty) =
    let
      val tm_ty = expr_value_type tm
      val to_ty = C_Ast_Utils.hol_type_of to_cty
    in
    if from_cty = to_cty then
      if C_Ast_Utils.is_ptr from_cty then tm
      else if tm_ty <> isa_dummyT andalso tm_ty = to_ty then tm
      else
        let
          val v = Isa_Free ("v__idcast", to_ty)
        in
          C_Term_Build.mk_bind tm (Term.lambda v (C_Term_Build.mk_literal v))
        end
    else if tm_ty <> isa_dummyT andalso tm_ty = to_ty then tm
    else if C_Ast_Utils.is_bool to_cty then
      (* scalar -> _Bool : compare against zero *)
      if C_Ast_Utils.is_ptr from_cty then
        let val vty = expr_value_type tm
        in
          if (case vty of Type (\<^type_name>\<open>List.list\<close>, [_]) => true | _ => false)
          then
            let val v = Isa_Free ("v__promo", vty)
                val nil_term = Const (\<^const_name>\<open>Nil\<close>, vty)
                val neq_nil =
                  Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool})
                    $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, vty --> vty --> @{typ bool}) $ v $ nil_term)
            in C_Term_Build.mk_bind tm (Term.lambda v (C_Term_Build.mk_literal neq_nil)) end
          else
            let val v = Isa_Free ("v__promo", isa_dummyT)
                val addr_term =
                  Isa_Const (\<^const_name>\<open>address\<close>, isa_dummyT --> isa_dummyT) $ v
                val neq_zero =
                  Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool})
                    $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT --> isa_dummyT --> @{typ bool})
                         $ addr_term
                         $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
            in C_Term_Build.mk_bind tm (Term.lambda v (C_Term_Build.mk_literal neq_zero)) end
        end
      else
        let val from_ty = if C_Ast_Utils.is_bool from_cty
                          then @{typ bool}
                          else C_Ast_Utils.hol_type_of from_cty
            val v = Isa_Free ("v__promo", from_ty)
            val truthy_expr =
              if C_Ast_Utils.is_bool from_cty then
                C_Term_Build.mk_literal v
              else if C_Ast_Utils.is_signed from_cty then
                Const (\<^const_name>\<open>c_signed_truthy\<close>, isa_dummyT) $ v
              else
                Const (\<^const_name>\<open>c_unsigned_truthy\<close>, isa_dummyT) $ v
        in C_Term_Build.mk_bind tm (Term.lambda v truthy_expr) end
    else if C_Ast_Utils.is_bool from_cty then
      (* Bool \<rightarrow> integer: if b then 1 else 0 *)
      let val v = Isa_Free ("v__promo", @{typ bool})
          val one = C_Term_Build.mk_literal_num to_cty 1
          val zero = C_Term_Build.mk_literal_num to_cty 0
      in C_Term_Build.mk_bind tm
           (Term.lambda v (C_Term_Build.mk_two_armed_cond
              (C_Term_Build.mk_literal v) one zero)) end
    else if to_cty = C_Ast_Utils.CVoid then
      (* (void)expr is a no-op: just evaluate and discard the result *)
      tm
    else if C_Ast_Utils.is_ptr from_cty andalso C_Ast_Utils.is_ptr to_cty then
      let fun is_void_like C_Ast_Utils.CVoid = true
            | is_void_like (C_Ast_Utils.CUnion _) = true
            | is_void_like _ = false
      in case (from_cty, to_cty) of
         (C_Ast_Utils.CPtr from_inner, C_Ast_Utils.CPtr to_inner) =>
           if is_void_like from_inner andalso is_void_like to_inner then tm
           (* untyped -> T* : attach prism focus *)
           else if is_void_like from_inner then
             (case to_inner of
                C_Ast_Utils.CStruct _ => mk_cast_from_void to_inner tm
              | C_Ast_Utils.CUnion _ => mk_cast_from_void to_inner tm
              | _ =>
                  let val cast_term = mk_cast_from_void_untyped tm
                      val target_ty =
                        (case pointer_expr_value_hol_ty to_cty of
                           SOME ty => ty
                         | NONE => isa_dummyT)
                  in if target_ty = isa_dummyT then cast_term
                     else constrain_expr_value_type target_ty cast_term
                  end)
           (* T* -> untyped : strip focus *)
           else if is_void_like to_inner then
             let val source_ptr_ty =
                   (case pointer_expr_value_hol_ty from_cty of
                      SOME ty => ty
                    | NONE => isa_dummyT)
                 val tm' =
                   if source_ptr_ty = isa_dummyT then tm
                   else constrain_expr_value_type source_ptr_ty tm
                 val from_ty = expr_value_type tm'
                 val v = Isa_Free ("v__cast", if from_ty = isa_dummyT then isa_dummyT else from_ty)
                 val cast = Const (\<^const_name>\<open>c_cast_to_void\<close>, dummyT)
                 val void_ptr_ty =
                   (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) to_cty of
                      SOME ty => ty
                    | NONE => isa_dummyT)
                 val cast_term =
                   C_Term_Build.mk_bind tm' (Term.lambda v (C_Term_Build.mk_literal (cast $ v)))
             in if void_ptr_ty = isa_dummyT then cast_term
                else constrain_expr_value_type void_ptr_ty cast_term
             end
           (* T* -> U* where neither is void/union:
              reinterpret through void* so the resulting focused reference
              carries U's prism (byte-level view), rather than leaving the
              term at type T* while only changing the tracked C type. *)
           else if from_inner = to_inner then tm
           else
             let val tm' =
                   (case scalar_pointer_value_hol_ty from_cty of
                      SOME ptr_ty => constrain_expr_value_type ptr_ty tm
                    | NONE => tm)
                 val v = Free ("v__cast", dummyT)
                 val cast = Const (\<^const_name>\<open>c_cast_to_void\<close>, dummyT)
                 val as_void = C_Term_Build.mk_bind tm' (Term.lambda v (C_Term_Build.mk_literal (cast $ v)))
             in mk_cast_from_void_untyped as_void end
       | _ => tm
      end
    else if C_Ast_Utils.is_ptr from_cty then
      (* pointer -> integer cast via semantic uintptr value, then convert as needed *)
      let val ctxt = require_current_visible_ctxt ()
          val tm =
            (case pointer_expr_value_hol_ty from_cty of
               SOME ty => constrain_expr_value_type ty tm
             | NONE => tm)
          val ptr_ty = expr_value_type tm
          val v = Free ("v__ptrint", if ptr_ty = isa_dummyT then isa_dummyT else ptr_ty)
          val raw_uint_v = Free ("v__uintptr", @{typ int})
          val ptr_uint_cty = C_Ast_Utils.pointer_uint_cty ()
          val ptr_uint_ty = C_Ast_Utils.hol_type_of ptr_uint_cty
          val conv = resolve_required_current_visible_const "c_ptr_to_uintptr"
          val raw_ptr_ty =
            Isa_Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])
          val raw_v =
            (case fastype_of v of
               Term.Type (name, _) =>
                 if name = \<^type_name>\<open>focused\<close>
                 then Isa_Const (\<^const_name>\<open>unwrap_focused\<close>, isa_dummyT --> raw_ptr_ty) $ v
                 else v
             | _ => v)
          val as_uintptr =
            C_Term_Build.mk_bind tm
              (Term.lambda v
                (C_Term_Build.mk_bind
                  (C_Term_Build.mk_literal (conv $ raw_v))
                  (Term.lambda raw_uint_v
                    (C_Term_Build.mk_literal
                      (Isa_Const (\<^const_name>\<open>of_int\<close>, @{typ int} --> ptr_uint_ty) $ raw_uint_v)))))
          val as_uintptr = constrain_expr_value_type ptr_uint_ty as_uintptr
      in if to_cty = ptr_uint_cty then as_uintptr
         else mk_implicit_cast (as_uintptr, ptr_uint_cty, to_cty)
      end
    else if C_Ast_Utils.is_ptr to_cty then
      (* integer -> pointer cast: widen/narrow to ABI uintptr, build a raw pointer,
         then attach the target pointer view for non-void pointees. *)
      let val ptr_uint_cty = C_Ast_Utils.pointer_uint_cty ()
          val ptr_uint_ty = C_Ast_Utils.hol_type_of ptr_uint_cty
          val as_uintptr = if from_cty = ptr_uint_cty then tm
                           else mk_implicit_cast (tm, from_cty, ptr_uint_cty)
          val v = Free ("v__intptr", ptr_uint_ty)
          val conv = resolve_required_current_visible_const "c_uintptr_to_ptr"
          val raw_ptr_term =
            C_Term_Build.mk_bind as_uintptr
              (Term.lambda v
                (C_Term_Build.mk_literal
                  (conv $
                     (Isa_Const (\<^const_name>\<open>of_nat\<close>, @{typ nat} --> @{typ int})
                        $ (C_Term_Build.mk_unat v)))))
      in
        case to_cty of
          C_Ast_Utils.CPtr to_inner =>
            let
              fun is_void_like C_Ast_Utils.CVoid = true
                | is_void_like (C_Ast_Utils.CUnion _) = true
                | is_void_like _ = false
            in
              if is_void_like to_inner then
                (case pointer_expr_value_hol_ty to_cty of
                   SOME ty => constrain_expr_value_type ty raw_ptr_term
                 | NONE => raw_ptr_term)
              else
                mk_cast_from_void to_inner raw_ptr_term
            end
        | _ => raw_ptr_term
      end
    else let val cast_const =
               if C_Ast_Utils.is_signed from_cty
               then (case #signed_narrowing (C_Compiler.get_compiler_profile ()) of
                       C_Compiler.Checked =>
                         Const (\<^const_name>\<open>c_scast_checked\<close>, isa_dummyT)
                     | C_Compiler.Truncating =>
                         Const (\<^const_name>\<open>c_scast\<close>, isa_dummyT))
               else Const (\<^const_name>\<open>c_ucast\<close>, isa_dummyT)
             (* Type-annotate the lambda variable with the source HOL type
                so c_scast/c_ucast input type is fully determined. *)
             val from_ty =
               let val explicit = C_Ast_Utils.hol_type_of from_cty
               in if tm_ty <> isa_dummyT then tm_ty else explicit end
             val to_ty = C_Ast_Utils.hol_type_of to_cty
             val v = Isa_Free ("v__promo", from_ty)
         in constrain_expr_side_types
              (constrain_expr_value_type to_ty
                 (C_Term_Build.mk_bind tm (Term.lambda v (cast_const $ v)))) end
    end

  fun strip_isa_fun_type (Type ("fun", [A, B])) = A :: strip_isa_fun_type B
    | strip_isa_fun_type _ = []

  fun set_decl_prefix pfx = (current_decl_prefix := pfx)
  fun set_union_names names = current_union_names := names
  fun set_ref_universe_types addr_ty gv_ty =
    (current_ref_addr_ty := addr_ty; current_ref_gv_ty := gv_ty)
  fun set_ref_abort_type abort_opt = (current_ref_expr_constraint := abort_opt)
  fun set_pointer_model model = (current_pointer_model := model)


  open C_Ast

  fun unsupported construct =
    error ("micro_c_translate: unsupported C construct: " ^ construct)

  fun normalize_ref_universe_type tctx ty =
    let
      val addr_ty = C_Trans_Ctxt.get_ref_addr_ty tctx
      val gv_ty = C_Trans_Ctxt.get_ref_gv_ty tctx
      fun go (Term.Type (name, args)) =
            let
              val args' = List.map go args
            in
              (case args' of
                 [Term.Type (gname, [_ , _]), _, vty] =>
                   if Long_Name.base_name name = "focused"
                      andalso Long_Name.base_name gname = "gref"
                   then Isa_Type (name, [Isa_Type (gname, [addr_ty, gv_ty]), gv_ty, vty])
                   else Isa_Type (name, args')
               | _ => Isa_Type (name, args'))
            end
        | go t = t
    in go ty end

  fun mk_typed_ref_var tctx name alloc_expr =
    Isa_Free (name, normalize_ref_universe_type tctx (expr_value_type alloc_expr))

  fun resolve_visible_const_term ctxt short_name =
    let
      fun const_or_free x =
        (case Symtab.lookup (!defined_func_consts) x of
           SOME tm => SOME tm
         | NONE =>
             let
               val c_opt = Variable.lookup_const ctxt x
             in
               case c_opt of
                 SOME c =>
                   ((let val _ = Consts.type_scheme (Proof_Context.consts_of ctxt) c
                     in SOME (Isa_Const (c, isa_dummyT)) end)
                    handle TYPE _ => SOME (Isa_Free (x, isa_dummyT)))
               | NONE => SOME (Isa_Free (x, isa_dummyT))
             end)
      val fixed_result =
        (case Variable.lookup_fixed ctxt short_name of
           SOME x => const_or_free x
         | NONE => NONE)
      val direct =
        SOME (Proof_Context.read_const {proper = true, strict = false} ctxt short_name)
        handle ERROR _ => NONE
      val result =
        case fixed_result of
          SOME t => SOME t
        | NONE =>
          (case direct of
             SOME (Term.Const (n, _)) => SOME (Isa_Const (n, isa_dummyT))
           | SOME (Term.Free (x, _)) => const_or_free x
           | _ =>
               let
                 val full_name = Proof_Context.intern_const ctxt short_name
                 val thy = Proof_Context.theory_of ctxt
               in
                 if can (Sign.the_const_type thy) full_name
                 then SOME (Isa_Const (full_name, isa_dummyT))
                 else NONE
               end)
    in result end

  fun mk_flag_ref_type tctx =
    let
      val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
      val alloc_expr =
        C_Term_Build.mk_var_alloc_typed
          (C_Ast_Utils.hol_type_of C_Ast_Utils.CUInt) false_lit
    in
      normalize_ref_universe_type tctx (expr_value_type alloc_expr)
    end

  (* Translate a C binary operator to a HOL function constant, dispatching
     signed vs unsigned based on the operand type.
     Arithmetic, comparison and bitwise operations use the overflow-checked
     C operations from C_Numeric_Types which are monadic (they can abort). *)
  fun translate_binop cty CAddOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_add\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_add\<close>, isa_dummyT))
    | translate_binop cty CSubOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT))
    | translate_binop cty CMulOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_mul\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_mul\<close>, isa_dummyT))
    | translate_binop cty CDivOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_div\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_div\<close>, isa_dummyT))
    | translate_binop cty CRmdOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_mod\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_mod\<close>, isa_dummyT))
    | translate_binop cty CLeOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_less\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_less\<close>, isa_dummyT))
    | translate_binop cty CLeqOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_le\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_le\<close>, isa_dummyT))
    | translate_binop cty CGrOp0 =  (* reversed operands *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_less\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_less\<close>, isa_dummyT))
    | translate_binop cty CGeqOp0 =  (* reversed operands *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_le\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_le\<close>, isa_dummyT))
    | translate_binop cty CEqOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_eq\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_eq\<close>, isa_dummyT))
    | translate_binop cty CNeqOp0 =
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_neq\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_neq\<close>, isa_dummyT))
    | translate_binop cty CAndOp0 = (* bitwise AND *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_and\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_and\<close>, isa_dummyT))
    | translate_binop cty CXorOp0 = (* bitwise XOR *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_xor\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_xor\<close>, isa_dummyT))
    | translate_binop cty COrOp0 = (* bitwise OR *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_or\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_or\<close>, isa_dummyT))
    | translate_binop cty CShlOp0 = (* left shift *)
        if C_Ast_Utils.is_signed cty
        then Monadic (Isa_Const (\<^const_name>\<open>c_signed_shl\<close>, isa_dummyT))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_shl\<close>, isa_dummyT))
    | translate_binop cty CShrOp0 = (* right shift *)
        if C_Ast_Utils.is_signed cty
        then (case #signed_shr (C_Compiler.get_compiler_profile ()) of
                C_Compiler.ArithmeticShift =>
                  Monadic (Isa_Const (\<^const_name>\<open>c_signed_shr\<close>, isa_dummyT))
              | C_Compiler.ConservativeShift =>
                  Monadic (Isa_Const (\<^const_name>\<open>c_signed_shr_conservative\<close>, isa_dummyT)))
        else Monadic (Isa_Const (\<^const_name>\<open>c_unsigned_shr\<close>, isa_dummyT))
    | translate_binop _ _ = unsupported "unsupported binary operator"

  (* Check if a given aggregate name refers to a union (not a struct). *)
  fun is_union_aggregate name =
    List.exists (fn n => n = name) (!current_union_names)

  val struct_name_of_cty = C_Ast_Utils.struct_name_of_cty

  fun cty_of_decl_for_struct tctx (CDecl0 (specs, declrs, _)) =
        let
          val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
          val struct_names = C_Trans_Ctxt.get_struct_names tctx
          val base_cty =
            (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
               SOME ct => SOME ct
             | NONE =>
                 (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                    SOME sn => SOME (C_Ast_Utils.CStruct sn)
                  | NONE =>
                      (case C_Ast_Utils.extract_union_type_from_specs_full (!current_union_names) specs of
                         SOME un => SOME (C_Ast_Utils.CUnion un)
                       | NONE => NONE)))
          val ptr_depth =
            List.mapPartial
              (fn ((Some declr, _), _) => SOME (C_Ast_Utils.pointer_depth_of_declr declr)
                | _ => NONE) declrs
            |> (fn d :: _ => d | [] => 0)
        in
          Option.map (fn ct => C_Ast_Utils.apply_ptr_depth ct ptr_depth) base_cty
        end
    | cty_of_decl_for_struct _ _ = NONE

  (* Determine the C struct type of an expression used as a member-access base.
     Handles casts and expression wrappers around variables/member chains. *)
  fun determine_struct_type tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.get_struct_type tctx name of
             SOME sname => sname
           | NONE => error ("micro_c_translate: cannot determine struct type for: " ^ name)
        end
    | determine_struct_type tctx (CMember0 (inner_expr, field_ident, _, _)) =
        let val inner_struct = determine_struct_type tctx inner_expr
            val field_name = C_Ast_Utils.ident_name field_ident
        in case C_Trans_Ctxt.lookup_struct_field_type tctx inner_struct field_name of
             SOME (C_Ast_Utils.CStruct sname) => sname
           | SOME (C_Ast_Utils.CPtr (C_Ast_Utils.CStruct sname)) => sname
           | SOME (C_Ast_Utils.CUnion sname) => sname
           | SOME (C_Ast_Utils.CPtr (C_Ast_Utils.CUnion sname)) => sname
           | _ => error ("micro_c_translate: field " ^ field_name ^ " of " ^
                         inner_struct ^ " is not a struct/union type")
        end
    | determine_struct_type tctx (CUnary0 (CIndOp0, inner_expr, _)) =
        (* *p where p points to a struct — recurse to determine struct type *)
        determine_struct_type tctx inner_expr
    | determine_struct_type tctx (CIndex0 (inner_expr, _, _)) =
        (* arr[i] where arr is a struct field — the struct type comes from the array expression *)
        determine_struct_type tctx inner_expr
    | determine_struct_type tctx (CCast0 (decl, inner_expr, _)) =
        (case cty_of_decl_for_struct tctx decl of
           SOME cty =>
             (case struct_name_of_cty cty of
                SOME sname => sname
              | NONE => determine_struct_type tctx inner_expr)
         | NONE => determine_struct_type tctx inner_expr)
    | determine_struct_type tctx (CCond0 (_, Some then_expr, else_expr, _)) =
        (determine_struct_type tctx then_expr
         handle ERROR _ => determine_struct_type tctx else_expr)
    | determine_struct_type tctx (CComma0 (exprs, _)) =
        (case List.rev exprs of
           e :: _ => determine_struct_type tctx e
         | [] => error "micro_c_translate: empty comma expression")
    | determine_struct_type _ _ =
        error "micro_c_translate: struct member access on complex expression not yet supported"

  (* Resolve a struct field accessor/updater constant by naming convention.
     Prefix defaults to "c_" and can be overridden via command options. *)
  fun struct_accessor_name struct_name field_name =
    !current_decl_prefix ^ struct_name ^ "_" ^ field_name

  fun struct_updater_name struct_name field_name =
    "update_" ^ struct_accessor_name struct_name field_name

  fun struct_focus_name struct_name field_name =
    struct_accessor_name struct_name field_name ^ "_focus"

  fun resolve_const ctxt name =
    let val (full_name, _) = Term.dest_Const
          (Proof_Context.read_const {proper = true, strict = true} ctxt name)
    in Isa_Const (full_name, isa_dummyT) end

  fun try_resolve_const ctxt name =
    SOME (resolve_const ctxt name) handle ERROR _ => NONE

  fun pick_preferred_const_by_base ctxt pred =
    let
      val consts_info = Consts.dest (Proof_Context.consts_of ctxt)
      val names = map #1 (#constants consts_info)
      val matches = List.filter pred names
      fun base n = Long_Name.base_name n
      fun pref_rank n =
        let val b = base n in
          if String.isPrefix (!current_decl_prefix) b then 0
          else if String.isPrefix "c_" b then 1
          else 2
        end
      fun best [] = NONE
        | best (n :: ns) =
            SOME (List.foldl (fn (m, acc) => if pref_rank m < pref_rank acc then m else acc) n ns)
    in
      best matches
    end

  fun resolve_struct_accessor_const ctxt struct_name field_name =
    let
      val suffix = struct_name ^ "_" ^ field_name
      val explicit =
        [ struct_accessor_name struct_name field_name
        , (!current_decl_prefix ^ struct_name) ^ "." ^ struct_accessor_name struct_name field_name
        , struct_name ^ "." ^ struct_accessor_name struct_name field_name
        ]
      fun try_explicit [] = NONE
        | try_explicit (n :: ns) =
            (case try_resolve_const ctxt n of SOME c => SOME c | NONE => try_explicit ns)
    in
      case try_explicit explicit of
        SOME c => c
      | NONE =>
          (case pick_preferred_const_by_base ctxt
                  (fn full =>
                    let val b = Long_Name.base_name full in
                      String.isSuffix suffix b andalso
                      not (String.isPrefix "update_" b) andalso
                      not (String.isSuffix "_focus" b)
                    end) of
             SOME full => Isa_Const (full, isa_dummyT)
           | NONE =>
               error ("micro_c_translate: missing struct field accessor constant: " ^
                      struct_accessor_name struct_name field_name))
    end

  fun resolve_struct_updater_const ctxt struct_name field_name =
    let
      val accessor_const = resolve_struct_accessor_const ctxt struct_name field_name
      val (accessor_full, _) = Term.dest_Const accessor_const
      val qualifier = Long_Name.qualifier accessor_full
      val accessor_base = Long_Name.base_name accessor_full
      val updater_base = "update_" ^ accessor_base
      val qualified = if qualifier = "" then updater_base else qualifier ^ "." ^ updater_base
      val suffix = "update_" ^ struct_name ^ "_" ^ field_name
    in
      case try_resolve_const ctxt qualified of
        SOME c => c
      | NONE =>
          (case try_resolve_const ctxt updater_base of
             SOME c => c
           | NONE =>
               (case pick_preferred_const_by_base ctxt
                       (fn full => String.isSuffix suffix (Long_Name.base_name full)) of
                  SOME full => Isa_Const (full, isa_dummyT)
                | NONE =>
                    error ("micro_c_translate: missing struct field updater constant: " ^
                           struct_updater_name struct_name field_name)))
    end

  fun resolve_struct_focus_const ctxt struct_name field_name =
    let
      val accessor_const = resolve_struct_accessor_const ctxt struct_name field_name
      val updater_const = resolve_struct_updater_const ctxt struct_name field_name
      val (accessor_full, _) = Term.dest_Const accessor_const
      val qualifier = Long_Name.qualifier accessor_full
      val accessor_base = Long_Name.base_name accessor_full
      val focus_base = accessor_base ^ "_focus"
      val record_name = !current_decl_prefix ^ struct_name
      val candidates =
        [ if qualifier = "" then focus_base else qualifier ^ "." ^ focus_base
        , focus_base
        , struct_focus_name struct_name field_name
        , record_name ^ "." ^ struct_focus_name struct_name field_name
        , struct_name ^ "." ^ struct_focus_name struct_name field_name
        ]
      fun mk_focus_from_lens () =
        let
          val make_lens_const = resolve_const ctxt "make_lens_via_view_modify"
          val lens_to_focus_raw_const = resolve_const ctxt "lens_to_focus_raw"
          val abs_focus_const = resolve_const ctxt "Abs_focus"
          val lens =
            make_lens_const $ accessor_const $ updater_const
          val focus_raw = lens_to_focus_raw_const $ lens
        in
          abs_focus_const $ focus_raw
        end
      fun try_names [] = mk_focus_from_lens ()
        | try_names (n :: ns) =
            (resolve_const ctxt n handle ERROR _ => try_names ns)
    in
      try_names candidates
    end

  fun resolve_dereference_const ctxt =
    (let
       val (full_name, _) =
         Term.dest_Const
           (Proof_Context.read_const {proper = true, strict = false} ctxt "dereference_fun")
     in
       Isa_Const (full_name, isa_dummyT)
     end
     handle ERROR _ =>
       Isa_Const (\<^const_name>\<open>store_dereference_const\<close>, isa_dummyT))

  fun resolve_required_visible_const ctxt short_name =
    (case resolve_visible_const_term ctxt short_name of
       SOME tm => tm
     | NONE => error ("micro_c_translate: missing required interface constant: " ^ short_name))

  fun resolve_pointer_model_const ctxt label opt_name default_name =
    (case opt_name of
       SOME name => resolve_required_visible_const ctxt name
     | NONE => resolve_required_visible_const ctxt default_name)

  fun resolve_ptr_add_const ctxt =
    resolve_pointer_model_const ctxt "ptr_add:" (#ptr_add (!current_pointer_model)) "c_ptr_add"

  fun resolve_ptr_shift_signed_const ctxt =
    resolve_pointer_model_const ctxt "ptr_shift_signed:" (#ptr_shift_signed (!current_pointer_model)) "c_ptr_shift_signed"

  fun resolve_ptr_diff_const ctxt =
    resolve_pointer_model_const ctxt "ptr_diff:" (#ptr_diff (!current_pointer_model)) "c_ptr_diff"

  fun resolve_ptr_to_uintptr_const ctxt =
    resolve_required_visible_const ctxt "c_ptr_to_uintptr"

  fun resolve_uintptr_to_ptr_const ctxt =
    resolve_required_visible_const ctxt "c_uintptr_to_ptr"

  fun mk_resolved_var_alloc_typed ctxt val_hol_type init_expr =
    let val ref_const =
          (case resolve_visible_const_term ctxt "store_reference_const" of
             SOME tm => tm
           | NONE =>
               (if val_hol_type = isa_dummyT
                then Isa_Const (\<^const_name>\<open>store_reference_const\<close>, isa_dummyT)
                else Isa_Const (\<^const_name>\<open>store_reference_const\<close>, val_hol_type --> isa_dummyT)))
        val init_expr = constrain_expr_side_types init_expr
        val arg_ty =
          if val_hol_type = isa_dummyT then expr_value_type init_expr else val_hol_type
        val res_value_ty =
          if arg_ty = isa_dummyT then isa_dummyT else local_ref_value_ty arg_ty
        val ref_const =
          if arg_ty = isa_dummyT then ref_const
          else constrain_function_body_arrow_from_tm arg_ty res_value_ty init_expr ref_const
    in constrain_expr_side_types (mk_typed_funcall1_from_tm init_expr res_value_ty ref_const) end

  fun mk_resolved_var_alloc ctxt init_expr =
    mk_resolved_var_alloc_typed ctxt isa_dummyT init_expr

  fun raw_ptr_local_gref_typ () =
    Isa_Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])

  fun supports_raw_ptr_local_refs ctxt =
    let
      val raw_ptr_ty = raw_ptr_local_gref_typ ()
      val uninit = Isa_Const (\<^const_name>\<open>c_uninitialized\<close>, raw_ptr_ty)
      val probe = mk_resolved_var_alloc_typed ctxt raw_ptr_ty (C_Term_Build.mk_literal uninit)
      val _ = Syntax.check_term ctxt probe
    in true end
    handle ERROR _ => false
         | TYPE _ => false

  fun is_uninitialized_literal tm =
    (case Term.strip_comb tm of
       (hd, [arg]) =>
         (case (try Term.dest_Const hd, try Term.dest_Const arg) of
            (SOME (n1, _), SOME (n2, _)) =>
              n1 = \<^const_name>\<open>Core_Expression.literal\<close> andalso
              n2 = \<^const_name>\<open>c_uninitialized\<close>
          | _ => false)
     | _ => false)

  fun expr_value_ty_is_list_backed_ptr tm =
    (case expr_value_type tm of
       Term.Type (fname, [_, _, Term.Type (lname, [_])]) =>
         Long_Name.base_name fname = "focused" andalso Long_Name.base_name lname = "list"
     | Term.Type (lname, [_]) => Long_Name.base_name lname = "list"
     | _ => false)

  fun prefer_pointer_alias_storage alias_list_backed init_term =
    is_uninitialized_literal init_term orelse alias_list_backed orelse expr_value_ty_is_list_backed_ptr init_term

  fun pointer_alias_kind alias_list_backed =
    if alias_list_backed then C_Trans_Ctxt.ParamListPtr
    else C_Trans_Ctxt.Param

  fun pointer_alias_var_ty tctx alias_list_backed cty init_term =
    let
      val init_ty = expr_value_type init_term
      val fallback_ty =
        (case if alias_list_backed then list_backed_pointer_value_hol_ty cty
               else pointer_expr_value_hol_ty cty of
           SOME ty => ty
         | NONE => expr_value_ty_of_cty cty)
      val ty =
        if is_uninitialized_literal init_term orelse init_ty = isa_dummyT
        then fallback_ty
        else init_ty
    in normalize_ref_universe_type tctx ty end

  (* Variable read: delegates to mk_var_read. *)
  fun mk_resolved_var_read _ ref_var =
    constrain_expr_side_types (C_Term_Build.mk_var_read ref_var)

  fun mk_literal_value_read var =
    let
      val tm = C_Term_Build.mk_literal var
      val value_ty = fastype_of var
    in
      if value_ty = isa_dummyT then constrain_expr_side_types tm
      else constrain_known_expr_value_type value_ty tm
    end

  fun mk_resolved_deref_expr ctxt result_cty ptr_expr =
    let
      val ptr_expr = constrain_expr_side_types ptr_expr
      val deref_const = resolve_dereference_const ctxt
      val result_ty = expr_value_ty_of_cty result_cty
      val deref_fn =
        if result_ty = isa_dummyT then
          Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
            $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
            $ deref_const
        else mk_typed_call_deep1_from_tm ptr_expr result_ty deref_const
    in constrain_expr_cty result_cty
         (Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
            $ ptr_expr $ deref_fn)
    end

  fun mk_pair_eval unseq ltm rtm lvar rvar body =
    if unseq then
      C_Term_Build.mk_bind2_unseq (Term.lambda lvar (Term.lambda rvar body)) ltm rtm
    else
      C_Term_Build.mk_bind ltm (Term.lambda lvar
        (C_Term_Build.mk_bind rtm (Term.lambda rvar body)))

  fun mk_index_guard idx_p_cty i_var list_tm body_term =
    let
      val idx_nat = C_Term_Build.mk_unat i_var
      val len_tm =
        Isa_Const (\<^const_name>\<open>size\<close>, isa_dummyT --> @{typ nat}) $ list_tm
      val in_bounds =
        Isa_Const (\<^const_name>\<open>Orderings.less\<close>, @{typ nat} --> @{typ nat} --> @{typ bool})
          $ idx_nat $ len_tm
      val overflow = Isa_Const (\<^const_name>\<open>c_bounds_abort\<close>, isa_dummyT)
      val guarded_upper =
        C_Term_Build.mk_two_armed_cond (C_Term_Build.mk_literal in_bounds) body_term overflow
    in
      if C_Ast_Utils.is_signed idx_p_cty then
        let
          val lt_zero =
            C_Term_Build.mk_bind2
              (Isa_Const (\<^const_name>\<open>c_signed_less\<close>, isa_dummyT))
              (C_Term_Build.mk_literal i_var)
              (C_Term_Build.mk_literal_num idx_p_cty 0)
        in
          C_Term_Build.mk_two_armed_cond lt_zero overflow guarded_upper
        end
      else guarded_upper
    end

  fun struct_field_is_array_backed struct_name field_name =
        List.exists (fn fname => fname = field_name)
          (the_default [] (Symtab.lookup (!current_struct_array_fields) struct_name))

  fun expr_is_list_backed_array tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in
          Option.isSome (C_Trans_Ctxt.lookup_array_decl tctx name) orelse
          (case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.ParamListPtr, _, _) => true
           | _ => false)
        end
    | expr_is_list_backed_array tctx (CMember0 (expr, field_ident, _, _)) =
        ((let
            val struct_name = determine_struct_type tctx expr
            val field_name = C_Ast_Utils.ident_name field_ident
          in
            struct_field_is_array_backed struct_name field_name
          end) handle ERROR _ => false)
    | expr_is_list_backed_array _ _ = false

  fun use_raw_pointer_indexing tctx arr_expr =
    uses_raw_pointer_model () andalso not (expr_is_list_backed_array tctx arr_expr)

  fun is_nonnegative_int_const (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) = (n >= 0)
    | is_nonnegative_int_const _ = false

  fun pointer_arith_result_ty elem_cty =
    let
      val gref_ty = Isa_Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])
    in
      case elem_cty of
        C_Ast_Utils.CVoid => gref_ty
      | C_Ast_Utils.CUnion _ => gref_ty
      | _ =>
          (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) elem_cty of
             SOME inner_ty => Isa_Type (\<^type_name>\<open>focused\<close>, [gref_ty, !current_ref_gv_ty, inner_ty])
           | NONE => gref_ty)
    end

  fun mk_ptr_shifted_term ctxt ptr_var idx_var idx_p_cty elem_cty prefer_unsigned_add =
    let
      val stride_tm = HOLogic.mk_number @{typ nat} (C_Ast_Utils.sizeof_c_type elem_cty)
      val ptr_ty = fastype_of ptr_var
      val is_focused =
        (case ptr_ty of
           Term.Type (name, _) => name = \<^type_name>\<open>focused\<close>
         | _ => false)
      val raw_ptr =
        if is_focused then
          Isa_Const (\<^const_name>\<open>unwrap_focused\<close>, isa_dummyT --> isa_dummyT) $ ptr_var
        else ptr_var
      val signed_idx =
        Isa_Const (\<^const_name>\<open>signed\<close>, isa_dummyT --> @{typ int}) $ idx_var
      val shifted_raw =
        if C_Ast_Utils.is_signed idx_p_cty andalso not prefer_unsigned_add then
          resolve_ptr_shift_signed_const ctxt $ raw_ptr $ signed_idx $ stride_tm
        else
          resolve_ptr_add_const ctxt $ raw_ptr $ (C_Term_Build.mk_unat idx_var) $ stride_tm
    in
      if is_focused then
        Isa_Const (\<^const_name>\<open>make_focused\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
          $ shifted_raw
          $ (Isa_Const (\<^const_name>\<open>get_focus\<close>, isa_dummyT --> isa_dummyT) $ ptr_var)
      else shifted_raw
    end

  fun mk_raw_ptr_loc_expr ctxt unseq_operands ptr_term idx_term idx_cty elem_cty prefer_unsigned_add =
    let
      val ptr_ty0 = expr_value_type ptr_term
      val ptr_ty = if ptr_ty0 = isa_dummyT then pointer_arith_result_ty elem_cty else ptr_ty0
      val p_var = Isa_Free ("v__ptr", ptr_ty)
      val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
      val idx_p_term = mk_implicit_cast (idx_term, idx_cty, idx_p_cty)
      val idx_var_ty =
        let val ty = expr_value_type idx_p_term
        in if ty = isa_dummyT then C_Ast_Utils.hol_type_of idx_p_cty else ty end
      val i_var = Isa_Free ("v__idx", idx_var_ty)
      val shifted = mk_ptr_shifted_term ctxt p_var i_var idx_p_cty elem_cty prefer_unsigned_add
    in
      mk_pair_eval unseq_operands ptr_term idx_p_term p_var i_var (C_Term_Build.mk_literal shifted)
    end

  fun raw_struct_field_offset tctx struct_name field_name =
    (case C_Trans_Ctxt.get_struct_fields tctx struct_name of
       SOME fields =>
         let
           fun align_up_local (offset, alignment) =
             let val rem = offset mod alignment
             in if rem = 0 then offset else offset + (alignment - rem) end
           fun field_offset [] _ _ =
                 error ("micro_c_translate: unknown struct field in layout: " ^ field_name)
             | field_offset ((name, field_cty) :: rest) offset max_align =
                 let
                   val field_size = C_Ast_Utils.sizeof_c_type field_cty
                   val field_align = C_Ast_Utils.alignof_c_type field_cty
                   val aligned_offset = align_up_local (offset, field_align)
                 in
                   if name = field_name then aligned_offset
                   else field_offset rest (aligned_offset + field_size) (Int.max (max_align, field_align))
                 end
         in
           field_offset fields 0 1
         end
     | NONE => error ("micro_c_translate: unknown struct for field offset: " ^ struct_name))

  fun mk_raw_struct_field_ptr_expr tctx struct_name field_name raw_ptr_expr =
    let
      val ctxt = C_Trans_Ctxt.get_ctxt tctx
      val offset = raw_struct_field_offset tctx struct_name field_name
      val raw_ptr_ty = Term.Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])
      val ptr_ty0 = expr_value_type raw_ptr_expr
      val ptr_ty = if ptr_ty0 = isa_dummyT then raw_ptr_ty else ptr_ty0
      val ptr_var = Isa_Free ("v__base_ptr", ptr_ty)
      val shifted =
        resolve_ptr_add_const ctxt $ ptr_var $ HOLogic.mk_nat offset $ HOLogic.mk_nat 1
    in
      constrain_expr_side_types
        (constrain_expr_value_type raw_ptr_ty
          (C_Term_Build.mk_bind raw_ptr_expr
            (Term.lambda ptr_var (C_Term_Build.mk_literal shifted))))
    end

  fun mk_raw_struct_field_loc_expr tctx struct_name field_name field_cty raw_ptr_expr =
    let
      val ctxt = C_Trans_Ctxt.get_ctxt tctx
      val field_ptr = mk_raw_struct_field_ptr_expr tctx struct_name field_name raw_ptr_expr
    in
      mk_cast_from_void_in ctxt field_cty field_ptr
    end

  (* Helper for pre/post increment/decrement.
     is_inc: true for increment, false for decrement
     is_pre: true for pre (return new), false for post (return old)
     expr_fn / lvalue_fn: callbacks for translate_expr / translate_lvalue_location
     passed from the mutual-recursion group where those functions are in scope. *)
  fun translate_inc_dec _ _ tctx is_inc is_pre (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Local, ref_var, cty) =>
               (case cty of
                  C_Ast_Utils.CPtr inner =>
                    let
                      val read = C_Term_Build.mk_var_read ref_var
                      val old_var = Isa_Free ("v__old_ptr", isa_dummyT)
                      val idx_cty = if is_inc then C_Ast_Utils.CUInt else C_Ast_Utils.CInt
                      val idx_ty = C_Ast_Utils.hol_type_of idx_cty
                      val idx_term = HOLogic.mk_number idx_ty (if is_inc then 1 else ~1)
                      val shifted =
                        mk_ptr_shifted_term (C_Trans_Ctxt.get_ctxt tctx)
                          old_var idx_term idx_cty inner is_inc
                      val shifted_expr = C_Term_Build.mk_literal shifted
                      val write = C_Term_Build.mk_var_write ref_var shifted_expr
                      val return_term =
                        if is_pre then shifted_expr else C_Term_Build.mk_literal old_var
                    in
                      (C_Term_Build.mk_bind read (Term.lambda old_var
                         (C_Term_Build.mk_sequence write return_term)), cty)
                    end
                | _ =>
                    let val old_var = Isa_Free ("v__old", isa_dummyT)
                        val new_var = Isa_Free ("v__new", isa_dummyT)
                        val arith_cty = C_Ast_Utils.integer_promote cty
                        val one = C_Term_Build.mk_literal_num arith_cty 1
                        val arith_const =
                          if is_inc then
                            (if C_Ast_Utils.is_signed arith_cty
                             then Isa_Const (\<^const_name>\<open>c_signed_add\<close>, isa_dummyT)
                             else Isa_Const (\<^const_name>\<open>c_unsigned_add\<close>, isa_dummyT))
                          else
                            (if C_Ast_Utils.is_signed arith_cty
                             then Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT)
                             else Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT))
                        val read = C_Term_Build.mk_var_read ref_var
                        val old_promoted =
                          mk_implicit_cast (C_Term_Build.mk_literal old_var, cty, arith_cty)
                        val add = C_Term_Build.mk_bind2 arith_const
                                    old_promoted one
                        val new_assigned =
                          mk_implicit_cast (C_Term_Build.mk_literal new_var, arith_cty, cty)
                        val write = C_Term_Build.mk_var_write ref_var
                                      new_assigned
                        val return_term =
                          if is_pre then new_assigned else C_Term_Build.mk_literal old_var
                    in (C_Term_Build.mk_bind read (Term.lambda old_var
                         (C_Term_Build.mk_bind add (Term.lambda new_var
                           (C_Term_Build.mk_sequence write
                             return_term)))), cty) end)
           | SOME (C_Trans_Ctxt.LocalPtr, ref_var, cty) =>
               (case cty of
                  C_Ast_Utils.CPtr inner =>
                    let
                      val old_raw = C_Term_Build.mk_var_read ref_var
                      val old_var = Isa_Free ("v__old_ptr", raw_ptr_local_gref_typ ())
                      val typed_old =
                        (case inner of
                           C_Ast_Utils.CVoid => old_var
                         | C_Ast_Utils.CUnion _ => old_var
                         | _ =>
                             let
                               val target_ty = C_Ast_Utils.hol_type_of inner
                               val prism_ty = Isa_Type (\<^type_name>\<open>prism\<close>, [!current_ref_gv_ty, target_ty])
                               val prism_const = Isa_Const (\<^const_name>\<open>c_void_cast_prism_for\<close>, prism_ty)
                               val cast_const = Isa_Const (\<^const_name>\<open>c_cast_from_void\<close>, isa_dummyT)
                             in
                               cast_const $ prism_const $ old_var
                             end)
                      val idx_cty = if is_inc then C_Ast_Utils.CUInt else C_Ast_Utils.CInt
                      val idx_ty = C_Ast_Utils.hol_type_of idx_cty
                      val idx_term = HOLogic.mk_number idx_ty (if is_inc then 1 else ~1)
                      val shifted = mk_ptr_shifted_term (C_Trans_Ctxt.get_ctxt tctx) typed_old idx_term idx_cty inner is_inc
                      val shifted_expr = C_Term_Build.mk_literal shifted
                      val shifted_raw = mk_implicit_cast (shifted_expr, cty, C_Ast_Utils.CPtr C_Ast_Utils.CVoid)
                      val new_raw = Isa_Free ("v__new_ptr", raw_ptr_local_gref_typ ())
                      val return_term =
                        if is_pre then shifted_expr else C_Term_Build.mk_literal old_var
                    in (C_Term_Build.mk_bind old_raw (Term.lambda old_var
                         (C_Term_Build.mk_bind shifted_raw (Term.lambda new_raw
                           (C_Term_Build.mk_sequence
                             (C_Term_Build.mk_var_write ref_var (C_Term_Build.mk_literal new_raw))
                             return_term)))), cty)
                    end
                | _ => error ("micro_c_translate: internal error: non-pointer LocalPtr: " ^ name))
           | SOME (C_Trans_Ctxt.Param, _, _) =>
               error ("micro_c_translate: cannot increment/decrement parameter: " ^ name)
           | SOME (C_Trans_Ctxt.ParamListPtr, _, _) =>
               error ("micro_c_translate: cannot increment/decrement parameter: " ^ name)
           | NONE =>
               (case C_Trans_Ctxt.lookup_global_const tctx name of
                  SOME _ =>
                    error ("micro_c_translate: cannot increment/decrement global constant: " ^ name)
                | NONE =>
                    error ("micro_c_translate: undefined variable: " ^ name))
        end
    (* inc/dec through pointer dereference *)
    | translate_inc_dec expr_fn _ tctx is_inc is_pre (CUnary0 (CIndOp0, ptr_expr, _)) =
        let val (ptr_term, ptr_cty) = expr_fn tctx ptr_expr
            val pointee_cty =
              (case ptr_cty of C_Ast_Utils.CPtr inner => inner
                             | _ => unsupported "increment/decrement dereference on non-pointer")
            val arith_cty = C_Ast_Utils.integer_promote pointee_cty
            val one = C_Term_Build.mk_literal_num arith_cty 1
            val arith_const =
              if is_inc then
                (if C_Ast_Utils.is_signed arith_cty
                 then Isa_Const (\<^const_name>\<open>c_signed_add\<close>, isa_dummyT)
                 else Isa_Const (\<^const_name>\<open>c_unsigned_add\<close>, isa_dummyT))
              else
                (if C_Ast_Utils.is_signed arith_cty
                 then Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT)
                 else Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT))
            val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
            val old_var = Isa_Free ("v__old", isa_dummyT)
            val new_var = Isa_Free ("v__new", isa_dummyT)
            val old_promoted =
              mk_implicit_cast (C_Term_Build.mk_literal old_var, pointee_cty, arith_cty)
            val add = C_Term_Build.mk_bind2 arith_const old_promoted one
            val new_assigned =
              mk_implicit_cast (C_Term_Build.mk_literal new_var, arith_cty, pointee_cty)
            val return_term =
              if is_pre then new_assigned else C_Term_Build.mk_literal old_var
        in (C_Term_Build.mk_bind ptr_term (Term.lambda ptr_var
              (C_Term_Build.mk_bind
                (C_Term_Build.mk_deref (C_Term_Build.mk_literal ptr_var))
                (Term.lambda old_var
                  (C_Term_Build.mk_bind add (Term.lambda new_var
                    (C_Term_Build.mk_sequence
                      (C_Term_Build.mk_ptr_write
                        (C_Term_Build.mk_literal ptr_var)
                        new_assigned)
                      return_term)))))),
            pointee_cty) end
    (* inc/dec struct field via p->f or s.f *)
    | translate_inc_dec expr_fn lvalue_fn tctx is_inc is_pre (CMember0 (expr, field_ident, is_ptr, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val accessor_const = resolve_struct_accessor_const ctxt struct_name field_name
            val updater_const = resolve_struct_updater_const ctxt struct_name field_name
            val ptr_term = if is_ptr then #1 (expr_fn tctx expr)
                           else #1 (lvalue_fn tctx expr)
            val field_cty =
              (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                 SOME cty => cty
               | NONE => unsupported ("unknown struct field: " ^ struct_name ^ "." ^ field_name))
            val arith_cty = C_Ast_Utils.integer_promote field_cty
            val one = C_Term_Build.mk_literal_num arith_cty 1
            val arith_const =
              if is_inc then
                (if C_Ast_Utils.is_signed arith_cty
                 then Isa_Const (\<^const_name>\<open>c_signed_add\<close>, isa_dummyT)
                 else Isa_Const (\<^const_name>\<open>c_unsigned_add\<close>, isa_dummyT))
              else
                (if C_Ast_Utils.is_signed arith_cty
                 then Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT)
                 else Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT))
            val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
            val struct_var = Isa_Free ("v__struct", isa_dummyT)
            val new_var = Isa_Free ("v__new", isa_dummyT)
            val old_val = accessor_const $ struct_var
            val old_promoted =
              mk_implicit_cast (C_Term_Build.mk_literal old_val, field_cty, arith_cty)
            val add = C_Term_Build.mk_bind2 arith_const old_promoted one
            val new_assigned =
              mk_implicit_cast (C_Term_Build.mk_literal new_var, arith_cty, field_cty)
            val return_term =
              if is_pre then new_assigned else C_Term_Build.mk_literal old_val
            val updated_struct =
              updater_const
                $ Term.lambda (Isa_Free ("_uu", isa_dummyT)) new_assigned
                $ struct_var
        in (C_Term_Build.mk_bind ptr_term (Term.lambda ptr_var
              (C_Term_Build.mk_bind
                (C_Term_Build.mk_deref (C_Term_Build.mk_literal ptr_var))
                (Term.lambda struct_var
                  (C_Term_Build.mk_bind add (Term.lambda new_var
                    (C_Term_Build.mk_sequence
                      (C_Term_Build.mk_ptr_write
                        (C_Term_Build.mk_literal ptr_var)
                        (C_Term_Build.mk_literal updated_struct))
                      return_term)))))),
            field_cty) end
    (* inc/dec array element via arr[i] *)
    | translate_inc_dec expr_fn _ tctx is_inc is_pre (CIndex0 (arr_expr, idx_expr, _)) =
        let val (arr_term, arr_cty) = expr_fn tctx arr_expr
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val deref_const = resolve_dereference_const ctxt
            val (idx_term_raw, idx_cty) = expr_fn tctx idx_expr
            val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
            val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
            val elem_cty = (case arr_cty of
                              C_Ast_Utils.CPtr inner => inner
                            | _ => unsupported "increment/decrement on non-array indexing")
            val arith_cty = C_Ast_Utils.integer_promote elem_cty
            val one = C_Term_Build.mk_literal_num arith_cty 1
            val arith_const =
              if is_inc then
                (if C_Ast_Utils.is_signed arith_cty
                 then Isa_Const (\<^const_name>\<open>c_signed_add\<close>, isa_dummyT)
                 else Isa_Const (\<^const_name>\<open>c_unsigned_add\<close>, isa_dummyT))
              else
                (if C_Ast_Utils.is_signed arith_cty
                 then Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT)
                 else Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT))
            val a_var = Isa_Free ("v__arr", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val loc_var = Isa_Free ("v__loc", isa_dummyT)
            val list_var = Isa_Free ("v__arr_vals", isa_dummyT)
            val deref_expr =
              Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ a_var)
                $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                     $ deref_const)
            val old_var = Isa_Free ("v__old", isa_dummyT)
            val new_var = Isa_Free ("v__new", isa_dummyT)
            val unseq_operands =
              C_Ast_Utils.expr_has_side_effect arr_expr orelse
              C_Ast_Utils.expr_has_side_effect idx_expr
            val focused = C_Term_Build.mk_focus_nth (C_Term_Build.mk_unat i_var) a_var
            val loc_expr =
              mk_pair_eval unseq_operands arr_term idx_term a_var i_var
                (let
                  val list_ty =
                    (case C_Ast_Utils.hol_type_of elem_cty of
                       t => if t = isa_dummyT then isa_dummyT else Isa_Type (\<^type_name>\<open>list\<close>, [t]))
                  val list_var = Isa_Free ("v__arr_vals", list_ty)
                in C_Term_Build.mk_bind deref_expr
                     (Term.lambda list_var (mk_index_guard idx_p_cty i_var list_var (C_Term_Build.mk_literal focused))) end)
            val old_promoted =
              mk_implicit_cast (C_Term_Build.mk_literal old_var, elem_cty, arith_cty)
            val add = C_Term_Build.mk_bind2 arith_const old_promoted one
            val new_assigned =
              mk_implicit_cast (C_Term_Build.mk_literal new_var, arith_cty, elem_cty)
            val return_term =
              if is_pre then new_assigned else C_Term_Build.mk_literal old_var
        in (C_Term_Build.mk_bind loc_expr (Term.lambda loc_var
              (C_Term_Build.mk_bind
                (C_Term_Build.mk_deref (C_Term_Build.mk_literal loc_var))
                (Term.lambda old_var
                  (C_Term_Build.mk_bind add (Term.lambda new_var
                    (C_Term_Build.mk_sequence
                      (C_Term_Build.mk_ptr_write
                        (C_Term_Build.mk_literal loc_var)
                        new_assigned)
                      return_term)))))),
            elem_cty) end
    | translate_inc_dec _ _ _ _ _ _ =
        unsupported "increment/decrement on unsupported expression"



  fun is_shift_binop CShlOp0 = true
    | is_shift_binop CShrOp0 = true
    | is_shift_binop _ = false

  (* C11 compound assignment arithmetic:
     e1 op= e2 is computed in the same arithmetic type as e1 op e2
     (with integer promotions/usual conversions), then converted back to e1 type. *)
  fun prepare_compound_operands lhs_cty rhs_tm rhs_cty binop lhs_old_tm =
    if is_shift_binop binop then
      let
        val lhs_prom_cty = C_Ast_Utils.integer_promote lhs_cty
        val rhs_prom_cty = C_Ast_Utils.integer_promote rhs_cty
        val lhs_prom = mk_implicit_cast (lhs_old_tm, lhs_cty, lhs_prom_cty)
        val rhs_prom =
          mk_implicit_cast
            (mk_implicit_cast (rhs_tm, rhs_cty, rhs_prom_cty), rhs_prom_cty, lhs_prom_cty)
      in
        (lhs_prom_cty, lhs_prom, rhs_prom)
      end
    else
      let
        val op_cty = C_Ast_Utils.usual_arith_conv (lhs_cty, rhs_cty)
        val lhs_prom = mk_implicit_cast (lhs_old_tm, lhs_cty, op_cty)
        val rhs_prom = mk_implicit_cast (rhs_tm, rhs_cty, op_cty)
      in
        (op_cty, lhs_prom, rhs_prom)
      end

  fun compound_op_cty lhs_cty rhs_cty binop =
    if is_shift_binop binop
    then C_Ast_Utils.integer_promote lhs_cty
    else C_Ast_Utils.usual_arith_conv (lhs_cty, rhs_cty)

  (* Map compound assignment operators to their binary operator equivalents *)
  fun compound_assign_to_binop CAddAssOp0 = SOME CAddOp0
    | compound_assign_to_binop CSubAssOp0 = SOME CSubOp0
    | compound_assign_to_binop CMulAssOp0 = SOME CMulOp0
    | compound_assign_to_binop CDivAssOp0 = SOME CDivOp0
    | compound_assign_to_binop CRmdAssOp0 = SOME CRmdOp0
    | compound_assign_to_binop CShlAssOp0 = SOME CShlOp0
    | compound_assign_to_binop CShrAssOp0 = SOME CShrOp0
    | compound_assign_to_binop CAndAssOp0 = SOME CAndOp0
    | compound_assign_to_binop CXorAssOp0 = SOME CXorOp0
    | compound_assign_to_binop COrAssOp0  = SOME COrOp0
    | compound_assign_to_binop _ = NONE

  val intinf_to_int_checked = C_Ast_Utils.intinf_to_int_checked

  val cty_bit_width = C_Ast_Utils.bit_width_of
  val sizeof_c_type = C_Ast_Utils.sizeof_c_type
  val alignof_c_type = C_Ast_Utils.alignof_c_type

  fun align_up (offset, alignment) =
    let val rem = offset mod alignment
    in if rem = 0 then offset else offset + (alignment - rem) end

  (* Compute struct layout with ABI alignment padding.
     Each field aligned to alignof(field); total rounded up to max alignment. *)
  fun struct_layout (fields : (string * C_Ast_Utils.c_numeric_type) list) =
    let
      val (total_size, max_align, rev_layout) =
        List.foldl (fn ((field_name, field_cty), (offset, max_a, acc)) =>
          let
            val field_size = sizeof_c_type field_cty
            val field_align = alignof_c_type field_cty
            val aligned_offset = align_up (offset, field_align)
          in
            (aligned_offset + field_size, Int.max (max_a, field_align),
             (field_name, aligned_offset, field_cty) :: acc)
          end)
          (0, 1, []) fields
      val final_size = if max_align > 0 then align_up (total_size, max_align) else total_size
    in
      (rev rev_layout, final_size)
    end

  fun sizeof_struct fields = #2 (struct_layout fields)

  fun struct_field_offset (fields : (string * C_Ast_Utils.c_numeric_type) list) field_name =
    (case List.find (fn (name, _, _) => name = field_name) (#1 (struct_layout fields)) of
       SOME (_, offset, _) => offset
     | NONE => error ("micro_c_translate: unknown struct field in layout: " ^ field_name))

  fun fits_int_literal_cty cty n =
    case cty_bit_width cty of
      NONE => false
    | SOME bits =>
        let val two_pow = IntInf.pow (2, bits)
        in
          if C_Ast_Utils.is_signed cty then
            let
              val maxp1 = IntInf.pow (2, bits - 1)
              val lo = ~ maxp1
              val hi = maxp1 - 1
            in lo <= n andalso n <= hi end
          else
            0 <= n andalso n < two_pow
        end

  fun int_literal_candidates repr (Flags0 bits) =
    let
      val is_unsigned = IntInf.andb (bits, 1) <> 0
      val is_long = IntInf.andb (bits, 2) <> 0
      val is_long_long = IntInf.andb (bits, 4) <> 0
      val non_decimal =
        (case repr of DecRepr0 => false | HexRepr0 => true | OctalRepr0 => true)
    in
      case (is_unsigned, is_long, is_long_long, non_decimal) of
        (false, false, false, false) =>
          [C_Ast_Utils.CInt, C_Ast_Utils.CLong, C_Ast_Utils.CLongLong]
      | (false, false, false, true) =>
          [C_Ast_Utils.CInt, C_Ast_Utils.CUInt,
           C_Ast_Utils.CLong, C_Ast_Utils.CULong,
           C_Ast_Utils.CLongLong, C_Ast_Utils.CULongLong]
      | (true, false, false, _) =>
          [C_Ast_Utils.CUInt, C_Ast_Utils.CULong, C_Ast_Utils.CULongLong]
      | (false, true, false, false) =>
          [C_Ast_Utils.CLong, C_Ast_Utils.CLongLong]
      | (false, true, false, true) =>
          [C_Ast_Utils.CLong, C_Ast_Utils.CULong,
           C_Ast_Utils.CLongLong, C_Ast_Utils.CULongLong]
      | (true, true, false, _) =>
          [C_Ast_Utils.CULong, C_Ast_Utils.CULongLong]
      | (false, false, true, false) =>
          [C_Ast_Utils.CLongLong]
      | (false, false, true, true) =>
          [C_Ast_Utils.CLongLong, C_Ast_Utils.CULongLong]
      | (true, false, true, _) =>
          [C_Ast_Utils.CULongLong]
      | _ => unsupported "unsupported integer literal suffix combination"
    end

  fun choose_int_literal_type n repr flags =
    let
      fun first_fit [] =
            unsupported ("integer literal out of supported range: " ^ IntInf.toString n)
        | first_fit (cty :: rest) =
            if fits_int_literal_cty cty n then cty else first_fit rest
    in
      first_fit (int_literal_candidates repr flags)
    end



  (* --- Switch statement helpers --- *)

  (* Unwrap nested case/default labels from the C AST.
     CCase0(1, CCase0(2, stmt)) becomes labels=[SOME 1, SOME 2], stmt *)
  fun unwrap_case_labels (CCase0 (expr, inner, _)) labels =
        unwrap_case_labels inner (SOME expr :: labels)
    | unwrap_case_labels (CDefault0 (inner, _)) labels =
        unwrap_case_labels inner (NONE :: labels)
    | unwrap_case_labels stmt labels = (rev labels, stmt)

  (* Extract case groups from flat switch body items.
     Returns list of {labels, body, has_break}. *)
  fun extract_switch_groups items =
    let
      fun close_group labels body has_break acc =
        if null labels then acc
        else {labels = rev labels, body = rev body, has_break = has_break} :: acc
      fun walk [] labels body acc = rev (close_group labels body false acc)
        | walk (CBlockStmt0 (stmt as CCase0 _) :: rest) labels body acc =
            let val acc' = close_group labels body false acc
                val (new_labels, first_stmt) = unwrap_case_labels stmt []
            in walk rest new_labels [CBlockStmt0 first_stmt] acc' end
        | walk (CBlockStmt0 (stmt as CDefault0 _) :: rest) labels body acc =
            let val acc' = close_group labels body false acc
                val (new_labels, first_stmt) = unwrap_case_labels stmt []
            in walk rest new_labels [CBlockStmt0 first_stmt] acc' end
        | walk (CBlockStmt0 (CBreak0 _) :: rest) labels body acc =
            let val acc' = close_group labels body true acc
            in walk rest [] [] acc' end
        | walk (item :: rest) labels body acc =
            walk rest labels (item :: body) acc
    in walk items [] [] [] end

  (* Translate a case label expression to a pure HOL value *)
  fun case_label_value switch_cty _ (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) =
        HOLogic.mk_number (C_Ast_Utils.hol_type_of switch_cty)
          (intinf_to_int_checked "switch case label" n)
    | case_label_value switch_cty tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_enum_const tctx name of
             SOME v => HOLogic.mk_number (C_Ast_Utils.hol_type_of switch_cty) v
           | NONE => error ("micro_c_translate: unsupported case label: " ^ name)
        end
    | case_label_value _ _ _ = error "micro_c_translate: unsupported case label expression"

  (* Build condition for a case group: switch_var = label1 OR ... OR labelN.
     Default labels map to default_cond, which should be ~(any explicit case matched). *)
  fun make_switch_cond switch_var switch_cty tctx default_cond labels =
    let fun one_label (SOME e) =
              HOLogic.mk_eq (switch_var, case_label_value switch_cty tctx e)
          | one_label NONE = default_cond
        fun combine [] = Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool})
          | combine [c] = c
          | combine (c :: cs) =
              Isa_Const (\<^const_name>\<open>HOL.disj\<close>,
                @{typ bool} --> @{typ bool} --> @{typ bool}) $ c $ (combine cs)
    in combine (List.map one_label labels) end

  (* Build a condition that says whether switch_var matches any explicit case label. *)
  fun make_any_case_match switch_var switch_cty tctx groups =
    let val labels = List.concat (List.map #labels groups)
                    |> List.mapPartial I
        fun one_label e = HOLogic.mk_eq (switch_var, case_label_value switch_cty tctx e)
        fun combine [] = Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool})
          | combine [c] = c
          | combine (c :: cs) =
              Isa_Const (\<^const_name>\<open>HOL.disj\<close>,
                @{typ bool} --> @{typ bool} --> @{typ bool}) $ c $ (combine cs)
    in combine (List.map one_label labels) end

  (* --- Break/continue AST scanners --- *)

  fun contains_break (CBreak0 _) = true
    | contains_break (CCompound0 (_, items, _)) = List.exists block_has_break items
    | contains_break (CIf0 (_, t_br, e_opt, _)) =
        contains_break t_br orelse
        (case e_opt of Some e => contains_break e | None => false)
    | contains_break (CSwitch0 _) = false  (* break in switch exits switch, not loop *)
    | contains_break (CFor0 _) = false     (* break in nested loop is local *)
    | contains_break (CWhile0 _) = false
    | contains_break _ = false
  and block_has_break (CBlockStmt0 s) = contains_break s
    | block_has_break _ = false

  fun contains_continue (CCont0 _) = true
    | contains_continue (CCompound0 (_, items, _)) = List.exists block_has_continue items
    | contains_continue (CIf0 (_, t_br, e_opt, _)) =
        contains_continue t_br orelse
        (case e_opt of Some e => contains_continue e | None => false)
    | contains_continue (CFor0 _) = false
    | contains_continue (CWhile0 _) = false
    | contains_continue _ = false
  and block_has_continue (CBlockStmt0 s) = contains_continue s
    | block_has_continue _ = false

  fun is_zero_int_const (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) = (n = 0)
    | is_zero_int_const (CCast0 (_, e, _)) = is_zero_int_const e
    | is_zero_int_const _ = false

  fun mk_ptr_is_null ptr_term =
    let val p = Isa_Free ("v__ptrcmp", isa_dummyT)
        val is_null =
          Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT --> isa_dummyT --> @{typ bool})
            $ (Isa_Const (\<^const_name>\<open>address\<close>, isa_dummyT --> isa_dummyT) $ p)
            $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT)
    in C_Term_Build.mk_bind ptr_term (Term.lambda p (C_Term_Build.mk_literal is_null)) end

  (* translate_expr returns (term * c_numeric_type).
     The type tracks the C type of the expression for binary operator dispatch.
     CInt is used as default when the actual type is unknown/irrelevant. *)
  fun translate_expr _ (CConst0 (CIntConst0 (CInteger0 (n, repr, flags), _))) =
        let val cty = choose_int_literal_type n repr flags
            val n_int = intinf_to_int_checked "integer literal" n
        in (C_Term_Build.mk_literal_num cty n_int, cty)
        end
    | translate_expr tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Param, var, cty) => (mk_literal_value_read var, cty)
           | SOME (C_Trans_Ctxt.ParamListPtr, var, cty) => (mk_literal_value_read var, cty)
           | SOME (C_Trans_Ctxt.Local, var, cty) =>
               (* For local arrays, the ref IS the pointer (array-to-pointer decay).
                  Return it directly so CIndex0's deref accesses the list correctly.
                  For regular locals, use generic dereference to keep the monad universe
                  polymorphic across pure helper calls. *)
               if Option.isSome (C_Trans_Ctxt.lookup_array_decl tctx name)
               then (C_Term_Build.mk_literal var, cty)
               else (C_Term_Build.mk_var_read var, cty)
           | SOME (C_Trans_Ctxt.LocalPtr, var, cty) =>
               (mk_implicit_cast (C_Term_Build.mk_var_read var, C_Ast_Utils.CPtr C_Ast_Utils.CVoid, cty), cty)
           | NONE =>
               (* Fallback: check global consts, then enum constants *)
               (case C_Trans_Ctxt.lookup_global_const tctx name of
                  SOME (tm, cty) =>
                    (case C_Trans_Ctxt.lookup_array_decl tctx name of
                       SOME (elem_cty, _) => (C_Term_Build.mk_literal tm, C_Ast_Utils.CPtr elem_cty)
                     | NONE => (C_Term_Build.mk_literal tm, cty))
                | NONE =>
               (case C_Trans_Ctxt.lookup_enum_const tctx name of
                  SOME value => (C_Term_Build.mk_literal_int value, C_Ast_Utils.CInt)
                | NONE => error ("micro_c_translate: undefined variable: " ^ name)))
        end
    | translate_expr tctx (CBinary0 (binop, lhs, rhs, _)) =
        let val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val (lhs', lhs_cty) = translate_expr tctx lhs
            val (rhs', rhs_cty) = translate_expr tctx rhs
            val unseq_operands =
              C_Ast_Utils.expr_has_side_effect lhs orelse C_Ast_Utils.expr_has_side_effect rhs
            val _ =
              if unseq_operands andalso C_Ast_Utils.expr_has_unsequenced_ub_risk lhs rhs then
                unsupported "potential unsequenced side-effect UB in binary expression"
              else ()
            fun to_bool (tm, cty) = mk_implicit_cast (tm, cty, C_Ast_Utils.CBool)
            fun mk_list_ptr_add ptr_term idx_term idx_cty elem_cty =
              let val ptr_ty = expr_value_type ptr_term
                  val p_var = Isa_Free ("v__ptr", if ptr_ty = isa_dummyT then isa_dummyT else ptr_ty)
                  val i_var = Isa_Free ("v__idx", isa_dummyT)
                  val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
                  val idx_p_term = mk_implicit_cast (idx_term, idx_cty, idx_p_cty)
                  val focused = C_Term_Build.mk_focus_nth (C_Term_Build.mk_unat i_var) p_var
                  val focused_lit = C_Term_Build.mk_literal focused
                  val list_ty =
                    (case C_Ast_Utils.hol_type_of elem_cty of
                       t => if t = isa_dummyT then isa_dummyT
                            else Isa_Type (\<^type_name>\<open>list\<close>, [t]))
                  val list_var = Isa_Free ("v__ptr_vals", list_ty)
                  val deref_const = resolve_dereference_const ctxt
                  val deref_expr =
                    Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                      $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ p_var)
                      $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                           $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                           $ deref_const)
                  val guarded =
                    C_Term_Build.mk_bind deref_expr
                      (Term.lambda list_var (mk_index_guard idx_p_cty i_var list_var focused_lit))
              in (mk_pair_eval unseq_operands ptr_term idx_p_term p_var i_var guarded,
                  C_Ast_Utils.CPtr elem_cty)
              end
            fun mk_raw_ptr_add ptr_term idx_term idx_cty elem_cty prefer_unsigned_add =
              (mk_raw_ptr_loc_expr ctxt unseq_operands ptr_term idx_term idx_cty elem_cty prefer_unsigned_add,
               C_Ast_Utils.CPtr elem_cty)
            fun mk_ptr_relcmp const_name short_name =
              let val lhs_c =
                    (case pointer_expr_value_hol_ty lhs_cty of
                       SOME ty => constrain_expr_value_type ty lhs'
                     | NONE => lhs')
                  val rhs_c =
                    (case pointer_expr_value_hol_ty rhs_cty of
                       SOME ty => constrain_expr_value_type ty rhs'
                     | NONE => rhs')
                  val lhs_ptr_ty = expr_value_type lhs_c
                  val rhs_ptr_ty = expr_value_type rhs_c
                  val p_var = Isa_Free ("v__lptr", lhs_ptr_ty)
                  val q_var = Isa_Free ("v__rptr", rhs_ptr_ty)
                  val raw_ptr_ty =
                    Isa_Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])
                  fun raw_ptr_of ptr_ty ptr_var =
                    (case ptr_ty of
                       Term.Type (name, _) =>
                         if name = \<^type_name>\<open>focused\<close>
                         then Isa_Const (\<^const_name>\<open>unwrap_focused\<close>, isa_dummyT --> raw_ptr_ty) $ ptr_var
                         else ptr_var
                     | _ => ptr_var)
                  val p_raw = raw_ptr_of lhs_ptr_ty p_var
                  val q_raw = raw_ptr_of rhs_ptr_ty q_var
                  val cmp_const =
                    Type.constraint (raw_ptr_ty --> raw_ptr_ty --> @{typ bool})
                      (if uses_raw_pointer_model () then resolve_required_visible_const ctxt short_name
                       else Isa_Const (const_name, isa_dummyT))
                  val cmp_body = cmp_const $ p_raw $ q_raw
              in (mk_pair_eval unseq_operands lhs_c rhs_c p_var q_var
                    (C_Term_Build.mk_literal cmp_body),
                  C_Ast_Utils.CBool)
              end
        in
        case binop of
          (* C logical operators short-circuit and return _Bool *)
          CLndOp0 =>
            let val lhs_bool = to_bool (lhs', lhs_cty)
                val rhs_bool = to_bool (rhs', rhs_cty)
                val v = Isa_Free ("v__lhsb", @{typ bool})
            in (C_Term_Build.mk_bind lhs_bool (Term.lambda v
                  (C_Term_Build.mk_two_armed_cond
                    (C_Term_Build.mk_literal v)
                    rhs_bool
                    (C_Term_Build.mk_literal (Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool}))))),
                C_Ast_Utils.CBool)
            end
        | CLorOp0 =>
            let val lhs_bool = to_bool (lhs', lhs_cty)
                val rhs_bool = to_bool (rhs', rhs_cty)
                val v = Isa_Free ("v__lhsb", @{typ bool})
            in (C_Term_Build.mk_bind lhs_bool (Term.lambda v
                  (C_Term_Build.mk_two_armed_cond
                    (C_Term_Build.mk_literal v)
                    (C_Term_Build.mk_literal (Isa_Const (\<^const_name>\<open>HOL.True\<close>, @{typ bool})))
                    rhs_bool)),
                C_Ast_Utils.CBool)
            end
        | _ =>
            (* Pointer arithmetic: p + n or n + p via focus_nth *)
            (case (binop, lhs_cty, rhs_cty) of
              (CEqOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                let val l = Isa_Free ("v__lptr", isa_dummyT)
                    val r = Isa_Free ("v__rptr", isa_dummyT)
                    val eq_t = Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT --> isa_dummyT --> @{typ bool}) $ l $ r
                in (mk_pair_eval unseq_operands lhs' rhs' l r (C_Term_Build.mk_literal eq_t),
                    C_Ast_Utils.CBool)
                end
            | (CNeqOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                let val l = Isa_Free ("v__lptr", isa_dummyT)
                    val r = Isa_Free ("v__rptr", isa_dummyT)
                    val neq_t =
                      Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool})
                        $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT --> isa_dummyT --> @{typ bool}) $ l $ r)
                in (mk_pair_eval unseq_operands lhs' rhs' l r (C_Term_Build.mk_literal neq_t),
                    C_Ast_Utils.CBool)
                end
            | (CEqOp0, C_Ast_Utils.CPtr _, _) =>
                if is_zero_int_const rhs then
                  (mk_ptr_is_null lhs', C_Ast_Utils.CBool)
                else
                  unsupported "pointer comparison with non-pointer operand"
            | (CEqOp0, _, C_Ast_Utils.CPtr _) =>
                if is_zero_int_const lhs then
                  (mk_ptr_is_null rhs', C_Ast_Utils.CBool)
                else
                  unsupported "pointer comparison with non-pointer operand"
            | (CNeqOp0, C_Ast_Utils.CPtr _, _) =>
                if is_zero_int_const rhs then
                  let val b = Isa_Free ("v__isnull", @{typ bool})
                  in (C_Term_Build.mk_bind (mk_ptr_is_null lhs') (Term.lambda b
                        (C_Term_Build.mk_literal
                          (Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool}) $ b))),
                      C_Ast_Utils.CBool)
                  end
                else
                  unsupported "pointer comparison with non-pointer operand"
            | (CNeqOp0, _, C_Ast_Utils.CPtr _) =>
                if is_zero_int_const lhs then
                  let val b = Isa_Free ("v__isnull", @{typ bool})
                  in (C_Term_Build.mk_bind (mk_ptr_is_null rhs') (Term.lambda b
                        (C_Term_Build.mk_literal
                          (Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool}) $ b))),
                      C_Ast_Utils.CBool)
                  end
                else
                  unsupported "pointer comparison with non-pointer operand"
            | (CLeOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                mk_ptr_relcmp \<^const_name>\<open>c_ptr_less\<close> "c_ptr_less"
            | (CLeqOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                mk_ptr_relcmp \<^const_name>\<open>c_ptr_le\<close> "c_ptr_le"
            | (CGrOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                mk_ptr_relcmp \<^const_name>\<open>c_ptr_greater\<close> "c_ptr_greater"
            | (CGeqOp0, C_Ast_Utils.CPtr _, C_Ast_Utils.CPtr _) =>
                mk_ptr_relcmp \<^const_name>\<open>c_ptr_ge\<close> "c_ptr_ge"
            | (CLeOp0, C_Ast_Utils.CPtr _, _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CLeOp0, _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CLeqOp0, C_Ast_Utils.CPtr _, _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CLeqOp0, _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CGrOp0, C_Ast_Utils.CPtr _, _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CGrOp0, _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CGeqOp0, C_Ast_Utils.CPtr _, _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CGeqOp0, _, C_Ast_Utils.CPtr _) =>
                unsupported "pointer relational comparison with non-pointer operand"
            | (CAddOp0, C_Ast_Utils.CPtr elem_cty, _) =>
                if uses_raw_pointer_model () andalso not (expr_is_list_backed_array tctx lhs) then
                  mk_raw_ptr_add lhs' rhs' rhs_cty elem_cty (is_nonnegative_int_const rhs)
                else
                  mk_list_ptr_add lhs' rhs' rhs_cty elem_cty
            | (CAddOp0, _, C_Ast_Utils.CPtr elem_cty) =>
                (* n + p = p + n *)
                if uses_raw_pointer_model () andalso not (expr_is_list_backed_array tctx rhs) then
                  mk_raw_ptr_add rhs' lhs' lhs_cty elem_cty (is_nonnegative_int_const lhs)
                else
                  mk_list_ptr_add rhs' lhs' lhs_cty elem_cty
            | (CSubOp0, C_Ast_Utils.CPtr elem_cty, C_Ast_Utils.CPtr _) =>
                let val isa_ty = C_Ast_Utils.hol_type_of elem_cty
                    val itself_ty = Isa_Type (\<^type_name>\<open>itself\<close>, [isa_ty])
                    val type_term = Isa_Const (\<^const_name>\<open>Pure.type\<close>, itself_ty)
                    val stride = Isa_Const (\<^const_name>\<open>c_sizeof\<close>,
                                    itself_ty --> @{typ nat}) $ type_term
                    val lhs' =
                      (case pointer_expr_value_hol_ty lhs_cty of
                         SOME ty => constrain_expr_value_type ty lhs'
                       | NONE => lhs')
                    val rhs' =
                      (case pointer_expr_value_hol_ty rhs_cty of
                         SOME ty => constrain_expr_value_type ty rhs'
                       | NONE => rhs')
                    val lhs_ptr_ty = expr_value_type lhs'
                    val rhs_ptr_ty = expr_value_type rhs'
                    val diff_raw_ty = @{typ int}
                    val diff_value_ty = C_Ast_Utils.hol_type_of (C_Ast_Utils.pointer_int_cty ())
                    val p_var = Isa_Free ("v__lptr", lhs_ptr_ty)
                    val q_var = Isa_Free ("v__rptr", rhs_ptr_ty)
                    val raw_ptr_ty =
                      Isa_Type (\<^type_name>\<open>gref\<close>, [!current_ref_addr_ty, !current_ref_gv_ty])
                    fun raw_ptr_of ptr_ty ptr_var =
                      (case ptr_ty of
                         Term.Type (name, _) =>
                           if name = \<^type_name>\<open>focused\<close>
                           then Isa_Const (\<^const_name>\<open>unwrap_focused\<close>, isa_dummyT --> raw_ptr_ty) $ ptr_var
                           else ptr_var
                       | _ => ptr_var)
                    val p_raw = raw_ptr_of lhs_ptr_ty p_var
                    val q_raw = raw_ptr_of rhs_ptr_ty q_var
                    val diff_const =
                      Type.constraint (raw_ptr_ty --> raw_ptr_ty --> @{typ nat} --> diff_raw_ty)
                        (if uses_raw_pointer_model () then resolve_ptr_diff_const ctxt
                         else Isa_Const (\<^const_name>\<open>c_ptr_diff\<close>, isa_dummyT))
                    val diff_body =
                      Isa_Const (\<^const_name>\<open>of_int\<close>, diff_raw_ty --> diff_value_ty)
                        $ (diff_const $ p_raw $ q_raw $ stride)
                    val f = Type.constraint (lhs_ptr_ty --> rhs_ptr_ty --> diff_value_ty)
                              (Term.lambda p_var (Term.lambda q_var diff_body))
                    val diff_expr0 = C_Term_Build.mk_bindlift2 f lhs' rhs'
                    val diff_expr =
                      (case expr_type_from_tm diff_value_ty lhs' of
                         SOME ty => Type.constraint ty diff_expr0
                       | NONE => constrain_known_expr_value_type diff_value_ty diff_expr0)
                in (constrain_expr_side_types diff_expr,
                    C_Ast_Utils.pointer_int_cty ())
                end
            | _ =>
                let
                  (* C11 integer promotion and usual arithmetic conversions.
                     Shifts: each operand independently promoted, result = promoted LHS.
                     Other ops: usual_arith_conv determines common type. *)
                  val is_shift = case binop of CShlOp0 => true | CShrOp0 => true | _ => false
                  val (cty, lhs_p, rhs_p) =
                    if is_shift then
                      let val lp_cty = C_Ast_Utils.integer_promote lhs_cty
                          val rp_cty = C_Ast_Utils.integer_promote rhs_cty
                      in (lp_cty,
                          mk_implicit_cast (lhs', lhs_cty, lp_cty),
                          mk_implicit_cast
                            (mk_implicit_cast (rhs', rhs_cty, rp_cty), rp_cty, lp_cty)) end
                    else
                      let val conv_cty = C_Ast_Utils.usual_arith_conv (lhs_cty, rhs_cty)
                      in (conv_cty,
                          mk_implicit_cast (lhs', lhs_cty, conv_cty),
                          mk_implicit_cast (rhs', rhs_cty, conv_cty)) end
                  (* For > and >=, swap operands to use < and <= *)
                  val (l, r) = case binop of CGrOp0 => (rhs_p, lhs_p)
                                           | CGeqOp0 => (rhs_p, lhs_p)
                                           | _ => (lhs_p, rhs_p)
                  (* Comparisons return CBool — they produce Isabelle bool values *)
                  val result_cty = case binop of
                      CLeOp0 => C_Ast_Utils.CBool | CLeqOp0 => C_Ast_Utils.CBool
                    | CGrOp0 => C_Ast_Utils.CBool | CGeqOp0 => C_Ast_Utils.CBool
                    | CEqOp0 => C_Ast_Utils.CBool | CNeqOp0 => C_Ast_Utils.CBool
                    | _ => cty
                in case translate_binop cty binop of
                     Monadic f =>
                       ((if unseq_operands then C_Term_Build.mk_bind2_unseq f l r
                         else C_Term_Build.mk_bind2 f l r), result_cty)
                end)
        end
    (* p->field = rhs  /  s.field = rhs : struct/union field write *)
    | translate_expr tctx (CAssign0 (CAssignOp0, CMember0 (expr, field_ident, is_ptr, _), rhs, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
        in if is_union_aggregate struct_name then
          (* Union field write: cast to typed ref, then write *)
          let val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                                 SOME cty => cty
                               | NONE => unsupported ("unknown union field type: " ^ struct_name ^ "." ^ field_name))
              val ptr_expr = if is_ptr then #1 (translate_expr tctx expr)
                             else #1 (translate_lvalue_location tctx expr)
              val (rhs', rhs_cty) = translate_expr tctx rhs
              val rhs_cast = mk_implicit_cast (rhs', rhs_cty, field_cty)
              val cast_expr = mk_cast_from_void_in (C_Trans_Ctxt.get_ctxt tctx) field_cty ptr_expr
              val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
              val ref_var = Isa_Free ("v__uref", typed_ref_ty_of_cty field_cty)
              val unseq_lhs_rhs =
                C_Ast_Utils.expr_has_side_effect expr orelse C_Ast_Utils.expr_has_side_effect rhs
              val _ =
                if unseq_lhs_rhs andalso C_Ast_Utils.expr_has_unsequenced_ub_risk expr rhs then
                  unsupported "potential unsequenced side-effect UB in union-field assignment"
                else ()
              val assign_fun =
                Term.lambda rhs_var (Term.lambda ref_var
                  (C_Term_Build.mk_sequence
                    (C_Term_Build.mk_ptr_write
                      (C_Term_Build.mk_literal ref_var)
                      (C_Term_Build.mk_literal rhs_var))
                    (C_Term_Build.mk_literal rhs_var)))
              val assign_term =
                (if unseq_lhs_rhs
                 then C_Term_Build.mk_bind2_unseq assign_fun rhs_cast cast_expr
                 else C_Term_Build.mk_bind2 assign_fun rhs_cast cast_expr)
          in (assign_term, field_cty) end
        else
        let val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val updater_const = resolve_struct_updater_const ctxt struct_name field_name
            val (ptr_expr, ptr_is_raw) =
              if is_ptr then
                (case expr of
                   CCast0 (_, inner_expr, _) =>
                     let val (inner_ptr, inner_cty) = translate_expr tctx inner_expr
                     in case inner_cty of
                          C_Ast_Utils.CPtr C_Ast_Utils.CVoid => (inner_ptr, true)
                        | C_Ast_Utils.CPtr (C_Ast_Utils.CUnion _) => (inner_ptr, true)
                        | _ => (#1 (translate_expr tctx expr), false)
                     end
                 | _ => (#1 (translate_expr tctx expr), false))
              else
                (#1 (translate_lvalue_location tctx expr), false)
            val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                               SOME cty => cty
                             | NONE => unsupported ("unknown struct field type: " ^ struct_name ^ "." ^ field_name))
            val (rhs', rhs_cty) = translate_expr tctx rhs
            val rhs_cast = mk_implicit_cast (rhs', rhs_cty, field_cty)
            val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
            val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
            val struct_var = Isa_Free ("v__struct", isa_dummyT)
            val dummy_var = Isa_Free ("_uu__", isa_dummyT)
            val updated_struct =
              updater_const $ (Term.lambda dummy_var rhs_var) $ struct_var
            val unseq_lhs_rhs =
              C_Ast_Utils.expr_has_side_effect expr orelse C_Ast_Utils.expr_has_side_effect rhs
            val _ =
              if unseq_lhs_rhs andalso C_Ast_Utils.expr_has_unsequenced_ub_risk expr rhs then
                unsupported "potential unsequenced side-effect UB in struct-field assignment"
              else ()
        in
          if ptr_is_raw then
            let
              val field_loc_expr = mk_raw_struct_field_loc_expr tctx struct_name field_name field_cty ptr_expr
              val ref_var = Isa_Free ("v__field_ref", typed_ref_ty_of_cty field_cty)
              val assign_fun =
                Term.lambda rhs_var (Term.lambda ref_var
                  (C_Term_Build.mk_sequence
                    (C_Term_Build.mk_ptr_write
                      (C_Term_Build.mk_literal ref_var)
                      (C_Term_Build.mk_literal rhs_var))
                    (C_Term_Build.mk_literal rhs_var)))
              val assign_term =
                (if unseq_lhs_rhs
                 then C_Term_Build.mk_bind2_unseq assign_fun rhs_cast field_loc_expr
                 else C_Term_Build.mk_bind2 assign_fun rhs_cast field_loc_expr)
            in (assign_term, field_cty) end
          else
            let
              val assign_fun =
                Term.lambda rhs_var (Term.lambda ptr_var
                  (C_Term_Build.mk_bind
                    (C_Term_Build.mk_deref (C_Term_Build.mk_literal ptr_var))
                    (Term.lambda struct_var
                      (C_Term_Build.mk_sequence
                        (C_Term_Build.mk_ptr_write
                          (C_Term_Build.mk_literal ptr_var)
                          (C_Term_Build.mk_literal updated_struct))
                        (C_Term_Build.mk_literal rhs_var)))))
              val assign_term =
                (if unseq_lhs_rhs
                 then C_Term_Build.mk_bind2_unseq assign_fun rhs_cast ptr_expr
                 else C_Term_Build.mk_bind2 assign_fun rhs_cast ptr_expr)
            in (assign_term, field_cty) end
        end end
    (* p->field op= rhs  /  s.field op= rhs : compound struct/union field write *)
    | translate_expr tctx (CAssign0 (asgn_op, CMember0 (expr, field_ident, is_ptr, _), rhs, _)) =
        (case compound_assign_to_binop asgn_op of
           SOME binop =>
             let val field_name = C_Ast_Utils.ident_name field_ident
                 val struct_name = determine_struct_type tctx expr
                 val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                                    SOME cty => cty
                                  | NONE => unsupported ("unknown field type: " ^ struct_name ^ "." ^ field_name))
                 val (ptr_term, ptr_is_raw) =
                   if is_ptr then
                     (case expr of
                        CCast0 (_, inner_expr, _) =>
                          let val (inner_ptr, inner_cty) = translate_expr tctx inner_expr
                          in case inner_cty of
                               C_Ast_Utils.CPtr C_Ast_Utils.CVoid => (inner_ptr, true)
                             | C_Ast_Utils.CPtr (C_Ast_Utils.CUnion _) => (inner_ptr, true)
                             | _ => (#1 (translate_expr tctx expr), false)
                          end
                      | _ => (#1 (translate_expr tctx expr), false))
                   else
                     (#1 (translate_lvalue_location tctx expr), false)
                 val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
                 val op_cty = compound_op_cty field_cty rhs_cty binop
                 val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
                 val old_var = Isa_Free ("v__old", isa_dummyT)
                 val new_var = Isa_Free ("v__new", isa_dummyT)
                 val unseq_lhs_rhs =
                   C_Ast_Utils.expr_has_side_effect expr orelse C_Ast_Utils.expr_has_side_effect rhs
                 val _ =
                   if unseq_lhs_rhs andalso C_Ast_Utils.expr_has_unsequenced_ub_risk expr rhs then
                     unsupported "potential unsequenced side-effect UB in field compound assignment"
                   else ()
             in if is_union_aggregate struct_name then
               (* Union: cast void ptr to typed ref, deref, compute, write back *)
               case translate_binop op_cty binop of
                  Monadic f =>
                    let
                      val ref_var = Isa_Free ("v__uref", typed_ref_ty_of_cty field_cty)
                      val cast_expr = mk_cast_from_void_in (C_Trans_Ctxt.get_ctxt tctx) field_cty ptr_term
                      val combine_rhs_ref =
                        if unseq_lhs_rhs then C_Term_Build.mk_bind2_unseq else C_Term_Build.mk_bind2
                      val assign_fun =
                        Term.lambda rhs_var (Term.lambda ref_var
                          (C_Term_Build.mk_bind
                            (C_Term_Build.mk_deref (C_Term_Build.mk_literal ref_var))
                            (Term.lambda old_var
                              (let
                                 val (_, old_prom, rhs_prom) =
                                   prepare_compound_operands
                                     field_cty
                                     (C_Term_Build.mk_literal rhs_var)
                                     rhs_cty
                                     binop
                                     (C_Term_Build.mk_literal old_var)
                               in
                                 C_Term_Build.mk_bind
                                   (C_Term_Build.mk_bind2 f old_prom rhs_prom)
                                   (Term.lambda new_var
                                     (let
                                        val new_assigned =
                                          mk_implicit_cast
                                            (C_Term_Build.mk_literal new_var, op_cty, field_cty)
                                      in
                                        C_Term_Build.mk_sequence
                                          (C_Term_Build.mk_ptr_write
                                            (C_Term_Build.mk_literal ref_var)
                                            new_assigned)
                                          new_assigned
                                      end))
                               end))))
                      val assign_term = combine_rhs_ref assign_fun rhs_term_raw cast_expr
                    in
                      (assign_term, field_cty)
                    end
             else if ptr_is_raw then
               case translate_binop op_cty binop of
                  Monadic f =>
                    let
                      val ref_var = Isa_Free ("v__field_ref", typed_ref_ty_of_cty field_cty)
                      val field_loc_expr = mk_raw_struct_field_loc_expr tctx struct_name field_name field_cty ptr_term
                      val combine_rhs_ref =
                        if unseq_lhs_rhs then C_Term_Build.mk_bind2_unseq else C_Term_Build.mk_bind2
                      val assign_fun =
                        Term.lambda rhs_var (Term.lambda ref_var
                          (C_Term_Build.mk_bind
                            (C_Term_Build.mk_deref (C_Term_Build.mk_literal ref_var))
                            (Term.lambda old_var
                              (let
                                 val (_, old_prom, rhs_prom) =
                                   prepare_compound_operands
                                     field_cty
                                     (C_Term_Build.mk_literal rhs_var)
                                     rhs_cty
                                     binop
                                     (C_Term_Build.mk_literal old_var)
                               in
                                 C_Term_Build.mk_bind
                                   (C_Term_Build.mk_bind2 f old_prom rhs_prom)
                                   (Term.lambda new_var
                                     (let
                                        val new_assigned =
                                          mk_implicit_cast
                                            (C_Term_Build.mk_literal new_var, op_cty, field_cty)
                                      in
                                        C_Term_Build.mk_sequence
                                          (C_Term_Build.mk_ptr_write
                                            (C_Term_Build.mk_literal ref_var)
                                            new_assigned)
                                          new_assigned
                                      end))
                               end))))
                      val assign_term = combine_rhs_ref assign_fun rhs_term_raw field_loc_expr
                    in
                      (assign_term, field_cty)
                    end
             else
               (* Struct: deref ptr, accessor/updater pattern *)
               let val ctxt = C_Trans_Ctxt.get_ctxt tctx
                   val accessor_const = resolve_struct_accessor_const ctxt struct_name field_name
                   val updater_const = resolve_struct_updater_const ctxt struct_name field_name
                   val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
                   val struct_var = Isa_Free ("v__struct", isa_dummyT)
                   val old_val = accessor_const $ struct_var
               in case translate_binop op_cty binop of
                  Monadic f =>
                    let
                      val combine_rhs_ptr =
                        if unseq_lhs_rhs then C_Term_Build.mk_bind2_unseq else C_Term_Build.mk_bind2
                      val assign_fun =
                        Term.lambda rhs_var (Term.lambda ptr_var
                          (C_Term_Build.mk_bind
                            (C_Term_Build.mk_deref (C_Term_Build.mk_literal ptr_var))
                            (Term.lambda struct_var
                              (C_Term_Build.mk_bind
                                (let
                                   val (_, old_prom, rhs_prom) =
                                     prepare_compound_operands
                                       field_cty
                                       (C_Term_Build.mk_literal rhs_var)
                                       rhs_cty
                                       binop
                                       (C_Term_Build.mk_literal old_val)
                                 in
                                   C_Term_Build.mk_bind2 f old_prom rhs_prom
                                 end)
                                (Term.lambda new_var
                                  (let
                                     val new_assigned =
                                       mk_implicit_cast
                                         (C_Term_Build.mk_literal new_var, op_cty, field_cty)
                                     val updated_struct =
                                       updater_const
                                         $ Term.lambda (Isa_Free ("_uu", isa_dummyT)) new_assigned
                                         $ struct_var
                                   in
                                     C_Term_Build.mk_sequence
                                       (C_Term_Build.mk_ptr_write
                                         (C_Term_Build.mk_literal ptr_var)
                                         (C_Term_Build.mk_literal updated_struct))
                                       new_assigned
                                   end))))))
                      val assign_term = combine_rhs_ptr assign_fun rhs_term_raw ptr_term
                    in
                      (assign_term, field_cty)
                    end
               end
             end
         | NONE => unsupported "unsupported compound operator on struct field")
    (* p->field[idx] = rhs  /  s.field[idx] = rhs : struct field array write *)
    | translate_expr tctx (CAssign0 (CAssignOp0,
          CIndex0 (CMember0 (expr, field_ident, is_ptr, _), idx_expr, _), rhs, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val accessor_const = resolve_struct_accessor_const ctxt struct_name field_name
            val updater_const = resolve_struct_updater_const ctxt struct_name field_name
            val deref_const = resolve_dereference_const ctxt
            val ptr_expr = if is_ptr then #1 (translate_expr tctx expr)
                           else #1 (translate_lvalue_location tctx expr)
            val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
            val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
            val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
            val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
            (* Side effects in rhs/idx/ptr are safe: the bind chain below
               sequences evaluation as rhs, then ptr, then deref, then idx. *)
            val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
            val struct_var = Isa_Free ("v__struct", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val v_var = Isa_Free ("v__rhs", isa_dummyT)
            val old_list = accessor_const $ struct_var
            val new_list = Isa_Const (\<^const_name>\<open>list_update\<close>,
                             isa_dummyT --> isa_dummyT --> isa_dummyT --> isa_dummyT)
                             $ old_list $ (C_Term_Build.mk_unat i_var) $ v_var
            val dummy_var = Isa_Free ("_uu__", isa_dummyT)
            val new_struct = updater_const $ (Term.lambda dummy_var new_list) $ struct_var
            val deref_expr =
              Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ ptr_var)
                $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                     $ deref_const)
            val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                               SOME (C_Ast_Utils.CPtr inner) => inner
                             | _ => unsupported "indexing non-array struct field")
            val rhs_term = mk_implicit_cast (rhs_term_raw, rhs_cty, field_cty)
            val write_term =
              C_Term_Build.mk_ptr_write
                (C_Term_Build.mk_literal ptr_var)
                (C_Term_Build.mk_literal new_struct)
            val write_term = mk_index_guard idx_p_cty i_var old_list write_term
            val assign_term =
              C_Term_Build.mk_bind rhs_term
                (Term.lambda v_var
                  (C_Term_Build.mk_bind ptr_expr
                    (Term.lambda ptr_var
                      (C_Term_Build.mk_bind deref_expr
                        (Term.lambda struct_var
                          (C_Term_Build.mk_bind idx_term
                            (Term.lambda i_var
                              (C_Term_Build.mk_sequence
                                write_term
                                (C_Term_Build.mk_literal v_var)))))))))
        in (assign_term, field_cty)
        end
    (* arr[idx] = rhs : array element write via focus *)
    | translate_expr tctx (CAssign0 (CAssignOp0, CIndex0 (arr_expr, idx_expr, _), rhs, _)) =
        let val (arr_term, arr_cty) = translate_expr tctx arr_expr
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val deref_const = resolve_dereference_const ctxt
            val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
            val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
            val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
            val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
            val elem_cty = (case arr_cty of
                              C_Ast_Utils.CPtr inner => inner
                            | _ => unsupported "indexing non-array expression")
            val elem_hol_ty =
              let val t = C_Ast_Utils.hol_type_of elem_cty
              in if t = isa_dummyT then isa_dummyT else t end
            val a_var = Isa_Free ("v__arr", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val v_var = Isa_Free ("v__rhs", elem_hol_ty)
            val deref_expr =
              Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ a_var)
                $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                     $ deref_const)
            val loc_var = Isa_Free ("v__loc", isa_dummyT)
            val arr_has_effect = C_Ast_Utils.expr_has_side_effect arr_expr
            val idx_has_effect = C_Ast_Utils.expr_has_side_effect idx_expr
            val rhs_has_effect = C_Ast_Utils.expr_has_side_effect rhs
            val arr_is_global_const =
              (case arr_expr of
                 CVar0 (ident, _) =>
                   (case C_Trans_Ctxt.lookup_global_const tctx (C_Ast_Utils.ident_name ident) of
                      SOME _ => true
                    | NONE => false)
               | _ => false)
            val unseq_lhs = arr_has_effect orelse idx_has_effect
            val unseq_lhs_rhs = unseq_lhs orelse rhs_has_effect
            val _ =
              if arr_is_global_const then
                unsupported "assignment to global constant array element"
              else if unseq_lhs_rhs andalso
                   (C_Ast_Utils.expr_has_unsequenced_ub_risk arr_expr idx_expr orelse
                    C_Ast_Utils.expr_has_unsequenced_ub_risk arr_expr rhs orelse
                    C_Ast_Utils.expr_has_unsequenced_ub_risk idx_expr rhs)
              then
                unsupported "potential unsequenced side-effect UB in indexed assignment"
              else ()
            val rhs_term = mk_implicit_cast (rhs_term_raw, rhs_cty, elem_cty)
            val loc_expr =
              if use_raw_pointer_indexing tctx arr_expr then
                mk_raw_ptr_loc_expr ctxt unseq_lhs arr_term idx_term_raw idx_cty elem_cty (is_nonnegative_int_const idx_expr)
              else
                let
                  val focused = C_Term_Build.mk_focus_nth (C_Term_Build.mk_unat i_var) a_var
                in
                  mk_pair_eval unseq_lhs arr_term idx_term a_var i_var
                    (let
                      val list_ty =
                        (case C_Ast_Utils.hol_type_of elem_cty of
                           t => if t = isa_dummyT then isa_dummyT else Isa_Type (\<^type_name>\<open>list\<close>, [t]))
                      val list_var = Isa_Free ("v__arr_vals", list_ty)
                    in C_Term_Build.mk_bind deref_expr
                         (Term.lambda list_var (mk_index_guard idx_p_cty i_var list_var (C_Term_Build.mk_literal focused))) end)
                end
            val write_fun =
              Term.lambda v_var (Term.lambda loc_var
                (C_Term_Build.mk_sequence
                  (C_Term_Build.mk_ptr_write
                    (C_Term_Build.mk_literal loc_var)
                    (C_Term_Build.mk_literal v_var))
                  (C_Term_Build.mk_literal v_var)))
            val assign_term =
              (if unseq_lhs_rhs
               then C_Term_Build.mk_bind2_unseq write_fun rhs_term loc_expr
               else C_Term_Build.mk_bind2 write_fun rhs_term loc_expr)
        in (assign_term, elem_cty)
        end
    (* arr[idx] op= rhs : compound array element write *)
    | translate_expr tctx (CAssign0 (asgn_op, CIndex0 (arr_expr, idx_expr, _), rhs, _)) =
        (case compound_assign_to_binop asgn_op of
           SOME binop =>
             let val (arr_term, arr_cty) = translate_expr tctx arr_expr
                 val ctxt = C_Trans_Ctxt.get_ctxt tctx
                 val deref_const = resolve_dereference_const ctxt
                 val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
                 val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
                 val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
                 val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
                 val a_var = Isa_Free ("v__arr", isa_dummyT)
                 val i_var = Isa_Free ("v__idx", isa_dummyT)
                 val loc_var = Isa_Free ("v__loc", isa_dummyT)
                 val list_var = Isa_Free ("v__arr_vals", isa_dummyT)
                 val deref_expr =
                   Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ a_var)
                     $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                          $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                          $ deref_const)
                 val old_var = Isa_Free ("v__old", isa_dummyT)
                 val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
                 val new_var = Isa_Free ("v__new", isa_dummyT)
                 val arr_has_effect = C_Ast_Utils.expr_has_side_effect arr_expr
                 val idx_has_effect = C_Ast_Utils.expr_has_side_effect idx_expr
                 val rhs_has_effect = C_Ast_Utils.expr_has_side_effect rhs
                 val arr_is_global_const =
                   (case arr_expr of
                      CVar0 (ident, _) =>
                        (case C_Trans_Ctxt.lookup_global_const tctx (C_Ast_Utils.ident_name ident) of
                           SOME _ => true
                         | NONE => false)
                    | _ => false)
                 val unseq_lhs = arr_has_effect orelse idx_has_effect
                 val unseq_lhs_rhs = unseq_lhs orelse rhs_has_effect
                 val _ =
                   if arr_is_global_const then
                     unsupported "compound assignment to global constant array element"
                   else if unseq_lhs_rhs andalso
                        (C_Ast_Utils.expr_has_unsequenced_ub_risk arr_expr idx_expr orelse
                         C_Ast_Utils.expr_has_unsequenced_ub_risk arr_expr rhs orelse
                         C_Ast_Utils.expr_has_unsequenced_ub_risk idx_expr rhs)
                   then
                     unsupported "potential unsequenced side-effect UB in indexed compound assignment"
                   else ()
                 val focused = C_Term_Build.mk_focus_nth
                                 (C_Term_Build.mk_unat i_var) a_var
                 val elem_cty = (case arr_cty of
                                   C_Ast_Utils.CPtr inner => inner
                                 | _ => unsupported "indexing non-array expression")
                 val op_cty = compound_op_cty elem_cty rhs_cty binop
                 val loc_expr =
                   if use_raw_pointer_indexing tctx arr_expr then
                     mk_raw_ptr_loc_expr ctxt unseq_lhs arr_term idx_term_raw idx_cty elem_cty (is_nonnegative_int_const idx_expr)
                   else
                     mk_pair_eval unseq_lhs arr_term idx_term a_var i_var
                       (let
                         val list_ty =
                           (case C_Ast_Utils.hol_type_of elem_cty of
                              t => if t = isa_dummyT then isa_dummyT else Isa_Type (\<^type_name>\<open>list\<close>, [t]))
                         val list_var = Isa_Free ("v__arr_vals", list_ty)
                       in C_Term_Build.mk_bind deref_expr
                            (Term.lambda list_var (mk_index_guard idx_p_cty i_var list_var (C_Term_Build.mk_literal focused))) end)
             in case translate_binop op_cty binop of
                  Monadic f =>
                    let
                      val combine_rhs_loc =
                        if unseq_lhs_rhs then C_Term_Build.mk_bind2_unseq else C_Term_Build.mk_bind2
                      val assign_fun =
                        Term.lambda rhs_var (Term.lambda loc_var
                          (C_Term_Build.mk_bind
                            (C_Term_Build.mk_deref (C_Term_Build.mk_literal loc_var))
                            (Term.lambda old_var
                              (let
                                 val (_, old_prom, rhs_prom) =
                                   prepare_compound_operands
                                     elem_cty
                                     (C_Term_Build.mk_literal rhs_var)
                                     rhs_cty
                                     binop
                                     (C_Term_Build.mk_literal old_var)
                               in
                                 C_Term_Build.mk_bind
                                   (C_Term_Build.mk_bind2 f old_prom rhs_prom)
                                   (Term.lambda new_var
                                     (let
                                        val new_assigned =
                                          mk_implicit_cast
                                            (C_Term_Build.mk_literal new_var, op_cty, elem_cty)
                                      in
                                        C_Term_Build.mk_sequence
                                          (C_Term_Build.mk_ptr_write
                                            (C_Term_Build.mk_literal loc_var)
                                            new_assigned)
                                          new_assigned
                                      end))
                               end))))
                      val assign_term = combine_rhs_loc assign_fun rhs_term_raw loc_expr
                    in
                      (assign_term, elem_cty)
                    end
             end
         | NONE => unsupported "unsupported compound operator on array element")
    | translate_expr tctx (CAssign0 (CAssignOp0, CVar0 (ident, _), rhs, _)) =
        let val name = C_Ast_Utils.ident_name ident
            val (rhs', rhs_cty) = translate_expr tctx rhs
            val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Local, var, cty) =>
               let val rhs_cast = mk_implicit_cast (rhs', rhs_cty, cty)
               in (C_Term_Build.mk_bind rhs_cast (Term.lambda rhs_var
                     (C_Term_Build.mk_sequence
                       (C_Term_Build.mk_var_write var (C_Term_Build.mk_literal rhs_var))
                       (C_Term_Build.mk_literal rhs_var))),
                   cty)
               end
           | SOME (C_Trans_Ctxt.LocalPtr, var, cty) =>
               let val rhs_cast = mk_implicit_cast (rhs', rhs_cty, cty)
                   val rhs_raw = mk_implicit_cast (rhs_cast, cty, C_Ast_Utils.CPtr C_Ast_Utils.CVoid)
               in (C_Term_Build.mk_bind rhs_raw (Term.lambda rhs_var
                     (C_Term_Build.mk_sequence
                       (C_Term_Build.mk_var_write var (C_Term_Build.mk_literal rhs_var))
                       rhs_cast)),
                   cty)
               end
           | SOME (C_Trans_Ctxt.Param, _, _) =>
               error ("micro_c_translate: assignment to parameter: " ^ name)
           | NONE =>
               (case C_Trans_Ctxt.lookup_global_const tctx name of
                  SOME _ =>
                    error ("micro_c_translate: assignment to global constant: " ^ name)
                | NONE =>
                    error ("micro_c_translate: undefined variable: " ^ name))
        end
    | translate_expr tctx (CAssign0 (CAssignOp0, CUnary0 (CIndOp0, lhs, _), rhs, _)) =
        (* *p = v : write through pointer *)
        let val (lhs', lhs_cty) = translate_expr tctx lhs
            val pointee_cty = (case lhs_cty of
                                 C_Ast_Utils.CPtr inner => inner
                               | _ => unsupported "dereference assignment on non-pointer expression")
            val (rhs', rhs_cty) = translate_expr tctx rhs
            val rhs_cast = mk_implicit_cast (rhs', rhs_cty, pointee_cty)
            val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
            val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
            val unseq_lhs_rhs =
              C_Ast_Utils.expr_has_side_effect lhs orelse C_Ast_Utils.expr_has_side_effect rhs
            val _ =
              if unseq_lhs_rhs andalso C_Ast_Utils.expr_has_unsequenced_ub_risk lhs rhs then
                unsupported "potential unsequenced side-effect UB in dereference assignment"
              else ()
            val write_fun =
              Term.lambda rhs_var (Term.lambda ptr_var
                (C_Term_Build.mk_sequence
                  (C_Term_Build.mk_ptr_write
                    (C_Term_Build.mk_literal ptr_var)
                    (C_Term_Build.mk_literal rhs_var))
                  (C_Term_Build.mk_literal rhs_var)))
            val assign_term =
              (if unseq_lhs_rhs
               then C_Term_Build.mk_bind2_unseq write_fun rhs_cast lhs'
               else C_Term_Build.mk_bind2 write_fun rhs_cast lhs')
        in (assign_term,
            pointee_cty)
        end
    (* *p op= rhs : compound assignment through pointer dereference *)
    | translate_expr tctx (CAssign0 (asgn_op, CUnary0 (CIndOp0, ptr_expr, _), rhs, _)) =
        (case compound_assign_to_binop asgn_op of
           SOME binop =>
             let val (ptr_term, cty) = translate_expr tctx ptr_expr
                 val pointee_cty = (case cty of
                                      C_Ast_Utils.CPtr inner => inner
                                    | _ => unsupported "compound dereference assignment on non-pointer expression")
                 val (rhs_term_raw, rhs_cty) = translate_expr tctx rhs
                 val op_cty = compound_op_cty pointee_cty rhs_cty binop
                 val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
                 val old_var = Isa_Free ("v__old", isa_dummyT)
                 val rhs_var = Isa_Free ("v__rhs", isa_dummyT)
                 val new_var = Isa_Free ("v__new", isa_dummyT)
                 val unseq_lhs_rhs =
                   C_Ast_Utils.expr_has_side_effect ptr_expr orelse C_Ast_Utils.expr_has_side_effect rhs
                 val _ =
                   if unseq_lhs_rhs andalso C_Ast_Utils.expr_has_unsequenced_ub_risk ptr_expr rhs then
                     unsupported "potential unsequenced side-effect UB in dereference compound assignment"
                   else ()
             in case translate_binop op_cty binop of
                  Monadic f =>
                    let
                      val combine_rhs_ptr =
                        if unseq_lhs_rhs then C_Term_Build.mk_bind2_unseq else C_Term_Build.mk_bind2
                      val assign_fun =
                        Term.lambda rhs_var (Term.lambda ptr_var
                          (C_Term_Build.mk_bind
                            (C_Term_Build.mk_deref (C_Term_Build.mk_literal ptr_var))
                            (Term.lambda old_var
                              (let
                                 val (_, old_prom, rhs_prom) =
                                   prepare_compound_operands
                                     pointee_cty
                                     (C_Term_Build.mk_literal rhs_var)
                                     rhs_cty
                                     binop
                                     (C_Term_Build.mk_literal old_var)
                               in
                                 C_Term_Build.mk_bind
                                   (C_Term_Build.mk_bind2 f old_prom rhs_prom)
                                   (Term.lambda new_var
                                     (let
                                        val new_assigned =
                                          mk_implicit_cast
                                            (C_Term_Build.mk_literal new_var, op_cty, pointee_cty)
                                      in
                                        C_Term_Build.mk_sequence
                                          (C_Term_Build.mk_ptr_write
                                            (C_Term_Build.mk_literal ptr_var)
                                            new_assigned)
                                          new_assigned
                                      end))
                               end))))
                      val assign_term = combine_rhs_ptr assign_fun rhs_term_raw ptr_term
                    in
                      (assign_term, pointee_cty)
                    end
             end
         | NONE => unsupported "unsupported operator on dereferenced pointer")
    | translate_expr tctx (CAssign0 (asgn_op, CVar0 (ident, _), rhs, _)) =
        (* Compound assignment: x op= rhs -> read x, compute (x op rhs), write x, return new *)
        (case compound_assign_to_binop asgn_op of
             SOME binop =>
               let val name = C_Ast_Utils.ident_name ident
                   val (rhs_raw, rhs_cty) = translate_expr tctx rhs
               in case C_Trans_Ctxt.lookup_var tctx name of
                    SOME (C_Trans_Ctxt.Local, var, cty) =>
                      let val old_var = Isa_Free ("v__old", isa_dummyT)
                          val new_var = Isa_Free ("v__new", isa_dummyT)
                          val op_cty = compound_op_cty cty rhs_cty binop
                      in case translate_binop op_cty binop of
                           Monadic f =>
                             (C_Term_Build.mk_bind (C_Term_Build.mk_var_read var)
                               (Term.lambda old_var
                                 (C_Term_Build.mk_bind
                                   (let
                                      val (_, old_prom, rhs_prom) =
                                        prepare_compound_operands
                                          cty rhs_raw rhs_cty binop
                                          (C_Term_Build.mk_literal old_var)
                                    in
                                      C_Term_Build.mk_bind2 f old_prom rhs_prom
                                    end)
                                   (Term.lambda new_var
                                     (let
                                        val new_assigned =
                                          mk_implicit_cast
                                            (C_Term_Build.mk_literal new_var, op_cty, cty)
                                      in
                                     (C_Term_Build.mk_sequence
                                       (C_Term_Build.mk_var_write var
                                         new_assigned)
                                       new_assigned)
                                      end)))), cty)
                      end
                  | _ =>
                      (case C_Trans_Ctxt.lookup_global_const tctx name of
                         SOME _ => unsupported ("compound assignment to global constant: " ^ name)
                       | NONE => unsupported "compound assignment to non-local variable")
               end
           | NONE => unsupported "compound assignment or non-variable lhs")
    | translate_expr _ (CAssign0 _) =
        unsupported "non-variable lhs in assignment"
    | translate_expr tctx (CCall0 (CVar0 (ident, _), args, _)) =
        let val fname = C_Ast_Utils.ident_name ident
            val arg_terms_typed = List.map (translate_expr tctx) args
            val arg_has_effects = List.map C_Ast_Utils.expr_has_side_effect args
            val any_arg_effect = List.exists I arg_has_effects
            val param_ctys = C_Trans_Ctxt.lookup_func_param_types tctx fname
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val func_ref =
              (case resolve_visible_const_term ctxt (!current_decl_prefix ^ fname) of
                 SOME fterm => SOME fterm
               | NONE =>
                   (case resolve_visible_const_term ctxt fname of
                      SOME fterm => SOME fterm
                    | NONE =>
                        (* In locale targets, freshly declared functions may not yet
                           resolve as constants. If the C signature table knows this
                           function, synthesize a reference term and let typing/casts
                           constrain it. *)
                        (case param_ctys of
                           SOME _ => SOME (Isa_Free (!current_decl_prefix ^ fname, isa_dummyT))
                         | NONE => NONE)))
            val _ =
              (case param_ctys of
                 SOME tys =>
                   if List.length arg_terms_typed = List.length tys then ()
                   else unsupported
                     ("function call arity mismatch for " ^ fname ^ ": expected " ^
                      Int.toString (List.length tys) ^ ", got " ^ Int.toString (List.length arg_terms_typed))
               | NONE =>
                   (case func_ref of
                      SOME _ => ()
                    | NONE =>
                        unsupported ("call to undeclared function: " ^ fname ^
                          " (tried symbols: " ^ !current_decl_prefix ^ fname ^ ", " ^ fname ^ ")")))
            fun cast_args [] _ = []
              | cast_args ((arg_tm, _) :: rest) [] = arg_tm :: cast_args rest []
              | cast_args ((arg_tm, arg_cty) :: rest) (p_cty :: p_rest) =
                  mk_implicit_cast (arg_tm, arg_cty, p_cty) :: cast_args rest p_rest
            val arg_terms =
              (case param_ctys of
                 SOME tys => cast_args arg_terms_typed tys
               | NONE => List.map #1 arg_terms_typed)
              |> List.map constrain_expr_side_types
            val argc = List.length arg_terms
            (* For arity > 2 with side-effecting arguments: funcallN sequences
               evaluation left-to-right via bindN, which is a valid ordering for
               C's unspecified argument evaluation order.  We warn if multiple
               arguments have side effects (potential for unsequenced UB), but
               allow it when at most one argument is side-effecting. *)
            val effect_count = List.length (List.filter I arg_has_effects)
            val _ =
              if argc > 2 andalso effect_count > 1 then
                unsupported ("call to " ^ fname ^
                  " has multiple side-effecting arguments with unspecified C evaluation order (arity > 2)")
              else ()
            val _ =
              if argc = 2 andalso any_arg_effect andalso
                 C_Ast_Utils.expr_has_unsequenced_ub_risk (List.nth (args, 0)) (List.nth (args, 1))
              then
                unsupported ("call to " ^ fname ^
                  " has potential unsequenced side-effect UB across arguments")
              else ()
        in
          (case func_ref of
             SOME fref =>
               let
                 (* Look up callee's fuel parameter count and generate fresh
                    while_fuel free variables to pass as leading arguments.
                    These will be picked up by the caller's fuel abstraction
                    (String.isPrefix "while_fuel" in translate_fundef). *)
                 val callee_full = !current_decl_prefix ^ fname
                 val fuel_count =
                   (case Symtab.lookup (!defined_func_fuels) callee_full of
                      SOME n => n | NONE => 0)
                 val fuel_args = List.tabulate (fuel_count, fn i =>
                   Isa_Free ("while_fuel_" ^ fname ^
                     (if fuel_count = 1 then "" else "_" ^ Int.toString i),
                     @{typ nat}))
                 (* Partial-apply fuel args to fref: fuel params are pure nat
                    values, not monadic expressions, so they must be applied
                    directly rather than passed through funcallN. *)
                 val fref_fueled = List.foldl (fn (a, f) => f $ a) fref fuel_args
                 val ret_value_ty =
                   (case C_Trans_Ctxt.lookup_func_return_type tctx fname of
                      SOME C_Ast_Utils.CVoid => @{typ unit}
                    | SOME rcty =>
                        (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) rcty of
                           SOME ty => ty
                         | NONE => isa_dummyT)
                    | NONE => isa_dummyT)
                 val fref_called =
                   if argc = 0 then fref_fueled
                   else
                     let
                       val arg_tys = List.map expr_value_type arg_terms
                       val fn_ty = Library.foldr (fn (a_ty, acc_ty) => a_ty --> acc_ty)
                         (arg_tys, isa_dummyT)
                     in
                       Type.constraint fn_ty fref_fueled
                     end
                 val call_term =
                   if argc = 2 andalso any_arg_effect then
                     let val call2 =
                           Isa_Const (\<^const_name>\<open>deep_compose2\<close>, dummyT --> dummyT --> dummyT)
                             $ Isa_Const (\<^const_name>\<open>call\<close>, dummyT --> dummyT)
                             $ fref_called
                     in C_Term_Build.mk_bind2_unseq call2 (List.nth (arg_terms, 0)) (List.nth (arg_terms, 1)) end
                   else
                     C_Term_Build.mk_funcall fref_called arg_terms
                 val call_term =
                   if ret_value_ty = isa_dummyT then call_term
                   else constrain_known_expr_value_type ret_value_ty call_term
                 val call_term = constrain_expr_side_types call_term
                 val ret_cty =
                   (case C_Trans_Ctxt.lookup_func_return_type tctx fname of
                      SOME cty => cty
                    | NONE =>
                        (case cty_of_hol_type (expr_value_type call_term) of
                           SOME cty => cty
                         | NONE => C_Ast_Utils.CInt))
               in (call_term, ret_cty) end
           | NONE =>
               unsupported ("call to undeclared function: " ^ fname ^
                 " (tried symbols: " ^ !current_decl_prefix ^ fname ^ ", " ^ fname ^ ")"))
        end
    | translate_expr _ (CCall0 _) =
        unsupported "indirect function call (function pointers)"
    | translate_expr tctx (CUnary0 (CAdrOp0, expr, _)) =
        translate_lvalue_location tctx expr
    | translate_expr tctx (CUnary0 (CIndOp0, expr, _)) =
        (* *p : dereference pointer. Resolve dereference_fun from locale context
           to avoid adhoc overloading ambiguity (same as CIndex0 reads).
           If the inner expression has CPtr ty, unwrap to ty. *)
        let val (expr', cty) = translate_expr tctx expr
            val result_cty = (case cty of
                                C_Ast_Utils.CPtr C_Ast_Utils.CVoid =>
                                  unsupported "dereference of void pointer (cast first)"
                              | C_Ast_Utils.CPtr inner => inner
                              | _ => unsupported "dereference on non-pointer expression")
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
        in (mk_resolved_deref_expr ctxt result_cty expr', result_cty) end
    | translate_expr tctx (CUnary0 (CCompOp0, expr, _)) =
        (* ~x : bitwise complement — C11: operand undergoes integer promotion *)
        let val (expr', cty) = translate_expr tctx expr
            val pcty = C_Ast_Utils.integer_promote cty
            val promoted = mk_implicit_cast (expr', cty, pcty)
            val not_const =
              if C_Ast_Utils.is_signed pcty
              then Isa_Const (\<^const_name>\<open>c_signed_not\<close>, isa_dummyT)
              else Isa_Const (\<^const_name>\<open>c_unsigned_not\<close>, isa_dummyT)
            val v = Isa_Free ("v__comp", isa_dummyT)
        in (C_Term_Build.mk_bind promoted (Term.lambda v (not_const $ v)), pcty) end
    | translate_expr tctx (CUnary0 (CMinOp0, expr, _)) =
        (* -x : unary minus, translate as 0 - x — C11: operand undergoes integer promotion *)
        let val (expr', cty) = translate_expr tctx expr
            val pcty = C_Ast_Utils.integer_promote cty
            val promoted = mk_implicit_cast (expr', cty, pcty)
            val zero = C_Term_Build.mk_literal_num pcty 0
            val sub_const =
              if C_Ast_Utils.is_signed pcty
              then Isa_Const (\<^const_name>\<open>c_signed_sub\<close>, isa_dummyT)
              else Isa_Const (\<^const_name>\<open>c_unsigned_sub\<close>, isa_dummyT)
        in (C_Term_Build.mk_bind2 sub_const zero promoted, pcty) end
    | translate_expr tctx (CUnary0 (CPreIncOp0, expr, _)) =
        translate_inc_dec translate_expr translate_lvalue_location tctx true true expr
    | translate_expr tctx (CUnary0 (CPostIncOp0, expr, _)) =
        translate_inc_dec translate_expr translate_lvalue_location tctx true false expr
    | translate_expr tctx (CUnary0 (CPreDecOp0, expr, _)) =
        translate_inc_dec translate_expr translate_lvalue_location tctx false true expr
    | translate_expr tctx (CUnary0 (CPostDecOp0, expr, _)) =
        translate_inc_dec translate_expr translate_lvalue_location tctx false false expr
    | translate_expr tctx (CUnary0 (CPlusOp0, expr, _)) =
        (* +x : unary plus — C11: operand undergoes integer promotion *)
        let val (expr', cty) = translate_expr tctx expr
            val pcty = C_Ast_Utils.integer_promote cty
        in (mk_implicit_cast (expr', cty, pcty), pcty) end
    | translate_expr tctx (CUnary0 (CNegOp0, expr, _)) =
        (* !x : logical NOT *)
        let val (expr', cty) = translate_expr tctx expr
            val b = mk_implicit_cast (expr', cty, C_Ast_Utils.CBool)
            val v = Isa_Free ("v__neg", @{typ bool})
        in (C_Term_Build.mk_bind b
              (Term.lambda v
                (C_Term_Build.mk_literal
                  (Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool}) $ v))),
            C_Ast_Utils.CBool)
        end
    (* p->field[idx]  /  s.field[idx] : struct field (list) read, then index with nth.
       Uses resolved dereference_fun to avoid store_dereference_const adhoc overloading. *)
    | translate_expr tctx (CIndex0 (CMember0 (expr, field_ident, is_ptr, _), idx_expr, _)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val accessor_const = resolve_struct_accessor_const ctxt struct_name field_name
            val deref_const = resolve_dereference_const ctxt
            val ptr_expr = if is_ptr then #1 (translate_expr tctx expr)
                           else #1 (translate_lvalue_location tctx expr)
            val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
            val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
            val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
            val unseq_index =
              C_Ast_Utils.expr_has_side_effect expr orelse C_Ast_Utils.expr_has_side_effect idx_expr
            val _ =
              if unseq_index andalso C_Ast_Utils.expr_has_unsequenced_ub_risk expr idx_expr then
                unsupported "potential unsequenced side-effect UB in indexed access"
              else ()
            val ptr_var = Isa_Free ("v__ptr", isa_dummyT)
            val struct_var = Isa_Free ("v__struct", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val list_val = accessor_const $ struct_var
            val nth_term = Isa_Const (\<^const_name>\<open>nth\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                             $ list_val $ (C_Term_Build.mk_unat i_var)
            val deref_expr =
              Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ ptr_var)
                $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                     $ deref_const)
            val elem_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                              SOME (C_Ast_Utils.CPtr inner) => inner
                            | SOME inner =>
                                if struct_field_is_array_backed struct_name field_name then inner
                                else unsupported "indexing non-array struct field"
                            | NONE => unsupported "indexing unknown struct field")
            val value_term = C_Term_Build.mk_literal nth_term
            val value_term = mk_index_guard idx_p_cty i_var list_val value_term
        in (mk_pair_eval unseq_index ptr_expr idx_term ptr_var i_var
              (C_Term_Build.mk_bind deref_expr (Term.lambda struct_var value_term)),
            elem_cty)
        end
    (* arr[idx] : deref whole list, then index with nth.
       We resolve dereference_fun from the locale context instead of using
       store_dereference_const, which has ambiguous adhoc overloading
       (dereference_fun vs ro_dereference_fun) for read-only references. *)
    | translate_expr tctx (CIndex0 (arr_expr, idx_expr, _)) =
        let val (arr_term, arr_cty) = translate_expr tctx arr_expr
            val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
            val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
            val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
            val unseq_index =
              C_Ast_Utils.expr_has_side_effect arr_expr orelse C_Ast_Utils.expr_has_side_effect idx_expr
            val _ =
              if unseq_index andalso C_Ast_Utils.expr_has_unsequenced_ub_risk arr_expr idx_expr then
                unsupported "potential unsequenced side-effect UB in indexed access"
              else ()
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val deref_const = resolve_dereference_const ctxt
            val elem_cty =
              (case arr_cty of
                 C_Ast_Utils.CPtr inner => inner
               | _ => unsupported "indexing non-array expression")
            val a_var = Isa_Free ("v__arr", isa_dummyT)
            val i_var = Isa_Free ("v__idx", isa_dummyT)
            val list_elem_ty =
              (case arr_cty of
                 C_Ast_Utils.CPtr inner =>
                   (case C_Ast_Utils.hol_type_of inner of
                      t => if t = isa_dummyT then isa_dummyT
                           else Isa_Type (\<^type_name>\<open>list\<close>, [t]))
               | _ => isa_dummyT)
            val list_var = Isa_Free ("v__list", list_elem_ty)
            val nth_term = Isa_Const (\<^const_name>\<open>nth\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                             $ list_var $ (C_Term_Build.mk_unat i_var)
            val deref_expr =
              Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ a_var)
                $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                     $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                     $ deref_const)
            val arr_is_global_const =
              (case arr_expr of
                 CVar0 (ident, _) =>
                   (case C_Trans_Ctxt.lookup_global_const tctx (C_Ast_Utils.ident_name ident) of
                      SOME _ => true
                    | NONE => false)
               | _ => false)
            val value_term = C_Term_Build.mk_literal nth_term
            val value_term = mk_index_guard idx_p_cty i_var list_var value_term
        in
          if use_raw_pointer_indexing tctx arr_expr then
            let
              val loc_expr = mk_raw_ptr_loc_expr ctxt unseq_index arr_term idx_term_raw idx_cty elem_cty (is_nonnegative_int_const idx_expr)
              val deref_loc =
                Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                  $ loc_expr
                  $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                       $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                       $ deref_const)
            in
              (deref_loc, elem_cty)
            end
          else
            (mk_pair_eval unseq_index arr_term idx_term a_var i_var
               (if arr_is_global_const then
                  let
                    val direct_nth =
                      Isa_Const (\<^const_name>\<open>nth\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                        $ a_var $ (C_Term_Build.mk_unat i_var)
                    val direct_term = C_Term_Build.mk_literal direct_nth
                    val direct_term = mk_index_guard idx_p_cty i_var a_var direct_term
                  in direct_term end
                else
                  C_Term_Build.mk_bind deref_expr (Term.lambda list_var value_term)),
             elem_cty)
        end
    (* p->field : struct/union field access through pointer.
       For unions: cast to typed ref, then dereference.
       For array fields (CPtr inner): array-to-pointer decay — create a focused
       reference to the field rather than reading the value.
       For scalar fields: dereference and read the value. *)
    | translate_expr tctx (CMember0 (expr, field_ident, true, ni)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val ctxt = C_Trans_Ctxt.get_ctxt tctx
            val (ptr_expr, ptr_cty, ptr_is_raw) =
              (case expr of
                 CCast0 (_, inner_expr, _) =>
                   let val (inner_ptr, inner_cty) = translate_expr tctx inner_expr
                   in case inner_cty of
                        C_Ast_Utils.CPtr C_Ast_Utils.CVoid => (inner_ptr, inner_cty, true)
                      | C_Ast_Utils.CPtr (C_Ast_Utils.CUnion _) => (inner_ptr, inner_cty, true)
                      | _ => let val (ptr_expr, ptr_cty) = translate_expr tctx expr
                             in (ptr_expr, ptr_cty, false) end
                   end
               | _ => let val (ptr_expr, ptr_cty) = translate_expr tctx expr
                      in (ptr_expr, ptr_cty, false) end)
            val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                               SOME cty => cty
                             | NONE => unsupported ("unknown struct field type: " ^ struct_name ^ "." ^ field_name))
            val array_backed_field = struct_field_is_array_backed struct_name field_name
        in if array_backed_field andalso not (is_union_aggregate struct_name) then
          let val (loc_expr, _) = translate_lvalue_location tctx (CMember0 (expr, field_ident, true, ni))
          in (constrain_expr_side_types loc_expr, C_Ast_Utils.CPtr field_cty) end
        else if is_union_aggregate struct_name then
          (* Union field read: cast to typed ref, then dereference *)
          let val cast_expr = mk_cast_from_void_in ctxt field_cty ptr_expr
              val v = Isa_Free ("v__uref", typed_ref_ty_of_cty field_cty)
          in (C_Term_Build.mk_bind cast_expr
                (Term.lambda v (mk_resolved_deref_expr ctxt field_cty (C_Term_Build.mk_literal v))),
              field_cty) end
        else if ptr_is_raw then
          let
            val loc_expr = mk_raw_struct_field_loc_expr tctx struct_name field_name field_cty ptr_expr
            val loc_ty = expr_value_type loc_expr
            val loc_var = Isa_Free ("v__field_loc", if loc_ty = isa_dummyT then isa_dummyT else loc_ty)
          in case field_cty of
               C_Ast_Utils.CPtr _ => (constrain_expr_side_types loc_expr, field_cty)
             | _ => (C_Term_Build.mk_bind loc_expr
                      (Term.lambda loc_var (mk_resolved_deref_expr ctxt field_cty (C_Term_Build.mk_literal loc_var))),
                     field_cty)
          end
        else
          let
            val _ = (case ptr_cty of
                       C_Ast_Utils.CPtr _ => ()
                     | _ => unsupported "member access through non-pointer expression")
            val focus_const = resolve_struct_focus_const ctxt struct_name field_name
            val base_ty = expr_value_type ptr_expr
            val base_var = Isa_Free ("v__base_loc", if base_ty = isa_dummyT then isa_dummyT else base_ty)
            val focused = C_Term_Build.mk_focus_field focus_const base_var
            val loc_expr =
              C_Term_Build.mk_bind ptr_expr (Term.lambda base_var (C_Term_Build.mk_literal focused))
            val loc_ty = expr_value_type loc_expr
            val loc_var = Isa_Free ("v__field_loc", if loc_ty = isa_dummyT then isa_dummyT else loc_ty)
          in case field_cty of
               C_Ast_Utils.CPtr _ => (constrain_expr_side_types loc_expr, field_cty)
             | _ => (C_Term_Build.mk_bind loc_expr
                      (Term.lambda loc_var (mk_resolved_deref_expr ctxt field_cty (C_Term_Build.mk_literal loc_var))),
                     field_cty)
          end
        end
    (* s.field : direct struct/union member access via value *)
    | translate_expr tctx (CMember0 (expr, field_ident, false, ni)) =
        let val field_name = C_Ast_Utils.ident_name field_ident
            val struct_name = determine_struct_type tctx expr
            val field_cty = (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
                               SOME cty => cty
                             | NONE => unsupported ("unknown field type: " ^ struct_name ^ "." ^ field_name))
            val array_backed_field = struct_field_is_array_backed struct_name field_name
        in if array_backed_field andalso not (is_union_aggregate struct_name) then
          let val (loc_expr, _) = translate_lvalue_location tctx (CMember0 (expr, field_ident, false, ni))
          in (constrain_expr_side_types loc_expr, C_Ast_Utils.CPtr field_cty) end
        else if is_union_aggregate struct_name then
          (* Union: get lvalue location of s, cast void ref to typed ref, deref *)
          let val (loc_expr, _) = translate_lvalue_location tctx expr
              val cast_expr = mk_cast_from_void_in (C_Trans_Ctxt.get_ctxt tctx) field_cty loc_expr
              val v = Isa_Free ("v__uref", typed_ref_ty_of_cty field_cty)
          in (C_Term_Build.mk_bind cast_expr
                (Term.lambda v (mk_resolved_deref_expr (C_Trans_Ctxt.get_ctxt tctx) field_cty
                                  (C_Term_Build.mk_literal v))),
              field_cty) end
        else
          let val ctxt = C_Trans_Ctxt.get_ctxt tctx
              val accessor_const = resolve_struct_accessor_const ctxt struct_name field_name
              val (struct_expr, _) = translate_expr tctx expr
              val v = Isa_Free ("v__struct", isa_dummyT)
          in (constrain_expr_cty field_cty
                (C_Term_Build.mk_bind struct_expr
                  (Term.lambda v (C_Term_Build.mk_literal (accessor_const $ v)))),
              field_cty) end
        end
    | translate_expr tctx (CCond0 (cond, Some then_expr, else_expr, _)) =
        (* x ? y : z — ternary conditional *)
        let val (then', then_cty) = translate_expr tctx then_expr
            val (else', else_cty) = translate_expr tctx else_expr
            val result_cty =
              if then_cty = else_cty then then_cty
              else if C_Ast_Utils.is_ptr then_cty andalso C_Ast_Utils.is_ptr else_cty
              then (* Both pointer types: allow void* \<leftrightarrow> T* coercion *)
                (case (then_cty, else_cty) of
                   (_, C_Ast_Utils.CPtr C_Ast_Utils.CVoid) => then_cty
                 | (C_Ast_Utils.CPtr C_Ast_Utils.CVoid, _) => else_cty
                 | _ => unsupported "ternary with incompatible pointer types")
              else if C_Ast_Utils.is_ptr then_cty orelse C_Ast_Utils.is_ptr else_cty
              then (* One pointer, one integer — use the pointer type *)
                if C_Ast_Utils.is_ptr then_cty then then_cty else else_cty
              else C_Ast_Utils.usual_arith_conv (then_cty, else_cty)
            val then_cast = mk_implicit_cast (then', then_cty, result_cty)
            val else_cast = mk_implicit_cast (else', else_cty, result_cty)
        in (C_Term_Build.mk_two_armed_cond (ensure_bool_cond tctx cond) then_cast else_cast, result_cty) end
    | translate_expr tctx (CCond0 (cond, None, else_expr, _)) =
        (* GNU extension: x ?: y means x ? x : y *)
        let val (cond_term, cond_cty) = translate_expr tctx cond
            val (else', else_cty) = translate_expr tctx else_expr
            val result_cty =
              if cond_cty = else_cty then cond_cty
              else if C_Ast_Utils.is_ptr cond_cty andalso C_Ast_Utils.is_ptr else_cty
              then (case (cond_cty, else_cty) of
                   (_, C_Ast_Utils.CPtr C_Ast_Utils.CVoid) => cond_cty
                 | (C_Ast_Utils.CPtr C_Ast_Utils.CVoid, _) => else_cty
                 | _ => unsupported "GNU ?: with incompatible pointer types")
              else if C_Ast_Utils.is_ptr cond_cty orelse C_Ast_Utils.is_ptr else_cty
              then if C_Ast_Utils.is_ptr cond_cty then cond_cty else else_cty
              else C_Ast_Utils.usual_arith_conv (cond_cty, else_cty)
            val cond_v = Isa_Free ("v__condv", isa_dummyT)
            val cond_bool = mk_implicit_cast (C_Term_Build.mk_literal cond_v, cond_cty, C_Ast_Utils.CBool)
            val then_cast = mk_implicit_cast (C_Term_Build.mk_literal cond_v, cond_cty, result_cty)
            val else_cast = mk_implicit_cast (else', else_cty, result_cty)
        in (C_Term_Build.mk_bind cond_term
              (Term.lambda cond_v
                (C_Term_Build.mk_two_armed_cond cond_bool then_cast else_cast)),
            result_cty)
        end
    | translate_expr _ (CConst0 (CCharConst0 (CChar0 (c, _), _))) =
        (* C character constants have type int. *)
        (C_Term_Build.mk_literal_num C_Ast_Utils.CInt
           (intinf_to_int_checked "character literal" (integer_of_char c)),
         C_Ast_Utils.CInt)
    | translate_expr _ (CConst0 (CStrConst0 (CString0 (abr_str, _), _))) =
        (* String literal: produce a c_char list with null terminator *)
        let val s = C_Ast_Utils.abr_string_to_string abr_str
            val char_ty = C_Ast_Utils.hol_type_of C_Ast_Utils.CChar
            val bytes = List.map (fn c => HOLogic.mk_number char_ty (Char.ord c))
                          (String.explode s)
            val with_null = bytes @ [HOLogic.mk_number char_ty 0]
            val list_term = HOLogic.mk_list char_ty with_null
        in (C_Term_Build.mk_literal list_term, C_Ast_Utils.CPtr C_Ast_Utils.CChar)
        end
    | translate_expr _ (CComma0 ([], _)) =
        (C_Term_Build.mk_literal_unit, C_Ast_Utils.CInt)
    | translate_expr tctx (CComma0 (exprs, _)) =
        let val translated = List.map (translate_expr tctx) exprs
            fun fold_comma [] = error "micro_c_translate: empty comma expression"
              | fold_comma [(e, ty)] = (e, ty)
              | fold_comma ((e, _) :: rest) =
                  let val (rest_e, rest_ty) = fold_comma rest
                  in (C_Term_Build.mk_sequence e rest_e, rest_ty) end
        in fold_comma translated end
    (* (target_type)expr : type cast *)
    | translate_expr tctx (CCast0 (target_decl, source_expr, _)) =
        let val (source_term, source_cty) = translate_expr tctx source_expr
            val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val target_cty =
              (case target_decl of
                 CDecl0 (specs, declrs, _) =>
                   let val struct_names = C_Trans_Ctxt.get_struct_names tctx
                       val base_cty =
                         (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                            SOME ct => SOME ct
                          | NONE =>
                              (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                                 SOME sn => SOME (C_Ast_Utils.CStruct sn)
                               | NONE =>
                                   (case C_Ast_Utils.extract_union_type_from_specs_full (!current_union_names) specs of
                                      SOME un => SOME (C_Ast_Utils.CUnion un)
                                    | NONE => NONE)))
                       val ptr_depth =
                         List.mapPartial
                           (fn ((Some declr, _), _) => SOME (C_Ast_Utils.pointer_depth_of_declr declr)
                             | _ => NONE) declrs
                         |> (fn d :: _ => d | [] => 0)
                   in case base_cty of
                        SOME ct => C_Ast_Utils.apply_ptr_depth ct ptr_depth
                      | NONE => unsupported "cast to non-numeric type"
                   end
               | _ => unsupported "cast to non-numeric type")
        in (mk_implicit_cast (source_term, source_cty, target_cty), target_cty)
        end
    (* sizeof(type) *)
    | translate_expr tctx (CSizeofType0 (decl, _)) =
        let val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val cty =
              (case decl of
                 CDecl0 (specs, declrs, _) =>
                   let val struct_names = C_Trans_Ctxt.get_struct_names tctx
                       val base_cty =
                         (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                            SOME ct => SOME ct
                          | NONE =>
                              (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                                 SOME sn => SOME (C_Ast_Utils.CStruct sn)
                               | NONE =>
                                   (case C_Ast_Utils.extract_union_type_from_specs_full (!current_union_names) specs of
                                      SOME un => SOME (C_Ast_Utils.CUnion un)
                                    | NONE => NONE)))
                       val ptr_depth =
                         List.mapPartial
                           (fn ((Some declr, _), _) => SOME (C_Ast_Utils.pointer_depth_of_declr declr)
                             | _ => NONE) declrs
                         |> (fn d :: _ => d | [] => 0)
                   in case base_cty of
                        SOME ct => C_Ast_Utils.apply_ptr_depth ct ptr_depth
                      | NONE => unsupported "sizeof non-numeric type"
                   end
               | _ => unsupported "sizeof non-numeric type")
            val size_cty = C_Ast_Utils.pointer_uint_cty ()
            val word_ty = C_Ast_Utils.hol_type_of size_cty
            val sizeof_term =
              (case cty of
                 C_Ast_Utils.CStruct sn =>
                   let val fields =
                         (case C_Trans_Ctxt.get_struct_fields tctx sn of
                            SOME fs => fs
                          | NONE => error ("micro_c_translate: sizeof: unknown struct: " ^ sn))
                       val sz = sizeof_struct fields
                   in Isa_Const (\<^const_name>\<open>of_nat\<close>, @{typ nat} --> word_ty) $ HOLogic.mk_nat sz end
               | C_Ast_Utils.CPtr _ =>
                   let val bytes = C_Ast_Utils.sizeof_c_type cty
                   in Isa_Const (\<^const_name>\<open>of_nat\<close>, @{typ nat} --> word_ty) $ HOLogic.mk_nat bytes end
               | _ =>
                   let val isa_ty = C_Ast_Utils.hol_type_of cty
                       val itself_ty = Isa_Type (\<^type_name>\<open>itself\<close>, [isa_ty])
                       val type_term = Isa_Const (\<^const_name>\<open>Pure.type\<close>, itself_ty)
                       val sizeof_nat = Isa_Const (\<^const_name>\<open>c_sizeof\<close>,
                                           itself_ty --> @{typ nat}) $ type_term
                   in Isa_Const (\<^const_name>\<open>of_nat\<close>, @{typ nat} --> word_ty) $ sizeof_nat end)
        in (C_Term_Build.mk_literal sizeof_term, size_cty) end
    (* sizeof(expr) *)
    | translate_expr tctx (CSizeofExpr0 (expr, _)) =
        let fun sizeof_nat_term cty =
                  let val isa_ty = C_Ast_Utils.hol_type_of cty
                      val itself_ty = Isa_Type (\<^type_name>\<open>itself\<close>, [isa_ty])
                      val type_term = Isa_Const (\<^const_name>\<open>Pure.type\<close>, itself_ty)
                  in Isa_Const (\<^const_name>\<open>c_sizeof\<close>, itself_ty --> @{typ nat}) $ type_term end
            fun sizeof_nat_for_cty (C_Ast_Utils.CStruct sn) =
                  let val fields =
                        (case C_Trans_Ctxt.get_struct_fields tctx sn of
                           SOME fs => fs
                         | NONE => error ("micro_c_translate: sizeof: unknown struct: " ^ sn))
                  in HOLogic.mk_nat (sizeof_struct fields) end
              | sizeof_nat_for_cty (C_Ast_Utils.CPtr ptr_cty) =
                  HOLogic.mk_nat (C_Ast_Utils.sizeof_c_type (C_Ast_Utils.CPtr ptr_cty))
              | sizeof_nat_for_cty cty = sizeof_nat_term cty
            val sizeof_nat =
              (case expr of
                 CVar0 (ident, _) =>
                   let val name = C_Ast_Utils.ident_name ident
                   in case C_Trans_Ctxt.lookup_array_decl tctx name of
                        SOME (elem_cty, n) =>
                          Isa_Const (\<^const_name>\<open>Groups.times_class.times\<close>, @{typ nat} --> @{typ nat} --> @{typ nat})
                            $ HOLogic.mk_nat n
                            $ sizeof_nat_for_cty elem_cty
                      | NONE =>
                          let val (_, cty) = translate_expr tctx expr
                          in sizeof_nat_for_cty cty end
                   end
               | _ =>
                   let val (_, cty) = translate_expr tctx expr
                   in sizeof_nat_for_cty cty end)
            val size_cty = C_Ast_Utils.pointer_uint_cty ()
            val word_ty = C_Ast_Utils.hol_type_of size_cty
            val sizeof_term = Isa_Const (\<^const_name>\<open>of_nat\<close>,
                                @{typ nat} --> word_ty) $ sizeof_nat
        in (C_Term_Build.mk_literal sizeof_term, size_cty) end
    | translate_expr tctx (CAlignofType0 (decl, _)) =
        let val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val cty =
              (case decl of
                 CDecl0 (specs, declrs, _) =>
                   let val struct_names = C_Trans_Ctxt.get_struct_names tctx
                       val base_cty =
                         (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                            SOME ct => SOME ct
                          | NONE =>
                              (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                                 SOME sn => SOME (C_Ast_Utils.CStruct sn)
                               | NONE => NONE))
                       val ptr_depth =
                         List.mapPartial
                           (fn ((Some declr, _), _) => SOME (C_Ast_Utils.pointer_depth_of_declr declr)
                             | _ => NONE) declrs
                         |> (fn d :: _ => d | [] => 0)
                   in case base_cty of
                        SOME ct => C_Ast_Utils.apply_ptr_depth ct ptr_depth
                      | NONE => unsupported "_Alignof non-numeric type"
                   end
               | _ => unsupported "_Alignof non-numeric type")
            val isa_ty = C_Ast_Utils.hol_type_of cty
            val itself_ty = Isa_Type (\<^type_name>\<open>itself\<close>, [isa_ty])
            val type_term = Isa_Const (\<^const_name>\<open>Pure.type\<close>, itself_ty)
            val alignof_nat = Isa_Const (\<^const_name>\<open>c_alignof\<close>,
                                itself_ty --> @{typ nat}) $ type_term
            val size_cty = C_Ast_Utils.pointer_uint_cty ()
            val word_ty = C_Ast_Utils.hol_type_of size_cty
            val alignof_term = Isa_Const (\<^const_name>\<open>of_nat\<close>,
                                @{typ nat} --> word_ty) $ alignof_nat
        in (C_Term_Build.mk_literal alignof_term, size_cty) end
    | translate_expr tctx (CAlignofExpr0 (expr, _)) =
        let val (_, cty) = translate_expr tctx expr
            val isa_ty = C_Ast_Utils.hol_type_of cty
            val itself_ty = Isa_Type (\<^type_name>\<open>itself\<close>, [isa_ty])
            val type_term = Isa_Const (\<^const_name>\<open>Pure.type\<close>, itself_ty)
            val alignof_nat = Isa_Const (\<^const_name>\<open>c_alignof\<close>,
                                itself_ty --> @{typ nat}) $ type_term
            val size_cty = C_Ast_Utils.pointer_uint_cty ()
            val word_ty = C_Ast_Utils.hol_type_of size_cty
            val alignof_term = Isa_Const (\<^const_name>\<open>of_nat\<close>,
                                @{typ nat} --> word_ty) $ alignof_nat
        in (C_Term_Build.mk_literal alignof_term, size_cty) end
    (* Compound literal: (type){init_list} *)
    | translate_expr tctx (CCompoundLit0 (decl, init_list, _)) =
        let val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val cty =
              (case decl of
                 CDecl0 (specs, declrs, _) =>
                   let val struct_names = C_Trans_Ctxt.get_struct_names tctx
                       val base_cty =
                         (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                            SOME ct => SOME ct
                          | NONE =>
                              (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                                 SOME sn => SOME (C_Ast_Utils.CStruct sn)
                               | NONE => NONE))
                       val ptr_depth =
                         List.mapPartial
                           (fn ((Some declr, _), _) => SOME (C_Ast_Utils.pointer_depth_of_declr declr)
                             | _ => NONE) declrs
                         |> (fn d :: _ => d | [] => 0)
                   in case base_cty of
                        SOME ct => C_Ast_Utils.apply_ptr_depth ct ptr_depth
                      | NONE => unsupported "compound literal with unsupported type"
                   end
               | _ => unsupported "compound literal with unsupported declaration")
        in case init_list of
             [([], CInitExpr0 (expr, _))] =>
               (* Scalar compound literal: (type){value} *)
               let val (expr_term, expr_cty) = translate_expr tctx expr
               in (mk_implicit_cast (expr_term, expr_cty, cty), cty) end
           | _ => unsupported "compound literal with complex initializer"
        end
    | translate_expr tctx (CGenericSelection0 (ctrl_expr, assoc_list, _)) =
        (* _Generic(ctrl, type1: expr1, ..., default: expr_default)
           Resolved at translation time based on the controlling expression's type. *)
        let val (_, ctrl_cty) = translate_expr tctx ctrl_expr
            val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val struct_names = C_Trans_Ctxt.get_struct_names tctx
            fun resolve_assoc_type (CDecl0 (specs, _, _)) =
                  (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                     SOME ct => ct
                   | NONE =>
                       (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                          SOME sn => C_Ast_Utils.CStruct sn
                        | NONE => unsupported "_Generic association type"))
              | resolve_assoc_type _ = unsupported "_Generic association type"
            fun find_match [] default_opt =
                  (case default_opt of
                     SOME expr => translate_expr tctx expr
                   | NONE => unsupported "_Generic: no matching association and no default")
              | find_match ((None, expr) :: rest) _ =
                  find_match rest (SOME expr)
              | find_match ((Some decl, expr) :: rest) default_opt =
                  if resolve_assoc_type decl = ctrl_cty
                  then translate_expr tctx expr
                  else find_match rest default_opt
        in find_match assoc_list NONE end
    | translate_expr _ _ =
        unsupported "expression"

  and translate_lvalue_location tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Local, ref_var, cty) =>
               (C_Term_Build.mk_literal ref_var, C_Ast_Utils.CPtr cty)
           | SOME (C_Trans_Ctxt.LocalPtr, _, _) =>
               unsupported ("address-of pointer local variable not supported: " ^ name)
           | SOME (C_Trans_Ctxt.Param, _, _) =>
               unsupported ("address-of by-value parameter: " ^ name)
           | NONE =>
               (case C_Trans_Ctxt.lookup_global_const tctx name of
                  SOME (tm, _) =>
                    (case C_Trans_Ctxt.lookup_array_decl tctx name of
                       SOME (elem_cty, _) => (C_Term_Build.mk_literal tm, C_Ast_Utils.CPtr elem_cty)
                     | NONE => unsupported ("address-of global const without reference storage not supported: " ^ name))
                | NONE =>
                    error ("micro_c_translate: undefined variable: " ^ name))
        end
    | translate_lvalue_location tctx (CUnary0 (CIndOp0, expr, _)) =
        let val (ptr_term, ptr_cty) = translate_expr tctx expr
        in case ptr_cty of
             C_Ast_Utils.CPtr _ => (ptr_term, ptr_cty)
           | _ => unsupported "address-of dereference on non-pointer expression"
        end
    | translate_lvalue_location tctx (CMember0 (expr, field_ident, is_ptr, _)) =
        let
          val field_name = C_Ast_Utils.ident_name field_ident
          val struct_name = determine_struct_type tctx expr
          val field_cty =
            (case C_Trans_Ctxt.lookup_struct_field_type tctx struct_name field_name of
               SOME cty => cty
             | NONE => unsupported ("unknown struct field type: " ^ struct_name ^ "." ^ field_name))
          val focus_const = resolve_struct_focus_const (C_Trans_Ctxt.get_ctxt tctx) struct_name field_name
          val (base_expr, base_is_raw) =
            if is_ptr then
              let val (ptr_expr, ptr_cty) =
                    (case expr of
                       CCast0 (_, inner_expr, _) =>
                         let val (inner_ptr, inner_cty) = translate_expr tctx inner_expr
                         in case inner_cty of
                              C_Ast_Utils.CPtr C_Ast_Utils.CVoid => (inner_ptr, inner_cty)
                            | C_Ast_Utils.CPtr (C_Ast_Utils.CUnion _) => (inner_ptr, inner_cty)
                            | _ => translate_expr tctx expr
                         end
                     | _ => translate_expr tctx expr)
              in case ptr_cty of
                   C_Ast_Utils.CPtr C_Ast_Utils.CVoid => (ptr_expr, true)
                 | C_Ast_Utils.CPtr (C_Ast_Utils.CUnion _) => (ptr_expr, true)
                 | C_Ast_Utils.CPtr _ => (ptr_expr, false)
                 | _ => unsupported "member access through non-pointer expression"
              end
            else
              (#1 (translate_lvalue_location tctx expr), false)
        in
          if base_is_raw then
            (mk_raw_struct_field_loc_expr tctx struct_name field_name field_cty base_expr,
             C_Ast_Utils.CPtr field_cty)
          else
            let
              val base_ty = expr_value_type base_expr
              val base_var = Isa_Free ("v__base_loc", if base_ty = isa_dummyT then isa_dummyT else base_ty)
              val focused = C_Term_Build.mk_focus_field focus_const base_var
            in
              (C_Term_Build.mk_bind base_expr (Term.lambda base_var (C_Term_Build.mk_literal focused)),
               C_Ast_Utils.CPtr field_cty)
            end
        end
    | translate_lvalue_location tctx (CIndex0 (arr_expr, idx_expr, _)) =
        let
          val allow_fallback =
            (case arr_expr of
               CMember0 _ => false
             | _ => true)
          fun fallback_to_expr msg =
            String.isSubstring "address-of non-lvalue expression" msg orelse
            String.isSubstring "address-of by-value parameter" msg
          val (arr_term, arr_cty) =
            (translate_lvalue_location tctx arr_expr
             handle ERROR msg =>
               if allow_fallback andalso fallback_to_expr msg then translate_expr tctx arr_expr
               else raise ERROR msg)
          val (idx_term_raw, idx_cty) = translate_expr tctx idx_expr
          val ctxt = C_Trans_Ctxt.get_ctxt tctx
          val deref_const = resolve_dereference_const ctxt
          val idx_p_cty = C_Ast_Utils.integer_promote idx_cty
          val idx_term = mk_implicit_cast (idx_term_raw, idx_cty, idx_p_cty)
          val arr_is_global_const =
            (case arr_expr of
               CVar0 (ident, _) =>
                 (case C_Trans_Ctxt.lookup_global_const tctx (C_Ast_Utils.ident_name ident) of
                    SOME _ => true
                  | NONE => false)
             | _ => false)
          val arr_has_effect = C_Ast_Utils.expr_has_side_effect arr_expr
          val idx_has_effect = C_Ast_Utils.expr_has_side_effect idx_expr
          val unseq_index = arr_has_effect orelse idx_has_effect
          val _ =
            if arr_is_global_const then
              unsupported "address-of global constant array element is not supported without reference storage"
            else if unseq_index andalso C_Ast_Utils.expr_has_unsequenced_ub_risk arr_expr idx_expr then
              unsupported "potential unsequenced side-effect UB in indexed lvalue"
            else ()
          val a_var = Isa_Free ("v__arr_loc", isa_dummyT)
          val i_var = Isa_Free ("v__idx", isa_dummyT)
          val deref_expr =
            Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
              $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ a_var)
              $ (Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                   $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                   $ deref_const)
          val elem_cty =
            (case arr_cty of
               C_Ast_Utils.CPtr inner => inner
             | _ => unsupported "indexing non-array expression")
          val loc_expr =
            if use_raw_pointer_indexing tctx arr_expr then
              mk_raw_ptr_loc_expr ctxt unseq_index arr_term idx_term_raw idx_cty elem_cty (is_nonnegative_int_const idx_expr)
            else
              let
                val focused = C_Term_Build.mk_focus_nth (C_Term_Build.mk_unat i_var) a_var
                val list_var =
                  let
                    val list_ty =
                      (case C_Ast_Utils.hol_type_of elem_cty of
                         t => if t = isa_dummyT then isa_dummyT
                              else Isa_Type (\<^type_name>\<open>list\<close>, [t]))
                  in Isa_Free ("v__arr_vals", list_ty) end
              in
                mk_pair_eval unseq_index arr_term idx_term a_var i_var
                  (C_Term_Build.mk_bind deref_expr
                     (Term.lambda list_var
                       (mk_index_guard idx_p_cty i_var list_var
                         (C_Term_Build.mk_literal focused))))
              end
        in (loc_expr, C_Ast_Utils.CPtr elem_cty) end
    | translate_lvalue_location _ _ =
        unsupported "address-of non-lvalue expression"

  (* Convenience: extract just the term from translate_expr *)
  and expr_term tctx e = #1 (translate_expr tctx e)

  (* Ensure a C expression produces a bool condition.
     In C, any scalar value in a condition position is implicitly converted
     to bool via != 0. If the expression already produces CBool (from a
     comparison or _Bool variable), use it directly. Otherwise, wrap with
     bind expr (\<lambda>v. literal (v \<noteq> 0)). *)
  and ensure_bool_cond tctx cond_expr =
    let val (cond_term, cond_cty) = translate_expr tctx cond_expr
    in mk_implicit_cast (cond_term, cond_cty, C_Ast_Utils.CBool)
    end

  (* Extract variable declarations as a list of (name, init_term, cty, array_meta, list_backed_ptr_alias) tuples.
     Handles multiple declarators in a single CDecl0.
     For pointer declarators (e.g. int *p = &x), the returned cty is CPtr base_cty. *)
  fun translate_decl tctx (CDecl0 (specs, declarators, _)) =
        let val typedef_tab = C_Trans_Ctxt.get_typedef_tab tctx
            val struct_names = C_Trans_Ctxt.get_struct_names tctx
            val cty =
              (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                 SOME C_Ast_Utils.CVoid => C_Ast_Utils.CInt
               | SOME t => t
               | NONE =>
                   (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                      SOME sn => C_Ast_Utils.CStruct sn
                    | NONE =>
                        (case C_Ast_Utils.extract_union_type_from_specs_full (!current_union_names) specs of
                           SOME un => C_Ast_Utils.CUnion un
                         | NONE => C_Ast_Utils.CInt)))
            fun pointer_depth_of_declr declr = C_Ast_Utils.pointer_depth_of_declr declr
            fun has_array_declr (CDeclr0 (_, derived, _, _, _)) =
                  List.exists (fn CArrDeclr0 _ => true | _ => false) derived
            fun array_decl_size (CDeclr0 (_, derived, _, _, _)) =
                  List.mapPartial
                    (fn CArrDeclr0 (_, CArrSize0 (_, CConst0 (CIntConst0 (CInteger0 (n, _, _), _))), _) =>
                          if n < 0 then
                            error "micro_c_translate: negative array bound not supported"
                          else
                            SOME (intinf_to_int_checked "array bound" n)
                      | _ => NONE) derived
                  |> (fn n :: _ => SOME n | [] => NONE)
            fun init_scalar_const_value (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) = n
              | init_scalar_const_value (CConst0 (CCharConst0 (CChar0 (c, _), _))) =
                  integer_of_char c
              | init_scalar_const_value (CVar0 (ident, _)) =
                  let val name = C_Ast_Utils.ident_name ident
                  in case C_Trans_Ctxt.lookup_enum_const tctx name of
                       SOME value => IntInf.fromInt value
                     | NONE =>
                         unsupported ("unsupported array initializer element: " ^ name)
                  end
              | init_scalar_const_value (CUnary0 (CMinOp0, e, _)) =
                  IntInf.~ (init_scalar_const_value e)
              | init_scalar_const_value (CUnary0 (CPlusOp0, e, _)) =
                  init_scalar_const_value e
              | init_scalar_const_value (CCast0 (_, e, _)) =
                  init_scalar_const_value e
              | init_scalar_const_value _ =
                  unsupported "non-constant array initializer element"
            fun string_literal_bytes (CConst0 (CStrConst0 (CString0 (abr_str, _), _))) =
                  SOME (List.map Char.ord
                    (String.explode (C_Ast_Utils.abr_string_to_string abr_str)))
              | string_literal_bytes _ = NONE
            fun init_scalar_const_term target_cty expr =
                  HOLogic.mk_number (C_Ast_Utils.hol_type_of target_cty)
                    (intinf_to_int_checked "array initializer literal"
                      (init_scalar_const_value expr))
            fun process_one ((Some declr, Some (CInitExpr0 (init, _))), _) =
                  let val name = C_Ast_Utils.declr_name declr
                      val ptr_depth = pointer_depth_of_declr declr
                      val actual_cty = C_Ast_Utils.apply_ptr_depth cty ptr_depth
                  in
                    case (has_array_declr declr, string_literal_bytes init) of
                      (true, SOME char_ords) =>
                        let val elem_cty =
                              if ptr_depth > 0
                              then C_Ast_Utils.apply_ptr_depth cty (ptr_depth - 1) else cty
                            val elem_type = C_Ast_Utils.hol_type_of elem_cty
                            val with_null =
                              List.map (fn b => HOLogic.mk_number elem_type b) char_ords
                              @ [HOLogic.mk_number elem_type 0]
                            val declared_n = array_decl_size declr
                            val arr_size =
                              case declared_n of SOME n => n | NONE => List.length with_null
                            val padded =
                              case declared_n of
                                SOME n =>
                                  if List.length with_null > n then
                                    unsupported "string initializer too long for array"
                                  else with_null @ List.tabulate
                                    (n - List.length with_null,
                                     fn _ => HOLogic.mk_number elem_type 0)
                              | NONE => with_null
                            val list_term =
                              C_Term_Build.mk_literal (HOLogic.mk_list elem_type padded)
                        in (name, list_term, actual_cty, SOME (elem_cty, arr_size), false) end
                    | _ =>
                        let val (init_raw, init_cty) = translate_expr tctx init
                            val init_term = mk_implicit_cast (init_raw, init_cty, actual_cty)
                            val arr_meta =
                              (case array_decl_size declr of
                                 SOME n =>
                                   if ptr_depth > 0
                                   then SOME (C_Ast_Utils.apply_ptr_depth cty (ptr_depth - 1), n)
                                   else NONE
                               | NONE => NONE)
                            val alias_list_backed =
                              C_Ast_Utils.is_ptr actual_cty andalso expr_is_list_backed_array tctx init
                        in (name, init_term, actual_cty, arr_meta, alias_list_backed) end
                  end
              | process_one ((Some declr, Some (CInitList0 (init_list, _))), _) =
                  let val name = C_Ast_Utils.declr_name declr
                      val ptr_depth = pointer_depth_of_declr declr
                      val actual_cty = C_Ast_Utils.apply_ptr_depth cty ptr_depth
                  in if has_array_declr declr then
                      let val elem_cty =
                            if ptr_depth > 0 then C_Ast_Utils.apply_ptr_depth cty (ptr_depth - 1) else cty
                          val elem_type = C_Ast_Utils.hol_type_of elem_cty
                          (* Resolve position for each element: designators set explicit index,
                             positional elements use sequential position *)
                          fun resolve_desig_idx [] pos = pos
                            | resolve_desig_idx [CArrDesig0 (CConst0 (CIntConst0 (CInteger0 (n, _, _), _)), _)] _ =
                                intinf_to_int_checked "array designator" n
                            | resolve_desig_idx _ _ = unsupported "complex designator in array initializer"
                          fun collect_indices [] _ = []
                            | collect_indices ((desigs, CInitExpr0 (e, _)) :: rest) pos =
                                let val idx = resolve_desig_idx desigs pos
                                in (idx, e) :: collect_indices rest (idx + 1) end
                            | collect_indices _ _ = unsupported "complex array initializer element"
                          val indexed_items = collect_indices init_list 0
                          val has_designators = List.exists (fn (desigs, _) => not (null desigs)) init_list
                          val declared_size = array_decl_size declr
                          val arr_size = case declared_size of
                              SOME n => n
                            | NONE => List.length indexed_items
                          val _ = if List.length indexed_items > arr_size andalso not has_designators
                                  then error "micro_c_translate: too many initializers for array"
                                  else ()
                          val _ = List.app (fn (idx, _) =>
                              if idx < 0 orelse idx >= arr_size
                              then error ("micro_c_translate: designator index " ^
                                          Int.toString idx ^ " out of bounds for array of size " ^
                                          Int.toString arr_size)
                              else ()) indexed_items
                          (* Try constant path first *)
                          val const_results = List.map (fn (idx, e) =>
                              let val v = (SOME (init_scalar_const_term elem_cty e) handle ERROR _ => NONE)
                              in (idx, v) end) indexed_items
                          val all_const = List.all (fn (_, v) => Option.isSome v) const_results
                          val zero_value = HOLogic.mk_number elem_type 0
                          val init_term =
                            if all_const then
                              (* All-constant: build zero array, fill in designated positions *)
                              let val base = List.tabulate (arr_size, fn _ => zero_value)
                                  val filled = List.foldl (fn ((idx, SOME v), arr) =>
                                        nth_map idx (K v) arr
                                      | _ => raise Match) base const_results
                              in C_Term_Build.mk_literal (HOLogic.mk_list elem_type filled) end
                            else
                              (* Monadic: evaluate all init values, build array with designators *)
                              let val init_exprs = List.map (fn (_, e) =>
                                      let val (raw, raw_cty) = translate_expr tctx e
                                      in mk_implicit_cast (raw, raw_cty, elem_cty) end) indexed_items
                                  val n = List.length init_exprs
                                  val vars = List.tabulate (n,
                                      fn i => Isa_Free ("v__init_" ^ Int.toString i, isa_dummyT))
                                  (* Build array: start with zeros, place vars at designated positions *)
                                  val base = List.tabulate (arr_size, fn _ => zero_value)
                                  val filled = ListPair.foldl
                                    (fn ((idx, _), var, arr) => nth_map idx (K var) arr)
                                    base (indexed_items, vars)
                                  val result_list = HOLogic.mk_list elem_type filled
                                  val result = C_Term_Build.mk_literal result_list
                              in ListPair.foldr
                                   (fn (expr, var, acc) =>
                                     C_Term_Build.mk_bind expr (Term.lambda var acc))
                                   result (init_exprs, vars)
                              end
                          val arr_meta =
                            (case declared_size of
                               SOME n => SOME (elem_cty, n)
                             | NONE => NONE)
                      in (name, init_term, actual_cty, arr_meta, false) end
                     else (case actual_cty of
                        C_Ast_Utils.CStruct struct_name =>
                          let val fields =
                                (case C_Trans_Ctxt.get_struct_fields tctx struct_name of
                                   SOME fs => fs
                                 | NONE => error ("micro_c_translate: unknown struct: " ^ struct_name))
                              (* Map each init item to (field_index, expr_opt, initlist_opt) *)
                              fun find_field_index _ [] _ =
                                    error "micro_c_translate: struct field not found"
                                | find_field_index fname ((n, _) :: rest) i =
                                    if n = fname then i
                                    else find_field_index fname rest (i + 1)
                              fun resolve_field_desig [] pos = pos
                                | resolve_field_desig [CMemberDesig0 (ident, _)] _ =
                                    find_field_index (C_Ast_Utils.ident_name ident) fields 0
                                | resolve_field_desig _ _ =
                                    unsupported "complex designator in struct initializer"
                              (* field_items: (idx, SOME expr, NONE) for scalar, (idx, NONE, SOME init_list) for nested *)
                              fun collect_field_items [] _ = []
                                | collect_field_items ((desigs, CInitExpr0 (e, _)) :: rest) pos =
                                    let val idx = resolve_field_desig desigs pos
                                    in (idx, SOME e, NONE) :: collect_field_items rest (idx + 1) end
                                | collect_field_items ((desigs, CInitList0 (inner_list, _)) :: rest) pos =
                                    let val idx = resolve_field_desig desigs pos
                                    in (idx, NONE, SOME inner_list) :: collect_field_items rest (idx + 1) end
                              val field_items = collect_field_items init_list 0
                              (* Helper: build constant array list from CInitList items *)
                              fun build_const_array_from_initlist arr_elem_cty arr_sz inner_list =
                                let val elem_type = C_Ast_Utils.hol_type_of arr_elem_cty
                                    fun resolve_arr_desig [] pos = pos
                                      | resolve_arr_desig [CArrDesig0 (CConst0 (CIntConst0 (CInteger0 (n, _, _), _)), _)] _ =
                                          intinf_to_int_checked "nested array designator" n
                                      | resolve_arr_desig _ _ = unsupported "complex nested array designator"
                                    fun collect_arr [] _ = []
                                      | collect_arr ((ds, CInitExpr0 (e, _)) :: rest) pos =
                                          let val idx = resolve_arr_desig ds pos
                                          in (idx, e) :: collect_arr rest (idx + 1) end
                                      | collect_arr _ _ = unsupported "complex nested array init element"
                                    val indexed = collect_arr inner_list 0
                                    val sz = case arr_sz of SOME n => n | NONE => List.length indexed
                                    val zero_val = HOLogic.mk_number elem_type 0
                                    val base = List.tabulate (sz, fn _ => zero_val)
                                    val filled = List.foldl (fn ((idx, e), arr) =>
                                        nth_map idx (K (init_scalar_const_term arr_elem_cty e)) arr) base indexed
                                in HOLogic.mk_list elem_type filled end
                              (* Helper: try to produce a constant init value for a field *)
                              fun try_const_field_val field_cty (SOME e) NONE =
                                    (SOME (init_scalar_const_term field_cty e) handle ERROR _ => NONE)
                                | try_const_field_val field_cty NONE (SOME inner_list) =
                                    (case field_cty of
                                       C_Ast_Utils.CPtr elem_cty =>
                                         (SOME (build_const_array_from_initlist elem_cty NONE inner_list)
                                          handle ERROR _ => NONE)
                                     | _ => NONE)
                                | try_const_field_val _ _ _ = NONE  (* e.g. both NONE *)
                              (* Helper: translate a field init value monadically *)
                              fun translate_field_val field_cty (SOME e) NONE =
                                    let val (raw, raw_cty) = translate_expr tctx e
                                    in mk_implicit_cast (raw, raw_cty, field_cty) end
                                | translate_field_val field_cty NONE (SOME inner_list) =
                                    (case field_cty of
                                       C_Ast_Utils.CPtr elem_cty =>
                                         let val elem_type = C_Ast_Utils.hol_type_of elem_cty
                                             fun resolve_arr_desig [] pos = pos
                                               | resolve_arr_desig [CArrDesig0 (CConst0 (CIntConst0 (CInteger0 (n, _, _), _)), _)] _ =
                                                   intinf_to_int_checked "nested array designator" n
                                               | resolve_arr_desig _ _ = unsupported "complex nested array designator"
                                             fun collect_arr [] _ = []
                                               | collect_arr ((ds, CInitExpr0 (e, _)) :: rest) pos =
                                                   let val idx = resolve_arr_desig ds pos
                                                   in (idx, e) :: collect_arr rest (idx + 1) end
                                               | collect_arr _ _ = unsupported "complex nested array init element"
                                             val indexed = collect_arr inner_list 0
                                             val sz = List.length indexed
                                             val zero_val = HOLogic.mk_number elem_type 0
                                             val init_exprs_inner = List.map (fn (_, e) =>
                                                 let val (raw, raw_cty) = translate_expr tctx e
                                                 in mk_implicit_cast (raw, raw_cty, elem_cty) end) indexed
                                             val nn = List.length init_exprs_inner
                                             val vars = List.tabulate (nn,
                                                 fn i => Isa_Free ("v__ainit_" ^ Int.toString i, isa_dummyT))
                                             val base = List.tabulate (sz, fn _ => zero_val)
                                             val filled = ListPair.foldl
                                               (fn ((idx, _), var, arr) => nth_map idx (K var) arr)
                                               base (indexed, vars)
                                             val result_list = HOLogic.mk_list elem_type filled
                                             val result = C_Term_Build.mk_literal result_list
                                         in ListPair.foldr
                                              (fn (expr, var, acc) =>
                                                C_Term_Build.mk_bind expr (Term.lambda var acc))
                                              result (init_exprs_inner, vars)
                                         end
                                     | _ => unsupported "nested init list for non-array struct field")
                                | translate_field_val _ _ _ =
                                    unsupported "malformed struct field initializer"
                              (* Try constant path first *)
                              val const_results = List.map (fn (idx, e_opt, il_opt) =>
                                  let val (_, field_cty) = List.nth (fields, idx)
                                      val v = try_const_field_val field_cty e_opt il_opt
                                  in (idx, v) end) field_items
                              val all_const = List.all (fn (_, v) => Option.isSome v) const_results
                              val ctxt_inner = C_Trans_Ctxt.get_ctxt tctx
                              val make_name = "make_" ^ (!current_decl_prefix) ^ struct_name
                              val make_const =
                                Proof_Context.read_const {proper = true, strict = false}
                                  ctxt_inner make_name
                              fun default_for_field (_, field_cty) =
                                (case field_cty of
                                   C_Ast_Utils.CPtr elem_cty =>
                                     HOLogic.mk_list (C_Ast_Utils.hol_type_of elem_cty) []
                                 | _ => HOLogic.mk_number (C_Ast_Utils.hol_type_of field_cty) 0)
                              val init_term =
                                if all_const then
                                  let val base_vals = List.map default_for_field fields
                                      val filled = List.foldl (fn ((idx, SOME v), arr) =>
                                            nth_map idx (K v) arr
                                          | _ => raise Match) base_vals const_results
                                      val struct_term = List.foldl (fn (v, acc) => acc $ v)
                                            make_const filled
                                  in C_Term_Build.mk_literal struct_term end
                                else
                                  let val init_exprs = List.map (fn (idx, e_opt, il_opt) =>
                                          let val (_, field_cty) = List.nth (fields, idx)
                                          in translate_field_val field_cty e_opt il_opt end)
                                        field_items
                                      val n = List.length init_exprs
                                      val vars = List.tabulate (n,
                                          fn i => Isa_Free ("v__sinit_" ^ Int.toString i, isa_dummyT))
                                      val base_vals = List.map default_for_field fields
                                      val filled = ListPair.foldl
                                        (fn ((idx, _, _), var, arr) => nth_map idx (K var) arr)
                                        base_vals (field_items, vars)
                                      val struct_term = List.foldl (fn (v, acc) => acc $ v)
                                            make_const filled
                                      val result = C_Term_Build.mk_literal struct_term
                                  in ListPair.foldr
                                       (fn (expr, var, acc) =>
                                         C_Term_Build.mk_bind expr (Term.lambda var acc))
                                       result (init_exprs, vars)
                                  end
                          in (name, init_term, actual_cty, NONE, false) end
                      | _ => unsupported "initializer list for non-array, non-struct declaration")
                  end
              | process_one ((Some declr, None), _) =
                  let val name = C_Ast_Utils.declr_name declr
                      val ptr_depth = pointer_depth_of_declr declr
                      val actual_cty = C_Ast_Utils.apply_ptr_depth cty ptr_depth
                      val uninit = Isa_Const (\<^const_name>\<open>c_uninitialized\<close>, isa_dummyT)
                      val arr_meta =
                        (case array_decl_size declr of
                           SOME n =>
                             if ptr_depth > 0
                             then SOME (C_Ast_Utils.apply_ptr_depth cty (ptr_depth - 1), n)
                             else NONE
                         | NONE => NONE)
                  in (name, C_Term_Build.mk_literal uninit, actual_cty, arr_meta, false) end
              | process_one _ = unsupported "complex declarator"
        in List.map process_one declarators end
    | translate_decl _ _ = unsupported "complex declaration"

  (* Find label names nested in statements/items, preserving first-seen order. *)
  fun find_stmt_labels (CLabel0 (ident, inner, _, _)) =
        C_Ast_Utils.ident_name ident :: find_stmt_labels inner
    | find_stmt_labels (CCompound0 (_, items, _)) = find_block_labels items
    | find_stmt_labels (CIf0 (_, thn, Some els, _)) =
        find_stmt_labels thn @ find_stmt_labels els
    | find_stmt_labels (CIf0 (_, thn, None, _)) = find_stmt_labels thn
    | find_stmt_labels (CWhile0 (_, body, _, _)) = find_stmt_labels body
    | find_stmt_labels (CFor0 (_, _, _, body, _)) = find_stmt_labels body
    | find_stmt_labels (CSwitch0 (_, body, _)) = find_stmt_labels body
    | find_stmt_labels _ = []
  and find_block_labels [] = []
    | find_block_labels (CBlockStmt0 stmt :: rest) =
        find_stmt_labels stmt @ find_block_labels rest
    | find_block_labels (_ :: rest) = find_block_labels rest

  (* Translate a compound block, right-folding declarations into nested binds.
     Goto support: when goto_refs is non-empty, each statement is guarded to be
     skipped if any active goto flag is set. At a label site, the corresponding
     goto flag is reset (written to 0) and removed from the active list. *)
  fun translate_compound_items _ [] = C_Term_Build.mk_literal_unit
    | translate_compound_items tctx [CBlockStmt0 stmt] =
        (* Last item: if it's a label, handle goto flag reset *)
        (case stmt of
           CLabel0 (ident, inner_stmt, _, _) =>
             let val label_name = C_Ast_Utils.ident_name ident
                 val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
                 val active' = List.filter (fn n => n <> label_name)
                                   (C_Trans_Ctxt.get_active_goto_labels tctx)
                 val tctx' = C_Trans_Ctxt.set_active_goto_labels active' tctx
             in case C_Trans_Ctxt.lookup_goto_ref tctx label_name of
                  SOME goto_ref =>
                    C_Term_Build.mk_sequence
                      (C_Term_Build.mk_var_write goto_ref false_lit)
                      (translate_stmt tctx' inner_stmt)
                | NONE => translate_stmt tctx' stmt
             end
         | _ => translate_stmt tctx stmt)
    | translate_compound_items _ [CNestedFunDef0 _] =
        unsupported "nested function definition"
    | translate_compound_items tctx (CBlockDecl0 decl :: rest) =
        let val decls = translate_decl tctx decl
            fun fold_decls [] tctx' = translate_compound_items tctx' rest
              | fold_decls ((name, init_term, cty, arr_meta, alias_list_backed) :: ds) tctx' =
                  if C_Ast_Utils.is_ptr cty andalso not (Option.isSome arr_meta) then
                    let
                        val ctxt' = C_Trans_Ctxt.get_ctxt tctx'
                        val supports_raw_ptr = supports_raw_ptr_local_refs ctxt'
                        val force_mutable_ptr =
                          List.exists (fn v => v = name) (!current_loop_written_vars)
                    in
                      if supports_raw_ptr andalso
                         (force_mutable_ptr orelse not (prefer_pointer_alias_storage alias_list_backed init_term)) then
                        let
                          val raw_ptr_ty = raw_ptr_local_gref_typ ()
                          val stored_init =
                            if is_uninitialized_literal init_term then init_term
                            else mk_implicit_cast (init_term, cty, C_Ast_Utils.CPtr C_Ast_Utils.CVoid)
                          val alloc_expr =
                            mk_resolved_var_alloc_typed ctxt' raw_ptr_ty stored_init
                          val var = mk_typed_ref_var tctx' name alloc_expr
                          val tctx'' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.LocalPtr var cty tctx'
                          val tctx'' = (case struct_name_of_cty cty of
                                          SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx''
                                        | NONE => tctx'')
                          val tctx'' = (case arr_meta of
                                          SOME (elem_cty, n) => C_Trans_Ctxt.set_array_decl name elem_cty n tctx''
                                        | NONE => tctx'')
                        in C_Term_Build.mk_bind alloc_expr
                             (Term.lambda var (fold_decls ds tctx'')) end
                      else
                        let
                            val var = Isa_Free (name, pointer_alias_var_ty tctx' alias_list_backed cty init_term)
                            val kind = pointer_alias_kind alias_list_backed
                            val tctx'' = C_Trans_Ctxt.add_var name kind var cty tctx'
                            val tctx'' = (case struct_name_of_cty cty of
                                            SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx''
                                          | NONE => tctx'')
                            val tctx'' = (case arr_meta of
                                            SOME (elem_cty, n) => C_Trans_Ctxt.set_array_decl name elem_cty n tctx''
                                          | NONE => tctx'')
                        in if is_uninitialized_literal init_term then
                             fold_decls ds tctx''
                           else
                             C_Term_Build.mk_bind init_term
                               (Term.lambda var (fold_decls ds tctx''))
                        end
                    end
                  else
                  let val val_type =
                        let val ty = C_Ast_Utils.hol_type_of cty
                        in if ty = isa_dummyT then expr_value_type init_term else ty end
                      val alloc_expr =
                        mk_resolved_var_alloc_typed (C_Trans_Ctxt.get_ctxt tctx') val_type init_term
                      val var = mk_typed_ref_var tctx' name alloc_expr
                      val tctx'' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.Local var cty tctx'
                      val tctx'' = (case struct_name_of_cty cty of
                                      SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx''
                                    | NONE => tctx'')
                      val tctx'' = (case arr_meta of
                                      SOME (elem_cty, n) => C_Trans_Ctxt.set_array_decl name elem_cty n tctx''
                                    | NONE => tctx'')
                  in C_Term_Build.mk_bind alloc_expr
                       (Term.lambda var (fold_decls ds tctx''))
                  end
        in fold_decls decls tctx end
    | translate_compound_items tctx (CBlockStmt0 (CLabel0 (ident, inner_stmt, _, _)) :: rest) =
        (* Label site: reset this label's goto flag, translate the labeled statement,
           then continue with the rest of the block *)
        let val label_name = C_Ast_Utils.ident_name ident
            val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
            val active' = List.filter (fn n => n <> label_name)
                              (C_Trans_Ctxt.get_active_goto_labels tctx)
            val tctx' = C_Trans_Ctxt.set_active_goto_labels active' tctx
            val stmt_term = translate_stmt tctx' inner_stmt
            val rest_term = translate_compound_items tctx' rest
        in case C_Trans_Ctxt.lookup_goto_ref tctx label_name of
             SOME goto_ref =>
               C_Term_Build.mk_sequence
                 (C_Term_Build.mk_var_write goto_ref false_lit)
                 (C_Term_Build.mk_sequence stmt_term rest_term)
           | NONE =>
               (* Label not targeted by any goto — just translate normally *)
               C_Term_Build.mk_sequence stmt_term rest_term
        end
    | translate_compound_items tctx (CBlockStmt0 stmt :: rest) =
        (* Pointer alias assignment: when a pointer-typed Param variable is assigned,
           rebind it via a monadic bind instead of writing to a reference.
           This handles patterns like: int16_t *r; ... r = p->coeffs; *)
        let val ptr_alias_result =
              (case stmt of
                 CExpr0 (Some (CAssign0 (CAssignOp0, CVar0 (ident, _), rhs, _)), _) =>
                   let val name = C_Ast_Utils.ident_name ident
                   in case C_Trans_Ctxt.lookup_var tctx name of
                        SOME (kind0, _, cty) =>
                          if C_Ast_Utils.is_ptr cty andalso
                             (case kind0 of
                                C_Trans_Ctxt.Param => true
                              | C_Trans_Ctxt.ParamListPtr => true
                              | _ => false)
                          then
                            let val (rhs_term, _) = translate_expr tctx rhs
                                val rhs_list_backed = expr_is_list_backed_array tctx rhs
                                val var = Isa_Free (name, pointer_alias_var_ty tctx rhs_list_backed cty rhs_term)
                                val kind = pointer_alias_kind rhs_list_backed
                                val tctx' = C_Trans_Ctxt.add_var name kind var cty tctx
                            in SOME (C_Term_Build.mk_bind rhs_term
                                 (Term.lambda var (translate_compound_items tctx' rest)))
                            end
                          else NONE
                      | _ => NONE
                   end
               | _ => NONE)
        in case ptr_alias_result of
             SOME result => result
           | NONE =>
        let val inherited_labels = C_Trans_Ctxt.get_active_goto_labels tctx
            val goto_refs = C_Trans_Ctxt.get_goto_refs tctx
            (* Determine which goto labels appear later in this block.
               Only those need guarding at this point. *)
            val later_labels = find_block_labels rest
            val active_labels = distinct (op =) (inherited_labels @ later_labels)
            val tctx_stmt = C_Trans_Ctxt.set_active_goto_labels active_labels tctx
            val stmt_term = translate_stmt tctx_stmt stmt
            val active_goto_refs = List.filter
              (fn (name, _) => List.exists (fn l => l = name) active_labels) goto_refs
        in case (C_Trans_Ctxt.get_break_ref tctx,
                 C_Trans_Ctxt.get_continue_ref tctx,
                 active_goto_refs) of
             (NONE, NONE, []) =>
               C_Term_Build.mk_sequence stmt_term
                 (translate_compound_items tctx rest)
           | _ =>
               let val guard_var = Isa_Free ("v__guard", isa_dummyT)
                   val guard_nonzero =
                     Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                     $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                        $ guard_var
                        $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                   (* Resolve dereference_fun from locale context to avoid
                      store_dereference_const adhoc overloading issues *)
                   val ctxt = C_Trans_Ctxt.get_ctxt tctx
                   val deref_const = resolve_dereference_const ctxt
                   val deref_fn =
                     Isa_Const (\<^const_name>\<open>deep_compose1\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                       $ Isa_Const (\<^const_name>\<open>call\<close>, isa_dummyT --> isa_dummyT)
                       $ deref_const
                   fun mk_guard_read ref_var =
                     Isa_Const (\<^const_name>\<open>Core_Expression.bind\<close>, isa_dummyT --> isa_dummyT --> isa_dummyT)
                       $ (Isa_Const (\<^const_name>\<open>Core_Expression.literal\<close>, isa_dummyT --> isa_dummyT) $ ref_var)
                       $ deref_fn
                   fun wrap_guard NONE inner = inner
                     | wrap_guard (SOME ref_var) inner =
                         C_Term_Build.mk_bind (mk_guard_read ref_var)
                           (Term.lambda guard_var
                             (C_Term_Build.mk_two_armed_cond
                               (C_Term_Build.mk_literal guard_nonzero)
                               C_Term_Build.mk_literal_unit inner))
                   fun wrap_goto_guards [] inner = inner
                     | wrap_goto_guards ((_, ref_var) :: refs) inner =
                         wrap_guard (SOME ref_var) (wrap_goto_guards refs inner)
                   (* Split rest into guarded prefix (before first active label)
                      and unguarded suffix (label + remaining items).
                      The label code must be outside the guard so that the return type
                      from return statements at/after the label doesn't clash with
                      the guard's then-branch (literal unit). *)
                   fun split_at_active_label [] = ([], [])
                     | split_at_active_label (all as (CBlockStmt0 (CLabel0 (ident, _, _, _)) :: _)) =
                         let val lname = C_Ast_Utils.ident_name ident
                         in if List.exists (fn (n, _) => n = lname) active_goto_refs
                            then ([], all)
                            else let val (pre, post) = split_at_active_label (tl all)
                                 in (hd all :: pre, post) end
                         end
                     | split_at_active_label (item :: items) =
                         let val (pre, post) = split_at_active_label items
                         in (item :: pre, post) end
                   val (guarded_items, label_suffix) = split_at_active_label rest
                   val guarded_term = translate_compound_items tctx_stmt guarded_items
                   val label_term = translate_compound_items tctx label_suffix
                   val guarded_part =
                     wrap_guard (C_Trans_Ctxt.get_break_ref tctx)
                       (wrap_guard (C_Trans_Ctxt.get_continue_ref tctx)
                         (wrap_goto_guards active_goto_refs guarded_term))
               in C_Term_Build.mk_sequence stmt_term
                    (C_Term_Build.mk_sequence guarded_part label_term)
               end
        end end
    | translate_compound_items _ _ = unsupported "block item"

  (* Translate a C expression to a pure nat term (for loop bounds).
     Only integer literals and parameter variables are supported. *)
  and translate_pure_nat_expr _ (CConst0 (CIntConst0 (CInteger0 (n, _, _), _))) =
        if n < 0
        then error "micro_c_translate: negative literal loop bound not supported in bounded-for lowering"
        else HOLogic.mk_nat (intinf_to_int_checked "for-loop bound literal" n)
    | translate_pure_nat_expr tctx (CVar0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
        in case C_Trans_Ctxt.lookup_var tctx name of
             SOME (C_Trans_Ctxt.Param, v, cty) =>
               if C_Ast_Utils.is_signed cty orelse C_Ast_Utils.is_bool cty orelse C_Ast_Utils.is_ptr cty
               then error ("micro_c_translate: loop bound parameter must be unsigned integer: " ^ name)
               else
               (* Convert parameter (word) to nat for range *)
               C_Term_Build.mk_unat v
           | _ => error ("micro_c_translate: loop bound must be a parameter or literal: " ^ name)
        end
    | translate_pure_nat_expr _ _ =
        error "micro_c_translate: unsupported loop bound expression"

  and try_translate_pure_nat_expr tctx e =
        SOME (translate_pure_nat_expr tctx e)
        handle ERROR _ => NONE

  (* Try to recognize: for (int i = start; i < bound; i++) body
     Returns SOME (var_name, start_nat, bound_nat, body) or NONE *)
  and try_bounded_for (CFor0 (Right init_decl, Some cond, Some step, body, _)) =
        let fun step_var_name (CUnary0 (CPostIncOp0, CVar0 (v, _), _)) =
                  SOME (C_Ast_Utils.ident_name v)
              | step_var_name (CUnary0 (CPreIncOp0, CVar0 (v, _), _)) =
                  SOME (C_Ast_Utils.ident_name v)
              | step_var_name _ = NONE
        in case (init_decl, cond, step_var_name step) of
             (CDecl0 (_, [((Some declr, Some (CInitExpr0 (init_expr, _))), _)], _),
              CBinary0 (CLeOp0, CVar0 (cond_var, _), bound_expr, _),
              SOME step_name) =>
               let val var_name = C_Ast_Utils.declr_name declr
                   val cond_name = C_Ast_Utils.ident_name cond_var
               in
                 if var_name = cond_name andalso var_name = step_name
                 then SOME (var_name, init_expr, bound_expr, body)
                 else NONE
               end
           | _ => NONE
        end
    | try_bounded_for _ = NONE

  and translate_stmt tctx (CCompound0 (_, items, _)) =
        translate_compound_items tctx items
    | translate_stmt _ (CReturn0 (None, _)) =
        C_Term_Build.mk_return_func C_Term_Build.mk_literal_unit
    | translate_stmt tctx (CReturn0 (Some expr, _)) =
        let val (term, expr_cty) = translate_expr tctx expr
            val ret_term = case !current_ret_cty of
                SOME ret_cty => mk_implicit_cast (term, expr_cty, ret_cty)
              | NONE => term
        in C_Term_Build.mk_return_func ret_term end
    | translate_stmt tctx (CExpr0 (Some expr, _)) =
        (* Expression statements are evaluated for side effects only.
           Discard the return value by sequencing with unit. *)
        C_Term_Build.mk_sequence (expr_term tctx expr) C_Term_Build.mk_literal_unit
    | translate_stmt _ (CExpr0 (None, _)) =
        C_Term_Build.mk_literal_unit
    | translate_stmt tctx (CIf0 (cond, then_br, Some else_br, _)) =
        C_Term_Build.mk_two_armed_cond
          (ensure_bool_cond tctx cond) (translate_stmt tctx then_br) (translate_stmt tctx else_br)
    | translate_stmt tctx (CIf0 (cond, then_br, None, _)) =
        C_Term_Build.mk_two_armed_cond
          (ensure_bool_cond tctx cond) (translate_stmt tctx then_br) C_Term_Build.mk_literal_unit
    | translate_stmt tctx (stmt as CFor0 (init_part, cond_opt, step_opt, body, _)) =
        let
          fun translate_general_for () =
            let
              fun cond_term_of tctx' =
                    (case cond_opt of
                       Some c => ensure_bool_cond tctx' c
                     | None => C_Term_Build.mk_literal
                                 (Isa_Const (\<^const_name>\<open>HOL.True\<close>, @{typ bool})))
              fun step_term_of tctx' =
                    (case step_opt of
                       Some s => C_Term_Build.mk_sequence (expr_term tctx' s) C_Term_Build.mk_literal_unit
                     | None => C_Term_Build.mk_literal_unit)
              fun expr_writes_name name (CAssign0 (_, CVar0 (ident, _), rhs, _)) =
                    C_Ast_Utils.ident_name ident = name orelse expr_writes_name name rhs
                | expr_writes_name name (CAssign0 (_, lhs, rhs, _)) =
                    expr_writes_name name lhs orelse expr_writes_name name rhs
                | expr_writes_name name (CUnary0 (CPreIncOp0, CVar0 (ident, _), _)) =
                    C_Ast_Utils.ident_name ident = name
                | expr_writes_name name (CUnary0 (CPostIncOp0, CVar0 (ident, _), _)) =
                    C_Ast_Utils.ident_name ident = name
                | expr_writes_name name (CUnary0 (CPreDecOp0, CVar0 (ident, _), _)) =
                    C_Ast_Utils.ident_name ident = name
                | expr_writes_name name (CUnary0 (CPostDecOp0, CVar0 (ident, _), _)) =
                    C_Ast_Utils.ident_name ident = name
                | expr_writes_name name (CBinary0 (_, l, r, _)) =
                    expr_writes_name name l orelse expr_writes_name name r
                | expr_writes_name name (CUnary0 (_, e, _)) =
                    expr_writes_name name e
                | expr_writes_name name (CIndex0 (a, i, _)) =
                    expr_writes_name name a orelse expr_writes_name name i
                | expr_writes_name name (CMember0 (e, _, _, _)) =
                    expr_writes_name name e
                | expr_writes_name name (CCast0 (_, e, _)) =
                    expr_writes_name name e
                | expr_writes_name name (CCall0 (f, args, _)) =
                    expr_writes_name name f orelse List.exists (expr_writes_name name) args
                | expr_writes_name name (CComma0 (es, _)) =
                    List.exists (expr_writes_name name) es
                | expr_writes_name name (CCond0 (c, t, e, _)) =
                    expr_writes_name name c orelse
                    (case t of Some te => expr_writes_name name te | None => false) orelse
                    expr_writes_name name e
                | expr_writes_name _ _ = false
              fun loop_var_written_in_step name =
                    (case step_opt of
                       Some s => expr_writes_name name s
                     | None => false)
              fun loop_var_needs_mutable_storage name =
                    loop_var_written_in_step name orelse
                    List.exists (fn n => n = name) (C_Ast_Utils.find_assigned_vars body)
              fun build_while tctx' =
                let val has_brk = contains_break body
                    val has_cont = contains_continue body
                    val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
                in if not has_brk andalso not has_cont then
                     let val cond_term = cond_term_of tctx'
                         val body_term =
                           C_Term_Build.mk_sequence (translate_stmt tctx' body) (step_term_of tctx')
                         val fuel_var = fresh_var [cond_term, body_term] "while_fuel" @{typ nat}
                     in C_Term_Build.mk_bounded_while fuel_var cond_term body_term end
                   else
                     let
                       val dummy_tctx = (if has_brk
                         then C_Trans_Ctxt.set_break_ref (Isa_Free ("__dummy_brk", isa_dummyT)) tctx'
                         else tctx')
                       val dummy_tctx = (if has_cont
                         then C_Trans_Ctxt.set_continue_ref (Isa_Free ("__dummy_cont", isa_dummyT)) dummy_tctx
                         else dummy_tctx)
                       val cond_raw = cond_term_of dummy_tctx
                       val body_raw = translate_stmt dummy_tctx body
                       val step_raw = step_term_of dummy_tctx
                        val flag_ref_ty = mk_flag_ref_type tctx'
                        val break_ref = if has_brk
                          then SOME (fresh_var [cond_raw, body_raw, step_raw] "v__for_break" flag_ref_ty)
                          else NONE
                        val continue_ref = if has_cont
                          then SOME (fresh_var [cond_raw, body_raw, step_raw] "v__for_cont" flag_ref_ty)
                          else NONE
                       val tctx_loop = case break_ref of
                           SOME b => C_Trans_Ctxt.set_break_ref b tctx'
                         | NONE => tctx'
                       val tctx_loop = case continue_ref of
                           SOME c => C_Trans_Ctxt.set_continue_ref c tctx_loop
                         | NONE => tctx_loop
                       val body_term = translate_stmt tctx_loop body
                       val step_term = step_term_of tctx_loop
                       val step_term =
                         (case break_ref of
                            SOME br =>
                              let val bf = Isa_Free ("v__for_bf", isa_dummyT)
                                  val bf_nonzero =
                                    Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                                    $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                                       $ bf
                                       $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                              in C_Term_Build.mk_bind
                                   (mk_resolved_var_read (C_Trans_Ctxt.get_ctxt tctx_loop) br)
                                   (Term.lambda bf
                                     (C_Term_Build.mk_two_armed_cond
                                       (C_Term_Build.mk_literal bf_nonzero)
                                       C_Term_Build.mk_literal_unit
                                       step_term))
                              end
                          | NONE => step_term)
                       val cond_term = cond_term_of tctx_loop
                       val cond_term =
                         (case break_ref of
                            SOME br =>
                              let val bf = Isa_Free ("v__for_bfc", isa_dummyT)
                                  val bf_nonzero =
                                    Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                                    $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                                       $ bf
                                       $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                              in C_Term_Build.mk_bind
                                   (mk_resolved_var_read (C_Trans_Ctxt.get_ctxt tctx_loop) br)
                                   (Term.lambda bf
                                     (C_Term_Build.mk_two_armed_cond
                                       (C_Term_Build.mk_literal bf_nonzero)
                                       (C_Term_Build.mk_literal
                                         (Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool})))
                                       cond_term))
                              end
                          | NONE => cond_term)
                       val body_with_resets =
                         (case continue_ref of
                            SOME cr =>
                              C_Term_Build.mk_sequence
                                (C_Term_Build.mk_var_write cr false_lit)
                                (C_Term_Build.mk_sequence body_term step_term)
                          | NONE => C_Term_Build.mk_sequence body_term step_term)
                       val fuel_var = fresh_var [cond_term, body_with_resets] "while_fuel" @{typ nat}
                       val loop_term = C_Term_Build.mk_bounded_while fuel_var cond_term body_with_resets
                       fun wrap_ref NONE t = t
                         | wrap_ref (SOME ref_var) t =
                             C_Term_Build.mk_bind
                               (mk_resolved_var_alloc (C_Trans_Ctxt.get_ctxt tctx') false_lit)
                               (Term.lambda ref_var t)
                     in wrap_ref break_ref (wrap_ref continue_ref loop_term) end
                end
            in
              case init_part of
                Left init_expr_opt =>
                  (case init_expr_opt of
                     Some (assign_expr as CAssign0 (CAssignOp0, CVar0 (ident, _), rhs, _)) =>
                       let
                         val name = C_Ast_Utils.ident_name ident
                       in case C_Trans_Ctxt.lookup_var tctx name of
                            SOME (kind0, _, cty) =>
                              if C_Ast_Utils.is_ptr cty andalso
                                 (case kind0 of
                                    C_Trans_Ctxt.Param => true
                                  | C_Trans_Ctxt.ParamListPtr => true
                                  | _ => false)
                              then
                                let
                                  val (rhs_term, rhs_cty) = translate_expr tctx rhs
                                  val mutable_ptr = loop_var_needs_mutable_storage name
                                  val rhs_list_backed = expr_is_list_backed_array tctx rhs
                                  val init_term =
                                    if mutable_ptr then
                                      let
                                        val rhs_cast = mk_implicit_cast (rhs_term, rhs_cty, cty)
                                      in
                                        if supports_raw_ptr_local_refs (C_Trans_Ctxt.get_ctxt tctx)
                                        then
                                          let
                                            val rhs_raw =
                                              mk_implicit_cast (rhs_cast, cty, C_Ast_Utils.CPtr C_Ast_Utils.CVoid)
                                            val alloc_expr =
                                              mk_resolved_var_alloc_typed
                                                (C_Trans_Ctxt.get_ctxt tctx)
                                                (raw_ptr_local_gref_typ ()) rhs_raw
                                            val var = mk_typed_ref_var tctx name alloc_expr
                                            val tctx' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.LocalPtr var cty tctx
                                            val tctx' = (case struct_name_of_cty cty of
                                                           SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx'
                                                         | NONE => tctx')
                                          in
                                            C_Term_Build.mk_bind alloc_expr
                                              (Term.lambda var (build_while tctx'))
                                          end
                                        else
                                          let
                                            val val_type =
                                              let val ty = expr_value_type rhs_cast
                                              in if ty = isa_dummyT then expr_value_type rhs_term else ty end
                                            val alloc_expr =
                                              mk_resolved_var_alloc_typed
                                                (C_Trans_Ctxt.get_ctxt tctx) val_type rhs_cast
                                            val var = mk_typed_ref_var tctx name alloc_expr
                                            val tctx' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.Local var cty tctx
                                            val tctx' = (case struct_name_of_cty cty of
                                                           SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx'
                                                         | NONE => tctx')
                                          in
                                            C_Term_Build.mk_bind alloc_expr
                                              (Term.lambda var (build_while tctx'))
                                          end
                                      end
                                    else
                                      let
                                        val var = Isa_Free (name, pointer_alias_var_ty tctx rhs_list_backed cty rhs_term)
                                        val kind = pointer_alias_kind rhs_list_backed
                                        val tctx' = C_Trans_Ctxt.add_var name kind var cty tctx
                                      in
                                        C_Term_Build.mk_bind rhs_term
                                          (Term.lambda var (build_while tctx'))
                                      end
                                in
                                  init_term
                                end
                              else
                                let
                                  val init_term = expr_term tctx assign_expr
                                in
                                  C_Term_Build.mk_sequence init_term (build_while tctx)
                                end
                          | _ =>
                              let
                                val init_term = expr_term tctx assign_expr
                              in
                                C_Term_Build.mk_sequence init_term (build_while tctx)
                              end
                       end
                   | Some e =>
                       let val init_term = expr_term tctx e
                       in C_Term_Build.mk_sequence init_term (build_while tctx) end
                   | None => build_while tctx)
              | Right init_decl =>
                  let val decls = translate_decl tctx init_decl
                      fun fold_decls [] tctx' = build_while tctx'
                        | fold_decls ((name, init, cty, arr_meta, alias_list_backed) :: ds) tctx' =
                            if C_Ast_Utils.is_ptr cty andalso not (Option.isSome arr_meta) then
                              if supports_raw_ptr_local_refs (C_Trans_Ctxt.get_ctxt tctx') andalso
                                 not (prefer_pointer_alias_storage alias_list_backed init) then
                                let
                                  val raw_ptr_ty = raw_ptr_local_gref_typ ()
                                  val stored_init =
                                    if is_uninitialized_literal init then init
                                    else mk_implicit_cast (init, cty, C_Ast_Utils.CPtr C_Ast_Utils.CVoid)
                                  val alloc_expr =
                                    mk_resolved_var_alloc_typed (C_Trans_Ctxt.get_ctxt tctx') raw_ptr_ty stored_init
                                  val var = mk_typed_ref_var tctx' name alloc_expr
                                  val tctx'' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.LocalPtr var cty tctx'
                                  val tctx'' = (case struct_name_of_cty cty of
                                                  SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx''
                                                | NONE => tctx'')
                                  val tctx'' = (case arr_meta of
                                                  SOME (elem_cty, n) => C_Trans_Ctxt.set_array_decl name elem_cty n tctx''
                                                | NONE => tctx'')
                                in C_Term_Build.mk_bind alloc_expr
                                     (Term.lambda var (fold_decls ds tctx'')) end
                              else
                                let
                                  val var = Isa_Free (name, pointer_alias_var_ty tctx' alias_list_backed cty init)
                                  val kind = pointer_alias_kind alias_list_backed
                                  val tctx'' = C_Trans_Ctxt.add_var name kind var cty tctx'
                                  val tctx'' = (case struct_name_of_cty cty of
                                                  SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx''
                                                | NONE => tctx'')
                                  val tctx'' = (case arr_meta of
                                                  SOME (elem_cty, n) => C_Trans_Ctxt.set_array_decl name elem_cty n tctx''
                                                | NONE => tctx'')
                                in if is_uninitialized_literal init then
                                     fold_decls ds tctx''
                                   else
                                     C_Term_Build.mk_bind init
                                       (Term.lambda var (fold_decls ds tctx''))
                                end
                            else
                              let val val_type =
                                    let val ty = C_Ast_Utils.hol_type_of cty
                                    in if ty = isa_dummyT then expr_value_type init else ty end
                                  val alloc_expr =
                                    mk_resolved_var_alloc_typed (C_Trans_Ctxt.get_ctxt tctx') val_type init
                                  val var = mk_typed_ref_var tctx' name alloc_expr
                                  val tctx'' = C_Trans_Ctxt.add_var name C_Trans_Ctxt.Local var cty tctx'
                                  val tctx'' = (case struct_name_of_cty cty of
                                                  SOME sn => C_Trans_Ctxt.set_struct_type name sn tctx''
                                                | NONE => tctx'')
                                  val tctx'' = (case arr_meta of
                                                  SOME (elem_cty, n) => C_Trans_Ctxt.set_array_decl name elem_cty n tctx''
                                                | NONE => tctx'')
                              in C_Term_Build.mk_bind alloc_expr
                                   (Term.lambda var (fold_decls ds tctx'')) end
                  in fold_decls decls tctx end
            end
        in
          case try_bounded_for stmt of
            SOME (var_name, init_c_expr, bound_c_expr, body) =>
              let
                val body_assigned = C_Ast_Utils.find_assigned_vars body
                val loop_var_mutated_or_escaped =
                  List.exists (fn n => n = var_name) body_assigned
              in
              if contains_break body orelse contains_continue body orelse loop_var_mutated_or_escaped then
                translate_general_for ()
              else
                (case (try_translate_pure_nat_expr tctx init_c_expr,
                       try_translate_pure_nat_expr tctx bound_c_expr) of
                   (SOME start_nat, SOME bound_nat) =>
                     let
                       val loop_cty =
                         (case stmt of
                            CFor0 (Right (CDecl0 (specs, [((Some declr, _), _)], _)), _, _, _, _) =>
                              let
                                val base_cty =
                                  (case C_Ast_Utils.resolve_c_type_full
                                          (C_Trans_Ctxt.get_typedef_tab tctx) specs of
                                     SOME C_Ast_Utils.CVoid => C_Ast_Utils.CInt
                                   | SOME t => t
                                   | NONE => C_Ast_Utils.CInt)
                              in
                                C_Ast_Utils.apply_ptr_depth base_cty
                                  (C_Ast_Utils.pointer_depth_of_declr declr)
                              end
                          | _ => C_Ast_Utils.CInt)
                     in
                       if C_Ast_Utils.is_signed loop_cty orelse
                          C_Ast_Utils.is_bool loop_cty orelse
                          C_Ast_Utils.is_ptr loop_cty then
                         translate_general_for ()
                       else
                         let
                           val loop_hol_ty = C_Ast_Utils.hol_type_of loop_cty
                           val loop_var = Isa_Free (var_name, loop_hol_ty)
                           val tctx' =
                             C_Trans_Ctxt.add_var var_name C_Trans_Ctxt.Param loop_var loop_cty tctx
                           val body_term = translate_stmt tctx' body
                           val range = C_Term_Build.mk_upt_int_range start_nat bound_nat
                         in
                           C_Term_Build.mk_raw_for_loop range (Term.lambda loop_var body_term)
                         end
                     end
                 | _ => translate_general_for ())
              end
          | NONE => translate_general_for ()
        end
    | translate_stmt tctx (CWhile0 (cond, body_stmt, is_do_while, _)) =
        let val has_brk = contains_break body_stmt
            val has_cont = contains_continue body_stmt
            val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
        in if not has_brk andalso not has_cont then
             (* Simple case: no break/continue *)
             let val cond_term = ensure_bool_cond tctx cond
                 val body_term = translate_stmt tctx body_stmt
                 val fuel_var = fresh_var [cond_term, body_term] "while_fuel" @{typ nat}
                 val while_term = C_Term_Build.mk_bounded_while fuel_var cond_term body_term
             in if is_do_while
                then C_Term_Build.mk_sequence body_term while_term
                else while_term
             end
           else
             (* Allocate break/continue flag refs *)
             let (* Pre-set dummy refs so first-pass translation doesn't warn *)
                val flag_ref_ty = mk_flag_ref_type tctx
                val dummy_tctx = (if has_brk
                  then C_Trans_Ctxt.set_break_ref (Isa_Free ("__dummy_brk", flag_ref_ty)) tctx
                  else tctx)
                val dummy_tctx = (if has_cont
                  then C_Trans_Ctxt.set_continue_ref (Isa_Free ("__dummy_cont", flag_ref_ty)) dummy_tctx
                  else dummy_tctx)
                 val cond_term_raw = ensure_bool_cond dummy_tctx cond
                 val body_raw = translate_stmt dummy_tctx body_stmt
                val break_ref = if has_brk
                  then SOME (fresh_var [cond_term_raw, body_raw] "v__break" flag_ref_ty)
                  else NONE
                val continue_ref = if has_cont
                  then SOME (fresh_var [cond_term_raw, body_raw] "v__cont" flag_ref_ty)
                  else NONE
                 (* Update context *)
                 val tctx' = case break_ref of
                     SOME b => C_Trans_Ctxt.set_break_ref b tctx | NONE => tctx
                 val tctx' = case continue_ref of
                     SOME c => C_Trans_Ctxt.set_continue_ref c tctx' | NONE => tctx'
                 (* Re-translate body with updated context (guards will be inserted) *)
                 val body_term = translate_stmt tctx' body_stmt
                 val cond_term = ensure_bool_cond tctx' cond
                 (* Augment condition: if break_flag then False else original_cond *)
                 val augmented_cond = case break_ref of
                     SOME br =>
                       let val bf = Isa_Free ("v__bf", isa_dummyT)
                           val bf_nonzero =
                             Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                             $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                                $ bf
                                $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                       in C_Term_Build.mk_bind (C_Term_Build.mk_var_read br)
                            (Term.lambda bf
                              (C_Term_Build.mk_two_armed_cond
                                (C_Term_Build.mk_literal bf_nonzero)
                                (C_Term_Build.mk_literal
                                  (Isa_Const (\<^const_name>\<open>HOL.False\<close>, @{typ bool})))
                                cond_term))
                       end
                   | NONE => cond_term
                 (* For continue: reset flag at start of each iteration *)
                 val body_with_resets = case continue_ref of
                     SOME cr =>
                       C_Term_Build.mk_sequence
                         (C_Term_Build.mk_var_write cr false_lit) body_term
                   | NONE => body_term
                 val fuel_var = fresh_var [augmented_cond, body_with_resets]
                                  "while_fuel" @{typ nat}
                 val while_term = C_Term_Build.mk_bounded_while
                                    fuel_var augmented_cond body_with_resets
                 val loop_term = if is_do_while
                   then C_Term_Build.mk_sequence body_with_resets while_term
                   else while_term
                 (* Wrap in Ref::new for break/continue refs *)
                 fun wrap_ref NONE t = t
                   | wrap_ref (SOME ref_var) t =
                       C_Term_Build.mk_bind
                         (mk_resolved_var_alloc (C_Trans_Ctxt.get_ctxt tctx) false_lit)
                         (Term.lambda ref_var t)
             in wrap_ref break_ref (wrap_ref continue_ref loop_term) end
        end
    | translate_stmt tctx (CSwitch0 (switch_expr, body, _)) =
        let val (switch_term_raw, switch_cty_raw) = translate_expr tctx switch_expr
            val switch_cty = C_Ast_Utils.integer_promote switch_cty_raw
            val switch_term = mk_implicit_cast (switch_term_raw, switch_cty_raw, switch_cty)
            val switch_var = fresh_var [switch_term] "v__switch" isa_dummyT
            val items = case body of
                          CCompound0 (_, items, _) => items
                        | _ => [CBlockStmt0 body]
            val groups = extract_switch_groups items
            val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
            val true_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 1
            val flag_ref_ty = mk_flag_ref_type tctx
            val switch_break_ref = fresh_var [switch_term] "v__switch_break" flag_ref_ty
            (* break inside switch exits this switch, not any enclosing loop *)
            val tctx_sw = C_Trans_Ctxt.set_break_ref switch_break_ref
                            (C_Trans_Ctxt.clear_break_ref tctx)
            val all_have_break = List.all #has_break groups
                                 orelse List.length groups <= 1
            val any_case_match = make_any_case_match switch_var switch_cty tctx groups
            val default_cond = Isa_Const (\<^const_name>\<open>HOL.Not\<close>, @{typ bool} --> @{typ bool}) $ any_case_match
            val brk = Isa_Free ("v__sw_break", isa_dummyT)
            val break_nonzero =
              Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
              $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                 $ brk
                 $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
            fun guard_break inner =
              C_Term_Build.mk_bind
                (mk_resolved_var_read (C_Trans_Ctxt.get_ctxt tctx_sw) switch_break_ref)
                (Term.lambda brk
                  (C_Term_Build.mk_two_armed_cond
                    (C_Term_Build.mk_literal break_nonzero)
                    C_Term_Build.mk_literal_unit
                    inner))
        in C_Term_Build.mk_bind
             (mk_resolved_var_alloc (C_Trans_Ctxt.get_ctxt tctx) false_lit)
             (Term.lambda switch_break_ref
               (if all_have_break then
                  (* Simple if-else chain: no fall-through *)
                  let fun build_chain [] = C_Term_Build.mk_literal_unit
                        | build_chain ({labels, body, ...} :: rest) =
                            let val body_term = translate_compound_items tctx_sw body
                                val rest_term = build_chain rest
                                val cond = C_Term_Build.mk_literal
                                             (make_switch_cond switch_var switch_cty tctx default_cond labels)
                            in C_Term_Build.mk_two_armed_cond cond body_term rest_term end
                  in C_Term_Build.mk_bind switch_term
                       (Term.lambda switch_var (build_chain groups))
                  end
                else
                  (* Fall-through: use matched_ref *)
                  let val matched_ref = fresh_var [switch_term] "v__matched" flag_ref_ty
                      val matched_var = Isa_Free ("v__m", isa_dummyT)
                      val matched_nonzero =
                        Isa_Const (\<^const_name>\<open>HOL.Not\<close>, isa_dummyT)
                        $ (Isa_Const (\<^const_name>\<open>HOL.eq\<close>, isa_dummyT)
                           $ matched_var
                           $ Isa_Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, isa_dummyT))
                      fun build_groups [] = C_Term_Build.mk_literal_unit
                        | build_groups ({labels, body, has_break} :: rest) =
                            let val body_term = translate_compound_items tctx_sw body
                                val label_cond =
                                  make_switch_cond switch_var switch_cty tctx default_cond labels
                                val full_cond =
                                  Isa_Const (\<^const_name>\<open>HOL.disj\<close>,
                                    @{typ bool} --> @{typ bool} --> @{typ bool})
                                  $ matched_nonzero $ label_cond
                                val group_action =
                                  C_Term_Build.mk_sequence body_term
                                    (if has_break
                                     then C_Term_Build.mk_var_write matched_ref false_lit
                                     else C_Term_Build.mk_var_write matched_ref true_lit)
                                val group_term =
                                  C_Term_Build.mk_bind (C_Term_Build.mk_var_read matched_ref)
                                    (Term.lambda matched_var
                                      (C_Term_Build.mk_two_armed_cond
                                        (C_Term_Build.mk_literal full_cond)
                                        group_action C_Term_Build.mk_literal_unit))
                            in guard_break (C_Term_Build.mk_sequence group_term (build_groups rest)) end
                  in C_Term_Build.mk_bind switch_term
                       (Term.lambda switch_var
                         (C_Term_Build.mk_bind
                         (mk_resolved_var_alloc (C_Trans_Ctxt.get_ctxt tctx) false_lit)
                         (Term.lambda matched_ref (build_groups groups))))
                  end))
        end
    | translate_stmt tctx (CGoto0 (ident, _)) =
        let val name = C_Ast_Utils.ident_name ident
            val is_forward_target =
              List.exists (fn n => n = name) (C_Trans_Ctxt.get_active_goto_labels tctx)
        in case C_Trans_Ctxt.lookup_goto_ref tctx name of
             SOME goto_ref =>
               if is_forward_target then
                 C_Term_Build.mk_var_write goto_ref
                   (C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 1)
               else
                 unsupported ("non-forward goto not supported: " ^ name)
           | NONE => unsupported ("goto target not found: " ^ name)
        end
    | translate_stmt tctx (CLabel0 (_, stmt, _, _)) =
        (* Labels as standalone statements (not in compound block context):
           just translate the labeled statement. The label flag reset is handled
           by translate_compound_items when the label appears in a block. *)
        translate_stmt tctx stmt
    | translate_stmt tctx (CCont0 _) =
        (case C_Trans_Ctxt.get_continue_ref tctx of
           SOME cont_ref =>
             C_Term_Build.mk_var_write cont_ref
               (C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 1)
         | NONE => unsupported "continue outside loop")
    | translate_stmt tctx (CBreak0 _) =
        (case C_Trans_Ctxt.get_break_ref tctx of
           SOME break_ref =>
             C_Term_Build.mk_var_write break_ref
               (C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 1)
         | NONE => unsupported "break outside loop/switch")
    | translate_stmt _ _ =
        unsupported "statement"

  local
    fun expr_writes_in_loop (CAssign0 (_, CVar0 (ident, _), rhs, _)) acc =
          expr_writes_in_loop rhs (C_Ast_Utils.ident_name ident :: acc)
      | expr_writes_in_loop (CAssign0 (_, lhs, rhs, _)) acc =
          expr_writes_in_loop rhs (expr_writes_in_loop lhs acc)
      | expr_writes_in_loop (CUnary0 (CPreIncOp0, CVar0 (ident, _), _)) acc =
          C_Ast_Utils.ident_name ident :: acc
      | expr_writes_in_loop (CUnary0 (CPostIncOp0, CVar0 (ident, _), _)) acc =
          C_Ast_Utils.ident_name ident :: acc
      | expr_writes_in_loop (CUnary0 (CPreDecOp0, CVar0 (ident, _), _)) acc =
          C_Ast_Utils.ident_name ident :: acc
      | expr_writes_in_loop (CUnary0 (CPostDecOp0, CVar0 (ident, _), _)) acc =
          C_Ast_Utils.ident_name ident :: acc
      | expr_writes_in_loop (CBinary0 (_, l, r, _)) acc =
          expr_writes_in_loop r (expr_writes_in_loop l acc)
      | expr_writes_in_loop (CUnary0 (_, e, _)) acc = expr_writes_in_loop e acc
      | expr_writes_in_loop (CIndex0 (a, i, _)) acc =
          expr_writes_in_loop i (expr_writes_in_loop a acc)
      | expr_writes_in_loop (CMember0 (e, _, _, _)) acc = expr_writes_in_loop e acc
      | expr_writes_in_loop (CCast0 (_, e, _)) acc = expr_writes_in_loop e acc
      | expr_writes_in_loop (CCall0 (f, args, _)) acc =
          List.foldl (fn (a, ac) => expr_writes_in_loop a ac) (expr_writes_in_loop f acc) args
      | expr_writes_in_loop (CComma0 (es, _)) acc =
          List.foldl (fn (e, ac) => expr_writes_in_loop e ac) acc es
      | expr_writes_in_loop (CCond0 (c, t, e, _)) acc =
          expr_writes_in_loop e
            ((case t of Some te => expr_writes_in_loop te | None => I)
              (expr_writes_in_loop c acc))
      | expr_writes_in_loop _ acc = acc

    fun loop_decl_writes (CDecl0 (_, declarators, _)) acc =
          List.foldl
            (fn (((_, Some (CInitExpr0 (e, _))), _), ac) => expr_writes_in_loop e ac
              | (((_, Some (CInitList0 (inits, _))), _), ac) =>
                  List.foldl (fn ((_, init), ac') =>
                      (case init of
                         CInitExpr0 (e, _) => expr_writes_in_loop e ac'
                       | CInitList0 _ => ac'))
                    ac inits
              | (_, ac) => ac)
            acc declarators
      | loop_decl_writes _ acc = acc

    fun loop_item_writes (CBlockStmt0 s) acc = loop_stmt_writes s acc
      | loop_item_writes (CBlockDecl0 d) acc = loop_decl_writes d acc
      | loop_item_writes _ acc = acc

    and loop_stmt_writes (CCompound0 (_, items, _)) acc =
          List.foldl (fn (it, ac) => loop_item_writes it ac) acc items
      | loop_stmt_writes (CExpr0 (Some e, _)) acc = expr_writes_in_loop e acc
      | loop_stmt_writes (CReturn0 (Some e, _)) acc = expr_writes_in_loop e acc
      | loop_stmt_writes (CIf0 (c, t, e_opt, _)) acc =
          let
            val acc = expr_writes_in_loop c acc
            val acc = loop_stmt_writes t acc
          in case e_opt of Some e => loop_stmt_writes e acc | None => acc end
      | loop_stmt_writes (CWhile0 (c, b, _, _)) acc =
          loop_stmt_writes b (expr_writes_in_loop c acc)
      | loop_stmt_writes (CFor0 (init, c, s, b, _)) acc =
          let
            val acc =
              (case init of
                 Left (Some e) => expr_writes_in_loop e acc
               | Right d => loop_decl_writes d acc
               | _ => acc)
            val acc = (case c of Some e => expr_writes_in_loop e acc | None => acc)
            val acc = (case s of Some e => expr_writes_in_loop e acc | None => acc)
          in loop_stmt_writes b acc end
      | loop_stmt_writes (CSwitch0 (e, s, _)) acc =
          loop_stmt_writes s (expr_writes_in_loop e acc)
      | loop_stmt_writes (CCase0 (e, s, _)) acc =
          loop_stmt_writes s (expr_writes_in_loop e acc)
      | loop_stmt_writes (CDefault0 (s, _)) acc = loop_stmt_writes s acc
      | loop_stmt_writes (CLabel0 (_, s, _, _)) acc = loop_stmt_writes s acc
      | loop_stmt_writes _ acc = acc
  in
    fun find_loop_written_vars_local stmt = distinct (op =) (loop_stmt_writes stmt [])
  end

  fun translate_fundef struct_tab enum_tab typedef_tab func_ret_types func_param_types global_consts ctxt
      (CFunDef0 (specs, declr, _, body, _)) =
    let
      val _ = current_visible_ctxt := SOME ctxt
      val name = C_Ast_Utils.declr_name declr
      val _ =
        if C_Ast_Utils.declr_is_variadic declr then
          unsupported ("variadic functions are not supported: " ^ name)
        else ()
      (* Register the function's return type for cross-function call type tracking *)
      val ret_base_cty = (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                            SOME C_Ast_Utils.CVoid => C_Ast_Utils.CVoid
                          | SOME t => t | NONE => C_Ast_Utils.CInt)
      val ret_cty = C_Ast_Utils.apply_ptr_depth ret_base_cty
                      (C_Ast_Utils.pointer_depth_of_declr declr)
      val _ = func_ret_types := Symtab.update (name, ret_cty) (! func_ret_types)
      val param_names = C_Ast_Utils.extract_params declr
      val param_decls = C_Ast_Utils.extract_param_decls declr
      val struct_names = Symtab.keys struct_tab
      val union_names = !current_union_names
      (* Extract parameter types and pointer-ness from declarations.
         Use resolve_c_type_full so that typedef'd types (e.g. uint32) resolve
         correctly to their underlying C type for signed/unsigned dispatch. *)
      val param_info = List.map (fn pdecl =>
        let
            val cty = case pdecl of
                        CDecl0 (specs, _, _) =>
                          (case C_Ast_Utils.resolve_c_type_full typedef_tab specs of
                             SOME t => t
                           | NONE =>
                               (case C_Ast_Utils.extract_struct_type_from_decl_full struct_names pdecl of
                                  SOME sn => C_Ast_Utils.CStruct sn
                                | NONE =>
                                    (case C_Ast_Utils.extract_union_type_from_decl_full union_names pdecl of
                                       SOME un => C_Ast_Utils.CUnion un
                                     | NONE => C_Ast_Utils.CInt)))
                      | _ => C_Ast_Utils.CInt
            val ptr_depth = C_Ast_Utils.pointer_depth_of_decl pdecl
            val reg_cty = C_Ast_Utils.apply_ptr_depth cty ptr_depth
        in reg_cty end) param_decls
      (* Pair names with type info; fall back to (CInt, false) if lengths differ *)
      val param_name_info = ListPair.zipEq (param_names, param_info)
        handle ListPair.UnequalLengths =>
          List.map (fn n => (n, C_Ast_Utils.CInt)) param_names
      val param_list_backed_modes =
        (case Symtab.lookup (!current_list_backed_param_modes) name of
           SOME modes =>
             if List.length modes = List.length param_name_info then modes
             else List.map (K false) param_name_info
         | NONE => List.map (K false) param_name_info)
      (* Create free variables for each parameter.
         List-backed decay parameters must stay concretely list-backed so helper
         extraction keeps working; other pointers remain inference-driven except
         raw void/union pointers, which need a stable representation. *)
      fun param_value_hol_ty list_backed cty =
        if list_backed then
          (case list_backed_pointer_value_hol_ty cty of
             SOME ty => ty
           | NONE => isa_dummyT)
        else
          (case cty of
             C_Ast_Utils.CPtr C_Ast_Utils.CVoid =>
               (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) cty of
                  SOME ty => ty
                | NONE => isa_dummyT)
           | C_Ast_Utils.CPtr (C_Ast_Utils.CUnion _) =>
               (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) cty of
                  SOME ty => ty
                | NONE => isa_dummyT)
           | _ =>
               if C_Ast_Utils.is_ptr cty then isa_dummyT else C_Ast_Utils.hol_type_of cty)
      val param_vars =
        ListPair.mapEq (fn ((n, cty), list_backed) =>
          let val hol_ty = param_value_hol_ty list_backed cty
          in (n, Isa_Free (n, hol_ty), cty, list_backed) end)
          (param_name_info, param_list_backed_modes)
        handle ListPair.UnequalLengths =>
          List.map (fn (n, cty) =>
            let val hol_ty = param_value_hol_ty false cty
            in (n, Isa_Free (n, hol_ty), cty, false) end) param_name_info
      (* Add parameters to the translation context as Param/ParamListPtr. *)
      val tctx = List.foldl
        (fn ((n, v, cty, list_backed), ctx) =>
            C_Trans_Ctxt.add_var n
              (if list_backed then C_Trans_Ctxt.ParamListPtr else C_Trans_Ctxt.Param)
              v cty ctx)
        (C_Trans_Ctxt.make ctxt struct_tab enum_tab typedef_tab func_ret_types func_param_types
          (!current_ref_addr_ty) (!current_ref_gv_ty)) param_vars
      val tctx = List.foldl (fn ((gname, gterm, gcty, garr_meta, gstruct), ctx) =>
                    let
                      val ctx' = C_Trans_Ctxt.add_global_const gname gterm gcty ctx
                      val ctx' = (case gstruct of
                                    SOME sn => C_Trans_Ctxt.set_struct_type gname sn ctx'
                                  | NONE => ctx')
                      val ctx' = (case garr_meta of
                                    SOME (elem_cty, n) => C_Trans_Ctxt.set_array_decl gname elem_cty n ctx'
                                  | NONE => ctx')
                    in ctx' end)
                  tctx global_consts
      (* Annotate struct pointer parameters with their struct type.
         Uses _full variant to also recognize typedef'd struct names. *)
      val tctx = List.foldl (fn (pdecl, ctx) =>
        case (C_Ast_Utils.param_name pdecl,
              C_Ast_Utils.extract_struct_type_from_decl_full struct_names pdecl) of
          (SOME n, SOME sn) => C_Trans_Ctxt.set_struct_type n sn ctx
        | _ =>
            (case (C_Ast_Utils.param_name pdecl,
                   C_Ast_Utils.extract_union_type_from_decl_full union_names pdecl) of
               (SOME n, SOME un) => C_Trans_Ctxt.set_struct_type n un ctx
             | _ => ctx)) tctx param_decls
      (* Promote parameters that are assigned in the body to local variables.
         For each promoted parameter, wrap the body with Ref::new(literal param)
         and register the ref as a Local in the context (shadowing the Param). *)
      val assigned_names = C_Ast_Utils.find_assigned_vars body
      val _ = current_loop_written_vars := find_loop_written_vars_local body
      val promoted_params = List.filter (fn (n, _, _, _) =>
        List.exists (fn a => a = n) assigned_names) param_vars
      val (tctx, promoted_bindings) = List.foldl
        (fn ((n, orig_var, cty, list_backed), (ctx, binds)) =>
          let
              val use_raw_ptr =
                C_Ast_Utils.is_ptr cty andalso
                supports_raw_ptr_local_refs (C_Trans_Ctxt.get_ctxt ctx) andalso
                not list_backed
              val (kind, alloc_expr) =
                if use_raw_ptr then
                  (C_Trans_Ctxt.LocalPtr,
                   mk_resolved_var_alloc_typed (C_Trans_Ctxt.get_ctxt ctx) (raw_ptr_local_gref_typ ())
                     (mk_implicit_cast (C_Term_Build.mk_literal orig_var, cty, C_Ast_Utils.CPtr C_Ast_Utils.CVoid)))
                else
                  let
                    val val_type =
                      let val ty = fastype_of orig_var
                      in if ty = isa_dummyT then C_Ast_Utils.hol_type_of cty else ty end
                  in
                    (C_Trans_Ctxt.Local,
                     mk_resolved_var_alloc_typed (C_Trans_Ctxt.get_ctxt ctx) val_type
                       (C_Term_Build.mk_literal orig_var))
                  end
              val ref_var = mk_typed_ref_var ctx (n ^ "_ref") alloc_expr
              val ctx' = C_Trans_Ctxt.add_var n kind ref_var cty ctx
          in (ctx', binds @ [(ref_var, alloc_expr)]) end)
        (tctx, []) promoted_params
      (* Allocate goto flag references for forward-only goto support.
         Each label targeted by a goto gets a flag ref initialized to 0. *)
      val goto_labels = C_Ast_Utils.find_goto_targets body
      val goto_ref_ty = mk_flag_ref_type tctx
      val goto_refs = List.map (fn label_name =>
        (label_name, Isa_Free ("v__goto_" ^ label_name, goto_ref_ty))) goto_labels
      val tctx = C_Trans_Ctxt.set_goto_refs goto_refs tctx
      (* Set current return type for implicit narrowing in CReturn0 *)
      val _ = current_ret_cty := SOME ret_cty
      val body_term = translate_stmt tctx body
      (* Wrap body with Ref::new for each promoted parameter *)
      val body_term = List.foldr
        (fn ((ref_var, alloc_expr), b) =>
          C_Term_Build.mk_bind
            alloc_expr
            (Term.lambda ref_var b))
        body_term promoted_bindings
      (* Wrap body with Ref::new(0) for each goto flag ref *)
      val false_lit = C_Term_Build.mk_literal_num C_Ast_Utils.CUInt 0
      val body_term = List.foldr
        (fn ((_, ref_var), b) =>
          C_Term_Build.mk_bind
            (mk_resolved_var_alloc ctxt false_lit)
            (Term.lambda ref_var b))
        body_term goto_refs
      (* If an expression type constraint is set, constrain the body so that
         type inference resolves state/abort/prompt to the locale's types instead of
         leaving them as unconstrained variables that get fixated to rigid TFrees. *)
      val body_term =
        (case !current_ref_expr_constraint of
           NONE => body_term
         | SOME expr_ty => Type.constraint expr_ty body_term)
      val body_term =
        (case ret_cty of
           C_Ast_Utils.CVoid => constrain_known_expr_value_type @{typ unit} body_term
         | _ =>
             (case C_Ast_Utils.cty_to_record_typ (!current_decl_prefix) ret_cty of
                SOME ty => constrain_known_expr_value_type ty body_term
              | NONE => body_term))
      val fn_term = C_Term_Build.mk_function_body body_term
      (* Wrap in lambdas for each parameter *)
      val fn_term = List.foldr
        (fn ((_, v, _, _), t) => Term.lambda v t)
        fn_term param_vars
      (* Abstract while-loop fuel variables as additional parameters *)
      val fuel_frees = Isa_add_frees fn_term []
        |> List.filter (fn (n, _) => String.isPrefix "while_fuel" n)
        |> List.map (fn (n, ty) => Isa_Free (n, ty))
      val fuel_count = List.length fuel_frees
      val _ = if fuel_count > 0 then
                (defined_func_fuels :=
                   Symtab.update (!current_decl_prefix ^ name, fuel_count) (!defined_func_fuels);
                 writeln ("  fuel params: " ^ Int.toString fuel_count))
              else ()
      val fn_term = List.foldr (fn (v, t) => Term.lambda v t) fn_term fuel_frees
      fun mk_fun_ty (arg_ty, res_ty) = Isa_Type (\<^type_name>\<open>fun\<close>, [arg_ty, res_ty])
      val fn_term =
        let
          val all_arg_tys =
            List.map fastype_of fuel_frees @
            List.map (fn (_, v, _, _) => fastype_of v) param_vars
          val fn_sig_ty = List.foldr mk_fun_ty (fastype_of (C_Term_Build.mk_function_body body_term)) all_arg_tys
        in Type.constraint fn_sig_ty fn_term end
      val fn_term' = Syntax.check_term ctxt fn_term
    in
      (name, fn_term')
    end
end
\<close>

end
