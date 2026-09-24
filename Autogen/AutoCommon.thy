(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory AutoCommon
  imports Main
begin

ML\<open>
  \<comment>\<open>Trace level: The higher, the more verbose the logging gets\<close>
  val locality_trace_level = Attrib.setup_config_int @{binding "locality_trace_level"} (K 0)

  \<comment>\<open>Construct and log text at the given debug level only when tracing is enabled.
     Level zero disables tracing; positive levels retain the existing verbosity ordering.\<close>
  fun locality_pretty_trace ctxt lvl (pretty : unit -> Pretty.T) =
    let val trace_level = Config.get ctxt locality_trace_level in
      if 0 < trace_level andalso lvl <= trace_level
      then pretty () |> Pretty.string_of |> tracing
      else ()
    end

  \<comment>\<open>Authoritative invocation-context switch for AutoLocality cancellation simprocs.\<close>
  val locality_cancel_enabled =
    Attrib.setup_config_bool @{binding "locality_cancel_enabled"} (K true)

  \<comment>\<open>When set, the locality commands report how long each generated sub-proof takes. This is a
     diagnostic for spotting which phase (commutativity / disjointness / local-action) dominates,
     independent of the verbosity governed by \<^verbatim>\<open>locality_trace_level\<close>.\<close>
  val locality_timing = Attrib.setup_config_bool @{binding "locality_timing"} (K false)

  \<comment>\<open>Time a thunk and, if \<^verbatim>\<open>locality_timing\<close> is set, report the elapsed time under \<^verbatim>\<open>label\<close>.\<close>
  fun locality_time ctxt (label : string) (f : unit -> 'a) : 'a =
    if Config.get ctxt locality_timing then
      let
        val timer = Timing.start ()
        val result = f ()
        val _ = tracing ("[locality timing] " ^ label ^ ": " ^ Timing.message (Timing.result timer))
      in result end
    else f ()

  \<comment>\<open>As \<^verbatim>\<open>locality_time\<close>, but for a tactic. The tactic's result sequence is forced eagerly so the
     measurement captures the real proof-search cost rather than the (lazy) construction of the
     sequence. The generated goals are deterministic (at most one result), so forcing is safe.\<close>
  fun locality_time_tac ctxt (label : string) (tac : tactic) : tactic =
    if Config.get ctxt locality_timing then
      (fn st =>
        let
          val timer = Timing.start ()
          val results = Seq.list_of (tac st)
          val _ = tracing ("[locality timing] " ^ label ^ ": " ^ Timing.message (Timing.result timer))
        in Seq.of_list results end)
    else tac

  \<comment>\<open>Lookup named theorem list by name. If it does not exist, return \<^verbatim>\<open>NONE\<close>.
     If it does, return the fully qualified name.\<close>
  fun named_theorems_check_opt (name : string) ctxt =
    Named_Theorems.check ctxt (name, Position.none) |> SOME
    handle ERROR _ => NONE
  
  \<comment>\<open>Lookup named theorem list by name. If it does not exist, create it.
  Return the triple of (a) a boolean indicating whether named theorem list was freshly
  created, (b) fully qualified name, (c) potentially updated context.\<close>
  fun check_create_named_theorems (name : string) ctxt =
    case named_theorems_check_opt name ctxt of
       NONE =>
         let
           val (name', ctxt') = Named_Theorems.declare (Binding.make (name, Position.none)) "" ctxt
           val _ = locality_pretty_trace ctxt 1 (fn () =>
             Pretty.text "Created named theorem list:" @ [Pretty.brk 1, Pretty.str name]
             |> Pretty.block)
         in
           (true, name', ctxt')
         end
     | SOME name' => (false, name', ctxt)

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
\<close>

end
