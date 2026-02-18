(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(* Build hook that optionally stores all document segments in a global
   table, keyed by theory name. Controlled by the system option
   "store_segments". When enabled, segments survive into the heap image. *)

val stored_segments : (string * Document_Output.segment list) list Synchronized.var
  = Synchronized.var "stored_segments" [];

val _ = Build.add_hook (fn qualifier => fn loaded_theories =>
  if (Options.default_bool "store_segments" handle ERROR _ => false) then
    let val entries = map (fn (thy, segs) =>
            (Context.theory_long_name thy, segs)) loaded_theories
        val _ = List.app (fn (name, segs) =>
            writeln ("Segment_Storage: " ^ name ^ " (" ^
                     string_of_int (length segs) ^ " segments) [STORING]")) entries
    in Synchronized.change stored_segments (fn old => entries @ old)
    end
  else
    writeln ("Segment_Storage: store_segments=false, skipping " ^
             string_of_int (length loaded_theories) ^ " theories"));
