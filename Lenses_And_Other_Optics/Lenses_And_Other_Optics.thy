(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Lenses_And_Other_Optics
  imports 
    "Prism" 
    "Lens" 
    "Focus"
    "Array_Optics"
    "List_Optics"
    "Result_Optics"
    "Vector_Optics"
    "Focused_Types"
begin

declare nth_optE[focus_elims]
declare nth_optI[focus_intros]

declare vector_nth_optE[focus_elims]
declare vector_nth_optI[focus_intros]

end
(*>*)
