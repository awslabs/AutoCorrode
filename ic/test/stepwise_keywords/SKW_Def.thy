theory SKW_Def
  imports Main
  keywords "skw_cmd" :: thy_decl
begin

ML \<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>skw_cmd\<close> "a no-op command"
    (Scan.succeed (Toplevel.theory I))
\<close>

skw_cmd

definition skw_val where "skw_val = (1::nat)"

end
