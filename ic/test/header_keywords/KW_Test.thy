theory KW_Test
  imports Main
  keywords "dummy_kw" :: thy_decl
begin

ML \<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>dummy_kw\<close> "a no-op command"
    (Scan.succeed (Toplevel.theory I))
\<close>

dummy_kw

definition kw_val where "kw_val = (42::nat)"

end
