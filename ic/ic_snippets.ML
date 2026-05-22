(* I/C ML snippets — loaded into I/R at runtime via the TCP connection.
   These functions are callable from Isar ML commands stepped inside REPLs. *)

fun ic_parse_spans (thy : theory) (text : string) =
  let val trs = Outer_Syntax.parse_text thy (fn () => thy) Position.start text
  in List.app (fn tr =>
    case Position.offset_of (Toplevel.pos_of tr) of
      SOME off => writeln (string_of_int off)
    | NONE => ()) trs
  end;

val ic_mgmt_tab : string Symtab.table Synchronized.var
  = Synchronized.var "ic_mgmt_tab" Symtab.empty;

fun ic_symtab_set key value =
  Synchronized.change ic_mgmt_tab (Symtab.update (key, value));

fun ic_symtab_get key =
  case Symtab.lookup (Synchronized.value ic_mgmt_tab) key of
    SOME v => writeln v
  | NONE => ();

fun ic_symtab_get_all () =
  Symtab.fold (fn (k, v) => fn () =>
    writeln (k ^ "\t" ^ v)) (Synchronized.value ic_mgmt_tab) ();

fun ic_symtab_delete key =
  Synchronized.change ic_mgmt_tab (Symtab.delete_safe key);

fun ic_symtab_clear () =
  Synchronized.change ic_mgmt_tab (K Symtab.empty);
