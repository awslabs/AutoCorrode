theory C_Translation_Smoke_Options
  imports
    C_To_Core_Translation
begin

section \<open>micro_c_translate Prefix Smoke\<close>

micro_c_translate prefix: smoke_ \<open>
  struct counter {
    unsigned int value;
  };

  unsigned int bump(struct counter *c) {
    c->value = c->value + 1;
    return c->value;
  }
\<close>

thm smoke_bump_def
thm smoke_counter.record_simps

section \<open>micro_c_file Prefix and Manifest Smoke\<close>

micro_c_file prefix: smoke_ manifest: "smoke_manifest.txt" "smoke_manifest_file.c"

thm smoke_keep_add_def
thm smoke_poly_get0_def
thm smoke_poly_t.record_simps

ML \<open>
  val _ =
    ((Proof_Context.read_const {proper = true, strict = true} @{context} "smoke_drop_mul"; error "manifest filtering failed")
      handle ERROR _ => ());
\<close>

section \<open>Two-Phase Type-Then-Function Smoke\<close>

micro_c_file prefix: smoke_split_ manifest: "smoke_manifest_types.txt" "smoke_manifest_file_types_phase1.c"

micro_c_file prefix: smoke_split_ addr: 'addr gv: 'gv
  manifest: "smoke_manifest_phase2.txt" "smoke_manifest_file_types_phase2.c"

thm smoke_split_poly_get0_def
thm smoke_split_poly_t.record_simps

end
