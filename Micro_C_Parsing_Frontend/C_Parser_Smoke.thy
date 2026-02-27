theory C_Parser_Smoke
  imports
    "Isabelle_C.C_Main"
begin

section \<open>Isabelle/C Parser Smoke Tests\<close>

text \<open>Verify Isabelle/C parses representative C fragments.\<close>

C \<open>
int main(void) {
  return 0;
}
\<close>

C \<open>
void swap(int *a, int *b) {
  int t = *a;
  *a = *b;
  *b = t;
}
\<close>

end
