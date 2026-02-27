theory C_Translation_Smoke_Core
  imports
    C_To_Core_Translation
begin

section \<open>Core Translation Smoke\<close>

micro_c_translate \<open>
void smoke_core_void(void) {
  return;
}
\<close>

thm c_smoke_core_void_def

micro_c_translate \<open>
int smoke_core_const(void) {
  return 42;
}
\<close>

thm c_smoke_core_const_def

micro_c_translate \<open>
void smoke_core_assign(void) {
  int x = 5;
  x = x + 1;
}
\<close>

thm c_smoke_core_assign_def

micro_c_translate \<open>
int smoke_core_if(int a, int b) {
  if (a > b) {
    return a;
  } else {
    return b;
  }
}
\<close>

thm c_smoke_core_if_def

micro_c_translate \<open>
int smoke_core_add(int a, int b) {
  return a + b;
}
\<close>

micro_c_translate \<open>
int smoke_core_add_three(int x, int y, int z) {
  return smoke_core_add(smoke_core_add(x, y), z);
}
\<close>

thm c_smoke_core_add_def c_smoke_core_add_three_def

micro_c_translate \<open>
unsigned int smoke_core_comma(unsigned int a, unsigned int b) {
  unsigned int x = (a, b);
  return x;
}
\<close>

thm c_smoke_core_comma_def

micro_c_translate \<open>
unsigned int smoke_core_multi_decl(unsigned int a, unsigned int b) {
  unsigned int x = a, y = b;
  return x;
}
\<close>

thm c_smoke_core_multi_decl_def

end
