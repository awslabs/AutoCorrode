theory C_Translation_Smoke_Advanced
  imports
    C_To_Core_Translation
    "Shallow_Separation_Logic.Separation_Algebra"
begin

section \<open>Advanced Feature Translation Smoke\<close>

text \<open>Smoke tests for features not covered by the core/control/memory/types suites.\<close>

subsection \<open>String Literals\<close>

micro_c_translate addr: nat \<open>
void smoke_adv_string_init(void) {
  char s[] = "Hi";
  char c = s[0];
}
\<close>

thm c_smoke_adv_string_init_def

subsection \<open>Compound Literals\<close>

micro_c_translate \<open>
unsigned int smoke_adv_compound_lit(void) {
  unsigned int x = (unsigned int){42};
  return x;
}
\<close>

thm c_smoke_adv_compound_lit_def

subsection \<open>sizeof(expr)\<close>

micro_c_translate \<open>
typedef unsigned long size_t;
size_t smoke_adv_sizeof_int(void) {
  return sizeof(int);
}
\<close>

thm c_smoke_adv_sizeof_int_def

micro_c_translate \<open>
struct smoke_adv_pair {
  int x;
  int y;
};
typedef unsigned long smoke_adv_size_t;
smoke_adv_size_t smoke_adv_sizeof_struct(void) {
  return sizeof(struct smoke_adv_pair);
}
\<close>

thm c_smoke_adv_sizeof_struct_def

subsection \<open>Chained Struct-Array Access\<close>

micro_c_translate addr: nat \<open>
struct smoke_adv_vec {
  int data[4];
};
int smoke_adv_struct_arr_read(struct smoke_adv_vec *v, unsigned int i) {
  return v->data[i];
}
\<close>

thm c_smoke_adv_struct_arr_read_def

subsection \<open>_Generic Selection\<close>

micro_c_translate \<open>
unsigned int smoke_adv_generic(unsigned int x) {
  return _Generic(x, unsigned int: x + 1, int: (unsigned int)(x - 1));
}
\<close>

thm c_smoke_adv_generic_def

subsection \<open>_Alignof\<close>

micro_c_translate \<open>
typedef unsigned long smoke_adv_al_size_t;
smoke_adv_al_size_t smoke_adv_alignof_int(void) {
  return _Alignof(int);
}
\<close>

thm c_smoke_adv_alignof_int_def

subsection \<open>__builtin_offsetof\<close>

micro_c_translate \<open>
struct smoke_adv_offset_pair { int x; int y; };
typedef unsigned long smoke_adv_off_size_t;
smoke_adv_off_size_t smoke_adv_offsetof(void) {
  return __builtin_offsetof(struct smoke_adv_offset_pair, y);
}
\<close>

thm c_smoke_adv_offsetof_def

subsection \<open>Range Designators in Array Initializers\<close>

micro_c_translate \<open>
static unsigned int smoke_adv_range_init[8] = { [2 ... 5] = 42 };
unsigned int smoke_adv_range_lookup(unsigned int i) {
  return smoke_adv_range_init[i];
}
\<close>

thm c_smoke_adv_range_lookup_def

end
