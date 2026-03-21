theory C_Translation_Smoke_Types
  imports
    C_To_Core_Translation
begin

section \<open>Type/Semantics Translation Smoke\<close>

micro_c_translate \<open>
unsigned int smoke_types_u_add(unsigned int a, unsigned int b) {
  return a + b;
}
\<close>

thm c_smoke_types_u_add_def

micro_c_translate \<open>
long smoke_types_l_add(long a, long b) {
  return a + b;
}
\<close>

thm c_smoke_types_l_add_def

micro_c_translate \<open>
char smoke_types_identity_char(char c) {
  return c;
}
\<close>

thm c_smoke_types_identity_char_def

micro_c_translate \<open>
unsigned int smoke_types_u_max(unsigned int a, unsigned int b) {
  if (a > b) return a;
  else return b;
}
\<close>

thm c_smoke_types_u_max_def

micro_c_translate \<open>
unsigned char smoke_types_id_u8(unsigned char x) {
  return x;
}
\<close>

thm c_smoke_types_id_u8_def

micro_c_translate \<open>
char smoke_types_char_lit(char c) {
  return 'A';
}
\<close>

thm c_smoke_types_char_lit_def

micro_c_translate \<open>
_Bool smoke_types_bool(_Bool a, _Bool b) {
  if (a) return b;
  else return !a;
}
\<close>

thm c_smoke_types_bool_def

micro_c_translate \<open>
int smoke_types_cast(unsigned int x) {
  return (int)x;
}
\<close>

thm c_smoke_types_cast_def

micro_c_translate \<open>
enum smoke_types_color { SMOKE_RED = 0, SMOKE_GREEN = 1, SMOKE_BLUE = 2 };
unsigned int smoke_types_enum(void) {
  return SMOKE_GREEN;
}
\<close>

thm c_smoke_types_enum_def

micro_c_translate \<open>
typedef unsigned int smoke_uint32;
smoke_uint32 smoke_types_typedef(smoke_uint32 a, smoke_uint32 b) {
  return a + b;
}
\<close>

thm c_smoke_types_typedef_def

micro_c_translate \<open>
static unsigned int smoke_types_static(unsigned int x) { return x + 1; }
\<close>

thm c_smoke_types_static_def

micro_c_translate \<open>
typedef unsigned short smoke_uint16_t;
smoke_uint16_t smoke_types_u16_add(smoke_uint16_t a, smoke_uint16_t b) { return a + b; }
\<close>

thm c_smoke_types_u16_add_def

micro_c_translate \<open>
typedef int smoke_int32_t;
smoke_int32_t smoke_types_i32_negate(smoke_int32_t x) { return 0 - x; }
\<close>

thm c_smoke_types_i32_negate_def

micro_c_translate \<open>
typedef unsigned long smoke_size_t;
smoke_size_t smoke_types_size_add(smoke_size_t a, smoke_size_t b) { return a + b; }
\<close>

thm c_smoke_types_size_add_def

micro_c_translate \<open>
typedef short smoke_int16_t;
smoke_int16_t smoke_types_ret_helper(smoke_int16_t x) { return x; }
smoke_int16_t smoke_types_ret_caller(smoke_int16_t a, smoke_int16_t b) {
  return smoke_types_ret_helper(a) + smoke_types_ret_helper(b);
}
\<close>

thm c_smoke_types_ret_helper_def c_smoke_types_ret_caller_def

micro_c_translate \<open>
unsigned int smoke_types_register(register unsigned int x) {
  register unsigned int y = x + 1;
  return y;
}
\<close>

thm c_smoke_types_register_def

micro_c_translate \<open>
unsigned __int128 smoke_types_u128_add(unsigned __int128 a, unsigned __int128 b) {
  return a + b;
}
\<close>

thm c_smoke_types_u128_add_def

micro_c_translate \<open>
__int128 smoke_types_i128_negate(__int128 x) {
  return 0 - x;
}
\<close>

thm c_smoke_types_i128_negate_def

micro_c_translate addr: nat \<open>
unsigned int smoke_types_volatile_read(volatile unsigned int *p) {
  return *p;
}
\<close>

thm c_smoke_types_volatile_read_def

micro_c_translate \<open>
unsigned int smoke_types_volatile_local(unsigned int x) {
  volatile unsigned int y = x + 1;
  return y;
}
\<close>

thm c_smoke_types_volatile_local_def

end
