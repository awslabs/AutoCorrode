theory C_Translation_Smoke_Memory
  imports
    C_To_Core_Translation
begin

section \<open>Memory/Pointer Translation Smoke\<close>

micro_c_translate \<open>
void smoke_mem_swap(int *a, int *b) {
  int t = *a;
  *a = *b;
  *b = t;
}
\<close>

thm c_smoke_mem_swap_def

datatype_record c_smoke_mem_point =
  c_smoke_mem_point_x :: c_int
  c_smoke_mem_point_y :: c_int

micro_c_translate \<open>
struct smoke_mem_point {
  int x;
  int y;
};
void smoke_mem_swap_fields(struct smoke_mem_point *p) {
  int t = p->x;
  p->x = p->y;
  p->y = t;
}
\<close>

thm c_smoke_mem_swap_fields_def

micro_c_translate \<open>
int smoke_mem_read_at(int *arr, int idx) {
  return arr[idx];
}
\<close>

thm c_smoke_mem_read_at_def

micro_c_translate \<open>
unsigned int smoke_mem_read_at_u(unsigned int *arr, unsigned int idx) {
  return arr[idx];
}
\<close>

thm c_smoke_mem_read_at_u_def

micro_c_translate \<open>
void smoke_mem_write_at(int *arr, int idx, int val) {
  arr[idx] = val;
}
\<close>

thm c_smoke_mem_write_at_def

micro_c_translate \<open>
typedef unsigned char uint8_t;
uint8_t smoke_mem_read_byte(uint8_t *buf, unsigned int idx) {
  return *(buf + idx);
}
\<close>

thm c_smoke_mem_read_byte_def

micro_c_translate \<open>
unsigned int smoke_mem_arr_param(unsigned int arr[], unsigned int i) {
  return arr[i];
}
\<close>

thm c_smoke_mem_arr_param_def

micro_c_translate \<open>
void smoke_mem_local_arr(void) {
  unsigned int arr[] = {1, 2, 3};
  unsigned int x = arr[1];
}
\<close>

thm c_smoke_mem_local_arr_def

micro_c_translate \<open>
typedef unsigned char smoke_uint8_t;
void smoke_mem_zero_init(void) {
  smoke_uint8_t t[4] = {0};
  smoke_uint8_t x = t[2];
}
\<close>

thm c_smoke_mem_zero_init_def

micro_c_translate \<open>
struct smoke_mem_point {
  int x;
  int y;
};
int smoke_mem_get_x(struct smoke_mem_point *p) {
  int t = p->x;
  return t;
}
\<close>

thm c_smoke_mem_get_x_def

micro_c_translate \<open>
unsigned int smoke_mem_inc_via_addr(void) {
  unsigned int x = 5;
  unsigned int *p = &x;
  *p = *p + 1;
  return x;
}
\<close>

thm c_smoke_mem_inc_via_addr_def

end
