theory C_Translation_Smoke_Memory
  imports
    C_To_Core_Translation
begin

section \<open>Memory/Pointer Translation Smoke\<close>

micro_c_translate addr: nat \<open>
void smoke_mem_swap(int *a, int *b) {
  int t = *a;
  *a = *b;
  *b = t;
}
\<close>

thm c_smoke_mem_swap_def

micro_c_translate addr: nat \<open>
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

micro_c_translate addr: nat \<open>
int smoke_mem_read_at(int *arr, int idx) {
  return arr[idx];
}
\<close>

thm c_smoke_mem_read_at_def

micro_c_translate addr: nat \<open>
unsigned int smoke_mem_read_at_u(unsigned int *arr, unsigned int idx) {
  return arr[idx];
}
\<close>

thm c_smoke_mem_read_at_u_def

micro_c_translate addr: nat \<open>
void smoke_mem_write_at(int *arr, int idx, int val) {
  arr[idx] = val;
}
\<close>

thm c_smoke_mem_write_at_def

micro_c_translate addr: nat \<open>
typedef unsigned char uint8_t;
uint8_t smoke_mem_read_byte(uint8_t *buf, unsigned int idx) {
  return *(buf + idx);
}
\<close>

thm c_smoke_mem_read_byte_def

micro_c_translate addr: nat \<open>
unsigned int smoke_mem_arr_param(unsigned int arr[], unsigned int i) {
  return arr[i];
}
\<close>

thm c_smoke_mem_arr_param_def

micro_c_translate addr: nat \<open>
void smoke_mem_local_arr(void) {
  unsigned int arr[3] = {1, 2, 3};
  unsigned int x = arr[1];
}
\<close>

thm c_smoke_mem_local_arr_def

micro_c_translate addr: nat \<open>
typedef unsigned char smoke_uint8_t;
void smoke_mem_zero_init(void) {
  smoke_uint8_t t[4] = {0};
  smoke_uint8_t x = t[2];
}
\<close>

thm c_smoke_mem_zero_init_def

micro_c_translate addr: nat \<open>
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

micro_c_translate addr: nat \<open>
unsigned int smoke_mem_inc_via_addr(void) {
  unsigned int x = 5;
  unsigned int *p = &x;
  *p = *p + 1;
  return x;
}
\<close>

thm c_smoke_mem_inc_via_addr_def

micro_c_translate addr: nat \<open>
int smoke_mem_addr_of_index(int *arr, unsigned int idx) {
  int *p = &arr[idx];
  return *p;
}
\<close>

thm c_smoke_mem_addr_of_index_def

micro_c_translate addr: nat \<open>
struct smoke_mem_holder {
  int vec[4];
};
int smoke_mem_addr_of_struct_index(struct smoke_mem_holder *h, unsigned int i) {
  int *p = &h->vec[i];
  return *p;
}
\<close>

thm c_smoke_mem_addr_of_struct_index_def
thm c_smoke_mem_holder.record_simps

micro_c_translate addr: nat \<open>
struct smoke_mem_decay_holder {
  int vec[4];
};
static int smoke_mem_sum2(int *p) {
  return p[0] + p[1];
}
void smoke_mem_struct_array_decay_assign(struct smoke_mem_decay_holder *h, unsigned int i, int v) {
  int *p;
  p = h->vec;
  p[i] = v;
}
int smoke_mem_struct_array_decay_init(struct smoke_mem_decay_holder *h, unsigned int i) {
  int *p = h->vec;
  return p[i];
}
int smoke_mem_struct_array_decay_pass(struct smoke_mem_decay_holder *h) {
  int *p = h->vec;
  return smoke_mem_sum2(p);
}
\<close>

thm c_smoke_mem_sum2_def
thm c_smoke_mem_struct_array_decay_assign_def
thm c_smoke_mem_struct_array_decay_init_def
thm c_smoke_mem_struct_array_decay_pass_def
thm c_smoke_mem_decay_holder.record_simps

micro_c_translate addr: nat \<open>
const int smoke_mem_global_vals[3] = {1, 2, 3};
int smoke_mem_read_global(unsigned int i) {
  return smoke_mem_global_vals[i];
}
\<close>

thm c_global_smoke_mem_global_vals_def
thm c_smoke_mem_read_global_def

end
