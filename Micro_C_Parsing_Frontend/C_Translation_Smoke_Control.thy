theory C_Translation_Smoke_Control
  imports
    C_To_Core_Translation
begin

section \<open>Control-Flow Translation Smoke\<close>

micro_c_translate \<open>
void smoke_ctrl_for(int n) {
  int s = 0;
  for (int i = 0; i < n; i++) {
    s = s + i;
  }
}
\<close>

thm c_smoke_ctrl_for_def

micro_c_translate \<open>
void smoke_ctrl_for_lit(void) {
  int s = 0;
  for (int i = 0; i < 5; i++) {
    s = s + i;
  }
}
\<close>

thm c_smoke_ctrl_for_lit_def

micro_c_translate \<open>
void smoke_ctrl_while(int n) {
  int x = 0;
  while (x < n) {
    x = x + 1;
  }
}
\<close>

thm c_smoke_ctrl_while_def

micro_c_translate \<open>
unsigned int smoke_ctrl_goto(unsigned int a, unsigned int b) {
  unsigned int r = a;
  if (b == 0) goto done;
  r = a + b;
 done:
  return r;
}
\<close>

thm c_smoke_ctrl_goto_def

micro_c_translate \<open>
void smoke_ctrl_pre_inc(void) {
  unsigned int x = 0;
  unsigned int r = ++x;
}
\<close>

thm c_smoke_ctrl_pre_inc_def

micro_c_translate \<open>
void smoke_ctrl_post_inc(void) {
  unsigned int x = 0;
  unsigned int r = x++;
}
\<close>

thm c_smoke_ctrl_post_inc_def

micro_c_translate \<open>
void smoke_ctrl_post_dec(void) {
  unsigned int x = 5;
  unsigned int r = x--;
}
\<close>

thm c_smoke_ctrl_post_dec_def

micro_c_translate \<open>
void smoke_ctrl_loop_pre_inc(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) {
    s = s + i;
  }
}
\<close>

thm c_smoke_ctrl_loop_pre_inc_def

micro_c_translate \<open>
unsigned int smoke_ctrl_neq(unsigned int a, unsigned int b) {
  return a != b;
}
\<close>

thm c_smoke_ctrl_neq_def

micro_c_translate \<open>
unsigned int smoke_ctrl_not(unsigned int x) {
  if (!x) return 1; else return 0;
}
\<close>

thm c_smoke_ctrl_not_def

micro_c_translate \<open>
unsigned int smoke_ctrl_uplus(unsigned int x) {
  return +x;
}
\<close>

thm c_smoke_ctrl_uplus_def

micro_c_translate \<open>
unsigned int smoke_ctrl_ternary(unsigned int a, unsigned int b) {
  return (a > b) ? a : b;
}
\<close>

thm c_smoke_ctrl_ternary_def

micro_c_translate \<open>
unsigned int smoke_ctrl_do_while(unsigned int n) {
  unsigned int i = 0;
  do {
    i += 1;
  } while (i < n);
  return i;
}
\<close>

thm c_smoke_ctrl_do_while_def

micro_c_translate \<open>
unsigned int smoke_ctrl_countdown(unsigned int n) {
  unsigned int r = 0;
  for (unsigned int i = n; i > 0; i--) {
    r += i;
  }
  return r;
}
\<close>

thm c_smoke_ctrl_countdown_def

micro_c_translate \<open>
unsigned int smoke_ctrl_add_assign(unsigned int a, unsigned int b) {
  unsigned int x = a;
  x += b;
  return x;
}
\<close>

thm c_smoke_ctrl_add_assign_def

micro_c_translate \<open>
unsigned int smoke_ctrl_sub_assign(unsigned int a, unsigned int b) {
  unsigned int x = a;
  x -= b;
  return x;
}
\<close>

thm c_smoke_ctrl_sub_assign_def

micro_c_translate \<open>
unsigned int smoke_ctrl_mul_assign(unsigned int a) {
  unsigned int x = a;
  x *= 2;
  return x;
}
\<close>

thm c_smoke_ctrl_mul_assign_def

section \<open>Switch Statement Smoke\<close>

micro_c_translate \<open>
unsigned int smoke_ctrl_switch_basic(unsigned int x) {
  unsigned int r;
  switch (x) {
    case 0: r = 10; break;
    case 1: r = 20; break;
    default: r = 99; break;
  }
  return r;
}
\<close>

thm c_smoke_ctrl_switch_basic_def

micro_c_translate \<open>
unsigned int smoke_ctrl_switch_fallthrough(unsigned int x) {
  unsigned int r;
  switch (x) {
    case 0:
    case 1: r = 42; break;
    default: r = 0; break;
  }
  return r;
}
\<close>

thm c_smoke_ctrl_switch_fallthrough_def

micro_c_translate \<open>
unsigned int smoke_ctrl_switch_no_default(unsigned int x) {
  unsigned int r = 0;
  switch (x) {
    case 1: r = 1; break;
    case 2: r = 2; break;
  }
  return r;
}
\<close>

thm c_smoke_ctrl_switch_no_default_def

end
