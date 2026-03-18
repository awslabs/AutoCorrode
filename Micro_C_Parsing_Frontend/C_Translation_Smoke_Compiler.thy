theory C_Translation_Smoke_Compiler
  imports
    C_To_Core_Translation
begin

section \<open>Compiler Profile Smoke Tests\<close>

text \<open>Verify that @{text "compiler:"} parameter selects the expected behavior
  for char signedness, signed right shift, and signed narrowing casts.\<close>

subsection \<open>Char signedness\<close>

text \<open>Under @{text "gcc-x86_64"}, plain @{text "char"} is signed.\<close>

micro_c_translate prefix: comp_x86_ compiler: gcc-x86_64 \<open>
char comp_char_id(char c) { return c; }
\<close>

thm comp_x86_comp_char_id_def

text \<open>Under @{text "gcc-aarch64"}, plain @{text "char"} is unsigned.\<close>

micro_c_translate prefix: comp_arm_ compiler: gcc-aarch64 \<open>
char comp_char_id(char c) { return c; }
\<close>

thm comp_arm_comp_char_id_def

subsection \<open>Signed right shift\<close>

text \<open>Under @{text "gcc-x86_64"}, signed right shift uses arithmetic (sign-extending) shift.\<close>

micro_c_translate prefix: comp_shr_gcc_ compiler: gcc-x86_64 \<open>
int comp_shr(int a, int b) { return a >> b; }
\<close>

thm comp_shr_gcc_comp_shr_def

text \<open>Under @{text "conservative"}, signed right shift aborts on negative operand.\<close>

micro_c_translate prefix: comp_shr_con_ compiler: conservative \<open>
int comp_shr(int a, int b) { return a >> b; }
\<close>

thm comp_shr_con_comp_shr_def

subsection \<open>Signed narrowing cast\<close>

text \<open>Under @{text "conservative"}, signed narrowing cast checks for overflow.\<close>

micro_c_translate prefix: comp_cast_con_ compiler: conservative \<open>
int comp_narrow(long a) { return (int)a; }
\<close>

thm comp_cast_con_comp_narrow_def

text \<open>Under @{text "gcc-aarch64"}, signed narrowing cast silently truncates.\<close>

micro_c_translate prefix: comp_cast_gcc_ compiler: gcc-aarch64 \<open>
int comp_narrow(long a) { return (int)a; }
\<close>

thm comp_cast_gcc_comp_narrow_def

end
