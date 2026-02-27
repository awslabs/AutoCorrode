theory C_File_Load_Smoke
  imports
    C_To_Core_Translation
begin

section \<open>micro_c_file Smoke Test\<close>

micro_c_file "smoke_test_file.c"

thm c_file_add_def

end
