theory StrLengthTest
imports "../SmallStep" StrLength
begin

definition strlen_main_decl :: fun_decl
  where "strlen_main_decl \<equiv>
    \<lparr> fun_decl.name = ''strlen_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''strlen_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''strlen_test'',
      program.globals = (program.globals p),
      program.procs = [create_array_decl, str_len_decl, strlen_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "strlen_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "strlen_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code strlen_test_show} @{code strlen_test}
   @{code strlen_failed_check} "../TestC" "strlen_test"\<close>

end