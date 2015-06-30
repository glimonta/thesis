theory NewTest
imports New
begin

definition new_main_decl :: fun_decl
  where "new_main_decl \<equiv>
    \<lparr> fun_decl.name = ''new_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''new_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''new_test'',
      program.globals = (program.globals p),
      program.procs = [new_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "new_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "new_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code new_test_show} @{code new_test}
  @{code init_disc} @{code new_failed_check} "../TestC" "new_test"\<close>

end