theory NotTest
imports Not
begin

definition not_main_decl :: fun_decl
  where "not_main_decl \<equiv>
    \<lparr> fun_decl.name = ''not_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''not_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''not_test'',
      program.globals = (program.globals p),
      program.procs = [not_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "not_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "not_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code not_test_show} @{code not_test}
  @{code init_disc} @{code not_failed_check} "../TestC" "not_test"\<close>

end