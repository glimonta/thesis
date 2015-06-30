theory LessTest
imports Less
begin

definition less_main_decl :: fun_decl
  where "less_main_decl \<equiv>
    \<lparr> fun_decl.name = ''less_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''less_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''less_test'',
      program.globals = (program.globals p),
      program.procs = [less_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "less_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "less_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code less_test_show} @{code less_test}
  @{code init_disc} @{code less_failed_check} "../TestC" "less_test"\<close>

end