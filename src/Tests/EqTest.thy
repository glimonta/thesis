theory EqTest
imports Eq
begin

definition eq_main_decl :: fun_decl
  where "eq_main_decl \<equiv>
    \<lparr> fun_decl.name = ''eq_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''eq_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''eq_test'',
      program.globals = (program.globals p),
      program.procs = [eq_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "eq_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "eq_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code eq_test_show} @{code eq_test}
  @{code init_disc} @{code eq_failed_check} "../TestC" "eq_test"\<close>

end