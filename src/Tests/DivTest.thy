theory DivTest
imports Div
begin

definition div_main_decl :: fun_decl
  where "div_main_decl \<equiv>
    \<lparr> fun_decl.name = ''div_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''div_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''div_test'',
      program.globals = (program.globals p),
      program.procs = [div_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "div_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "div_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code div_test_show} @{code div_test}
   @{code div_failed_check} "../TestC" "div_test"\<close>

end