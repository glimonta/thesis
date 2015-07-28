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
      fun_decl.body = CALL ''div_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''div_test'',
      program.globals = (program.globals p),
      program.procs = [div_main_decl, main_test_decl]
    \<rparr>"

definition "div_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code div_test} "../TestC" "div_test"\<close>

end
