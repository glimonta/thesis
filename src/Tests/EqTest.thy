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
      fun_decl.body = CALL ''eq_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''eq_test'',
      program.globals = (program.globals p),
      program.procs = [eq_main_decl, main_test_decl]
    \<rparr>"

definition "eq_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code eq_test} "../TestC" "eq_test"\<close>

end
