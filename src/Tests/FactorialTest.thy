theory FactorialTest
imports "../SmallStep" "Factorial"
begin

definition fact_main_decl :: fun_decl
  where "fact_main_decl \<equiv>
    \<lparr> fun_decl.name = ''fact_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''fact_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''fact_test'',
      program.globals = (program.globals p),
      program.procs = [factorial_decl, fact_main_decl, main_test_decl]
    \<rparr>"

definition "fact_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code fact_test} "../TestC" "fact_test"\<close>

end
