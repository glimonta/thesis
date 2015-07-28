theory MinusTest
imports Minus
begin

definition minus_main_decl :: fun_decl
  where "minus_main_decl \<equiv>
    \<lparr> fun_decl.name = ''minus_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''minus_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''minus_test'',
      program.globals = (program.globals p),
      program.procs = [minus_main_decl, main_test_decl]
    \<rparr>"

definition "minus_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code minus_test} "../TestC" "minus_test"\<close>

end
