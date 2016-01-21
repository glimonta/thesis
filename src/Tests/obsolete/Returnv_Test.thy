theory Returnv_Test
imports "Returnv"
begin

definition returnv_main_decl :: fun_decl
  where "returnv_main_decl \<equiv>
    \<lparr> fun_decl.name = ''returnv_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''returnv_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''returnv_test'',
      program.globals = (program.globals p),
      program.procs = [plus_foo_decl, plus_one_foo_decl, returnv_main_decl, main_test_decl]
    \<rparr>"

definition "returnv_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code returnv_test} "../TestC" "returnv_test"\<close>

end
