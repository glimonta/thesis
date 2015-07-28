theory CountTest
imports "../SmallStep" "Count"
begin

definition count_main_decl :: fun_decl
  where "count_main_decl \<equiv>
    \<lparr> fun_decl.name = ''count_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''count_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''count_test'',
      program.globals = (program.globals p),
      program.procs = [count_decl, count_main_decl, main_test_decl]
    \<rparr>"

definition "count_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code count_test} "../TestC" "count_test"\<close>

end
