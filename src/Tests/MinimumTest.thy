theory MinimumTest
imports "../SmallStep" Minimum
begin

definition min_main_decl :: fun_decl
  where "min_main_decl \<equiv>
    \<lparr> fun_decl.name = ''min_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''min_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''min_test'',
      program.globals = (program.globals p),
      program.procs = [min_decl, min_main_decl, main_test_decl]
    \<rparr>"

definition "minimum_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code minimum_test} "../TestC" "min_test"\<close>

end
