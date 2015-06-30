theory BubblesortTest
imports "Bubblesort"
begin

definition bubblesort_main_decl :: fun_decl
  where "bubblesort_main_decl \<equiv>
    \<lparr> fun_decl.name = ''bubblesort_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''bubblesort_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''bubblesort_test'',
      program.globals = (program.globals p),
      program.procs = [bubblesort_decl, bubblesort_main_decl, main_test_decl]
    \<rparr>"

definition "bubblesort_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code bubblesort_test} "../TestC" "bubblesort_test"\<close>

end
