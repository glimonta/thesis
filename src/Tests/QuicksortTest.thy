theory QuicksortTest
imports "../SmallStep" Quicksort
begin

definition quicksort_main_decl :: fun_decl
  where "quicksort_main_decl \<equiv>
    \<lparr> fun_decl.name = ''quicksort_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''quicksort_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''quicksort_test'',
      program.globals = (program.globals p),
      program.procs = [swap_decl, quicksort_decl, quicksort_main_decl, main_test_decl]
    \<rparr>"

definition "quicksort_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code quicksort_test} "../TestC" "quicksort_test"\<close>

end
