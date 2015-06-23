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
      fun_decl.body = Callfunv ''quicksort_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''quicksort_test'',
      program.globals = (program.globals p),
      program.procs = [swap_decl, quicksort_decl, quicksort_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "quicksort_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "quicksort_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code quicksort_test_show} @{code quicksort_test}
  @{code init_disc} @{code quicksort_failed_check} "../TestC" "quicksort_test"\<close>

end