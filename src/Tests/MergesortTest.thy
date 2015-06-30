theory MergesortTest
imports "../SmallStep" "Mergesort"
begin

definition mergesort_main_decl :: fun_decl
  where "mergesort_main_decl \<equiv>
    \<lparr> fun_decl.name = ''mergesort_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''mergesort_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''mergesort_test'',
      program.globals = (program.globals p),
      program.procs = [merge_decl, mergesort_decl, mergesort_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "mergesort_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "mergesort_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code mergesort_test_show} @{code mergesort_test}
   @{code mergesort_failed_check} "../TestC" "mergesort_test"\<close>

end