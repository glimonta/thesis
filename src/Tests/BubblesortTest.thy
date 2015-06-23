theory BubblesortTest
imports "../SmallStep" "Bubblesort"
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

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "bubblesort_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "init_disc_bubble \<equiv> init_discovered 1 ''''"

definition "failed_check_bubble \<equiv> failed_check (program.name p') 1 ''''"

setup \<open>generate_c_test_code @{code bubblesort_test_show} @{code bubblesort_test} @{code bubblesort_test}
  @{code init_disc_bubble} @{code failed_check_bubble} "../TestC" "bubblesort_test"\<close>

end