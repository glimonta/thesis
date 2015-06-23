theory SelectionsortTest
imports "../SmallStep" Selectionsort
begin

definition selection_main_decl :: fun_decl
  where "selection_main_decl \<equiv>
    \<lparr> fun_decl.name = ''selection_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''selection_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''selection_test'',
      program.globals = (program.globals p),
      program.procs = [selection_decl, selection_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "selection_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "selection_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code selection_test_show} @{code selection_test}
  @{code init_disc} @{code selection_failed_check} "../TestC" "selection_test"\<close>

end