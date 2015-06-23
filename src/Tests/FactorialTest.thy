theory FactorialTest
imports "../SmallStep" "Factorial"
begin

definition fact_main_decl :: fun_decl
  where "fact_main_decl \<equiv>
    \<lparr> fun_decl.name = ''fact_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''fact_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''fact_test'',
      program.globals = (program.globals p),
      program.procs = [factorial_decl, fact_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "fact_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "fact_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code fact_test_show} @{code fact_test}
  @{code init_disc} @{code fact_failed_check} "../TestC" "fact_test"\<close>

end