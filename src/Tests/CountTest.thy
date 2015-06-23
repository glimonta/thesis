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
      fun_decl.body = Callfunv ''count_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''count_test'',
      program.globals = (program.globals p),
      program.procs = [count_decl, count_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "count_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "count_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code count_test_show} @{code count_test}
  @{code init_disc} @{code count_failed_check} "../TestC" "count_test"\<close>

end