theory OccursTest
imports "../SmallStep" Occurs
begin

definition occurs_main_decl :: fun_decl
  where "occurs_main_decl \<equiv>
    \<lparr> fun_decl.name = ''occurs_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''occurs_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''occurs_test'',
      program.globals = (program.globals p),
      program.procs = [occurs_decl, occurs_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "occurs_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "occurs_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code occurs_test_show} @{code occurs_test}
   @{code occurs_failed_check} "../TestC" "occurs_test"\<close>

end