theory ModTest
imports Mod
begin

definition mod_main_decl :: fun_decl
  where "mod_main_decl \<equiv>
    \<lparr> fun_decl.name = ''mod_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''mod_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''mod_test'',
      program.globals = (program.globals p),
      program.procs = [mod_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "mod_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "mod_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code mod_test_show} @{code mod_test}
   @{code mod_failed_check} "../TestC" "mod_test"\<close>

end