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

definition "mod_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code mod_test} "../TestC" "mod_test"\<close>

end
