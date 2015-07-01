theory LessTest
imports Less
begin

definition less_main_decl :: fun_decl
  where "less_main_decl \<equiv>
    \<lparr> fun_decl.name = ''less_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''less_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''less_test'',
      program.globals = (program.globals p),
      program.procs = [less_main_decl, main_test_decl]
    \<rparr>"

definition "less_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code less_test} "../TestC" "less_test"\<close>

end
