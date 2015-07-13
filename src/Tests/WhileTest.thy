theory WhileTest
imports While
begin

definition while_main_decl :: fun_decl
  where "while_main_decl \<equiv>
    \<lparr> fun_decl.name = ''while_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''while_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''while_test'',
      program.globals = (program.globals p),
      program.procs = [while_main_decl, main_test_decl]
    \<rparr>"

definition "while_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code while_test} "../TestC" "while_test"\<close>

end
