theory MultTest
imports Mult
begin

definition mult_main_decl :: fun_decl
  where "mult_main_decl \<equiv>
    \<lparr> fun_decl.name = ''mult_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''mult_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''mult_test'',
      program.globals = (program.globals p),
      program.procs = [mult_main_decl, main_test_decl]
    \<rparr>"

definition "mult_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code mult_test} "../TestC" "mult_test"\<close>

end
