theory Global_Scope2_Test
imports "Global_Scope2"
begin

definition global_scope2_main_decl :: fun_decl
  where "global_scope2_main_decl \<equiv>
    \<lparr> fun_decl.name = ''global_scope2_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''global_scope2_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''global_scope2_test'',
      program.globals = (program.globals p),
      program.procs = [mult_decl, doub_decl, global_scope2_main_decl, main_test_decl]
    \<rparr>"

definition "global_scope2_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code global_scope2_test} "../TestC" "global_scope2_test"\<close>

end
