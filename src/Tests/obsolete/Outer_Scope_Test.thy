theory Outer_Scope_Test
imports "Outer_Scope"
begin

definition outer_scope_main_decl :: fun_decl
  where "outer_scope_main_decl \<equiv>
    \<lparr> fun_decl.name = ''outer_scope_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''outer_scope_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''outer_scope_test'',
      program.globals = (program.globals p),
      program.procs = [mult_foo_decl, outer_scope_main_decl, main_test_decl]
    \<rparr>"

definition "outer_scope_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code outer_scope_test} "../TestC" "outer_scope_test"\<close>

end
