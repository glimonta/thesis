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
      fun_decl.body = Callfunv ''outer_scope_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''outer_scope_test'',
      program.globals = (program.globals p),
      program.procs = [mult_foo_decl, outer_scope_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "outer_scope_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "outer_scope_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code outer_scope_test_show} @{code outer_scope_test}
  @{code init_disc} @{code outer_scope_failed_check} "../TestC" "outer_scope_test"\<close>

end