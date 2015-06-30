theory Global_Scope_Test
imports "Global_Scope"
begin

definition global_scope_main_decl :: fun_decl
  where "global_scope_main_decl \<equiv>
    \<lparr> fun_decl.name = ''global_scope_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''global_scope_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''global_scope_test'',
      program.globals = (program.globals p),
      program.procs = [mult_decl, global_scope_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "global_scope_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "global_scope_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code global_scope_test_show} @{code global_scope_test}
  @{code init_disc} @{code global_scope_failed_check} "../TestC" "global_scope_test"\<close>

end