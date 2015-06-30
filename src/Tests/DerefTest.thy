theory DerefTest
imports Deref
begin

definition deref_main_decl :: fun_decl
  where "deref_main_decl \<equiv>
    \<lparr> fun_decl.name = ''deref_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''deref_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''deref_test'',
      program.globals = (program.globals p),
      program.procs = [init_decl, deref_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "deref_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "deref_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code deref_test_show} @{code deref_test}
   @{code deref_failed_check} "../TestC" "deref_test"\<close>

end