theory OrTest
imports Or
begin

definition or_main_decl :: fun_decl
  where "or_main_decl \<equiv>
    \<lparr> fun_decl.name = ''or_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''or_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''or_test'',
      program.globals = (program.globals p),
      program.procs = [or_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "or_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "or_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code or_test_show} @{code or_test}
   @{code or_failed_check} "../TestC" "or_test"\<close>

end