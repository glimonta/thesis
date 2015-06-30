theory AndTest
imports And
begin

definition and_main_decl :: fun_decl
  where "and_main_decl \<equiv>
    \<lparr> fun_decl.name = ''and_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''and_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''and_test'',
      program.globals = (program.globals p),
      program.procs = [and_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "and_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "and_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code and_test_show} @{code and_test}
  @{code init_disc} @{code and_failed_check} "../TestC" "and_test"\<close>

end