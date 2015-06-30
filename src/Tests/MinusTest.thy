theory MinusTest
imports Minus
begin

definition minus_main_decl :: fun_decl
  where "minus_main_decl \<equiv>
    \<lparr> fun_decl.name = ''minus_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''minus_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''minus_test'',
      program.globals = (program.globals p),
      program.procs = [minus_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "minus_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "minus_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code minus_test_show} @{code minus_test}
  @{code init_disc} @{code minus_failed_check} "../TestC" "minus_test"\<close>

end