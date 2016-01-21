theory OccursTest
imports "../SmallStep" Occurs
begin

definition occurs_main_decl :: fun_decl
  where "occurs_main_decl \<equiv>
    \<lparr> fun_decl.name = ''occurs_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''occurs_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''occurs_test'',
      program.globals = (program.globals p),
      program.procs = [occurs_decl, occurs_main_decl, main_test_decl]
    \<rparr>"

definition "occurs_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code occurs_test} "../TestC" "occurs_test"\<close>

end
