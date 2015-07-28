theory PlusTest
imports Plus
begin

definition plus_main_decl :: fun_decl
  where "plus_main_decl \<equiv>
    \<lparr> fun_decl.name = ''plus_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''plus_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''plus_test'',
      program.globals = (program.globals p),
      program.procs = [plus_main_decl, main_test_decl]
    \<rparr>"

definition "plus_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code plus_test} "../TestC" "plus_test"\<close>

end
