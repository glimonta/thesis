theory SubstTest
imports "../SmallStep" Subst
begin

definition subst_main_decl :: fun_decl
  where "subst_main_decl \<equiv>
    \<lparr> fun_decl.name = ''subst_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = CALL ''subst_main'' ([])
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''subst_test'',
      program.globals = (program.globals p),
      program.procs = [subst_main_decl, main_test_decl]
    \<rparr>"

definition "subst_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code subst_test} "../TestC" "subst_test"\<close>

end
