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
      fun_decl.body = Callfunv ''subst_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''subst_test'',
      program.globals = (program.globals p),
      program.procs = [subst_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "subst_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "subst_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code subst_test_show} @{code subst_test}
   @{code subst_failed_check} "../TestC" "subst_test"\<close>

end