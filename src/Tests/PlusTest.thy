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
      fun_decl.body = Callfunv ''plus_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''plus_test'',
      program.globals = (program.globals p),
      program.procs = [plus_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

value "execute_show [] p'"

definition "plus_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "plus_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code plus_test_show} @{code plus_test}
   @{code plus_failed_check} "../TestC" "plus_test"\<close>

end