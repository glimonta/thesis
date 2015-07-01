theory Reserved_Keywords_Switch
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        ''switch'' ::= (Const 42) (* ''switch'' is a reserved keyword *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''switch'',
      program.globals = [''switch''],
      program.procs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
