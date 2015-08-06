theory Test_Keywords_Discovered
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        ''__test_harness_discovered'' ::= (Const 42) (* ''__test_harness_discovered'' is a test keyword *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''reserved_keywords_discovered'',
      program.globals = [''__test_harness_discovered''],
      program.procs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
