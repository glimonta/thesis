theory Test_Keywords_Num_Tests
imports "../Tests/Test_Setup"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        ''__test_harness_num_tests'' ::= (Const 42) (* ''__test_harness_num_tests'' is a reserved keyword *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''reserved_keywords_num_tests'',
      program.structs = [], program.globals = ints [''__test_harness_num_tests''],
      program.functs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
