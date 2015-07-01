theory Address_Null_And
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (And (New (Const 42)) (Null))
        (* Cannot perform and between an integer and Null *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''address_null_and'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
