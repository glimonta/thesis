theory Integer_Null_Or
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Or (Const 21) (Null));;
        (* Cannot perform or between an integer and a Null.
           The or between an integer and a Null will only fail
           when the first operand is false, otherwise it'll go through
           because of the short-circuit evaluation (the Null will never be evaluated) *)
        xx ::= (Or (Const 0) (Null))
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''integer_null_or'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
