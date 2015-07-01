theory Integer_Address_Or
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Or (Const 21) (New (Const 21)));;
        (* Cannot perform or between an integer or an address.
           The or between an integer and an address will only fail
           when the first operand is false, otherwise it'll go through
           because of the short-circuit evaluation (the address will never be evaluated) *)
        xx ::= (Or (Const 0) (New (Const 21)))
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''integer_address_or'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

value "execute_show (program.globals p) p"

definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
