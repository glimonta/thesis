theory Invalid_Address_Free
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= New (Const 6);;
        yy ::= (Plus (V xx) (Const 6));;
        FREE (Derefl (V yy))
        (* Error: Argument of a free is an invalid address*)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''invalid_address_free'',
      program.globals = [xx, yy],
      program.procs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
