theory Invalid_Address_Derefl
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= New (Const 5);;
        (Derefl (Plus (V xx) (Const 5))) ::== (Const 42)
        (* Cannot apply derefl to an invalid address, the address would be the next to last element *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''invalid_address_derefl'',
      program.globals = [xx, yy],
      program.procs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
