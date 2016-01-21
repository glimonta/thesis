theory Integer_Address_Eq
imports "../Tests/Test_Setup"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        $xx := (Eq (Const 21) (New (Const 21)))
        (* Cannot perform equality between an integer and an address *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''integer_address_eq'',
      program.structs = [], program.globals = ints [xx],
      program.functs = [main_decl]
    \<rparr>"

definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
