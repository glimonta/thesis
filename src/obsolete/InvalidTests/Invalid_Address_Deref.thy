theory Invalid_Address_Deref
imports "../Tests/Test_Setup"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        $xx := New (Const 5);;
        $yy := (Deref (Plus (V xx) (Const 5)))
        (* Cannot apply deref to an invalid address, the address would be the next to last element *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''invalid_address_deref'',
      program.structs = [], program.globals = ints [xx, yy],
      program.functs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
