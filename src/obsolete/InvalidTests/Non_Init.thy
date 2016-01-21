theory Non_Init
imports "../Tests/Test_Setup"
begin


definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        $xx := (Plus (V xx) (Const 42)) (* Variable a is not initialized *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''non_init'',
      program.structs = [], program.globals = ints [xx],
      program.functs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
