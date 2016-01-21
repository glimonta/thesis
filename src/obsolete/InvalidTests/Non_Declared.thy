theory Non_Declared
imports "../Tests/Test_Setup"
begin


definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        $aa := (Const 42) (* Variable a is not declared *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''non_declared'',
      program.structs = [], program.globals = ints [],
      program.functs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
