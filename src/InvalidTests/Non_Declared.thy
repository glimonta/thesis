theory Non_Declared
imports "../SmallStep" "../Test" "../Test_Harness"
begin


definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        aa ::= (Const 42) (* Variable a is not declared *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''non_declared'',
      program.globals = [],
      program.procs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
