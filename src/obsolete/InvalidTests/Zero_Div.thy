theory Zero_Div
imports "../Tests/Test_Setup"
begin


(* Here we have a problem, overflow is being detected in Plus not in Mod *)
definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        $xx := (Div (Const 42) (Const 0)) (* Division by zero *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''zero_div'',
      program.structs = [], program.globals = ints [xx],
      program.functs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
