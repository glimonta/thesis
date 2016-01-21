theory Overflow2_Mod
imports "../Tests/Test_Setup"
begin


(* Here we have a problem, overflow is being detected in Const not in Mod *)
definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        $xx := (Mod (Const (INT_MIN - 1)) (Const 2)) (* Overflow *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''overflow2_mod'',
      program.structs = [], program.globals = ints [xx],
      program.functs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
