theory Overflow1_Minus
imports "../Tests/Test_Setup"
begin

(* Works but not as I want it to *)
value "shows_exp (Minus (Const (INT_MAX + 1))) ''''"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        $xx := (Minus (Const (INT_MAX + 1))) (* Overflow *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''overflow1_minus'',
      program.structs = [], program.globals = ints [xx],
      program.functs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
