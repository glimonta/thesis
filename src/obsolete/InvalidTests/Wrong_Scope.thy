theory Wrong_Scope
imports "../Tests/Test_Setup"
begin

definition f_decl :: fun_decl
  where "f_decl \<equiv>
    \<lparr> fun_decl.name = ''f'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [xx],
      fun_decl.body =
        $xx := (Const 42)
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        Callfunv ''f'' [];;
        $xx := (Const 21) (* Variable xx is only in f's local scope *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''wrong_scope'',
      program.structs = [], program.globals = ints [],
      program.functs = [f_decl, main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
