theory Variable_Returnv
imports "../Tests/Test_Setup"
begin

(* return void in a function with variable return value *)

definition f_decl :: fun_decl
  where "f_decl \<equiv>
    \<lparr> fun_decl.name = ''f'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [foo],
      fun_decl.body = 
        $foo := Const 42;;
        Returnv
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        Callfun bar ''f'' []
        (* Error: The function doesn't return a value to the variable *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''variable_returnv'',
      program.structs = [], program.globals = ints [bar],
      program.functs = [f_decl, main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
