theory No_Args_Callfunv
imports "../Tests/Test_Setup"
begin

definition sum_decl :: fun_decl
  where "sum_decl \<equiv>
    \<lparr> fun_decl.name = ''sum'',
      fun_decl.rtype = None, fun_decl.params = [foo, bar],
      fun_decl.locals = [],
      fun_decl.body = 
        $baz := (Plus (V foo) (V bar));;
        Returnv
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        Callfunv ''sum'' []
        (* Error: No arguments for function call *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''no_args_callfunv'',
      program.structs = [], program.globals = ints [baz],
      program.functs = [sum_decl, main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
