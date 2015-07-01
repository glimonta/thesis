theory Few_Args_Callfun
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition sum_decl :: fun_decl
  where "sum_decl \<equiv>
    \<lparr> fun_decl.name = ''sum'',
      fun_decl.params = [foo, bar],
      fun_decl.locals = [],
      fun_decl.body = 
        Return (Plus (V foo) (V bar))
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        Callfun baz ''sum'' [Const 21]
        (* Error: Too few arguments for function call *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''few_args_callfun'',
      program.globals = [baz],
      program.procs = [sum_decl, main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
