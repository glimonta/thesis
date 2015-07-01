theory Address_Returnv
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition f_decl :: fun_decl
  where "f_decl \<equiv>
    \<lparr> fun_decl.name = ''f'',
      fun_decl.params = [],
      fun_decl.locals = [foo],
      fun_decl.body = 
        foo ::= Const 42;;
        Returnv
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        bar ::= New (Const 1);;
        Callfunl (Derefl (V bar)) ''f'' []
        (* Error: The function doesn't return a value to the address *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''address_returnv'',
      program.globals = [bar],
      program.procs = [f_decl, main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
