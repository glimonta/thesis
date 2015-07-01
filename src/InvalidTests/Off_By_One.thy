theory Off_By_One
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        nn ::= (Const 5);;
        foo ::= New (V nn);;
        ii ::= Const 0;;
        WHILE (Or (Less (V ii) (V nn)) (Eq (V ii) (V nn))) DO (
          (Indexl (V foo) (V ii)) ::== V ii;;
          ii ::= (Plus (V ii) (Const 1))
        )
        (* Error: The condition allows to check the index foo[n] which is an invalid address.
           This error is fairly common when writing cycles if Less or equal than is used. *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''off_by_one'',
      program.globals = [nn, foo, ii],
      program.procs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
