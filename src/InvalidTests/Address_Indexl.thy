theory Address_Indexl
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        (Indexl (New (Const 42)) (New (Const 21))) ::== Const 42 (* Cannot apply indexl to two addresses *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''address_indexl'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
