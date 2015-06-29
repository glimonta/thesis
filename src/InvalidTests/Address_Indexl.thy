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

export_code p in SML

value "execute_show [] p"

definition "address_indexl_exec \<equiv> execute_show [] p"

definition "address_indexl_ex \<equiv> (
  shows_prog p ''''
)"

definition "address_indexl_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code address_indexl_ex} @{code address_indexl_exec} "../TestC" "address_indexl"\<close>


end
