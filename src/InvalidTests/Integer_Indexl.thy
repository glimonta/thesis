theory Integer_Indexl
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        (Indexl (Const 42) (Const 21)) ::== Const 42 (* Cannot apply indexl to two integers *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''integer_indexl'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "integer_indexl_exec \<equiv> execute_show [] p"

definition "integer_indexl_ex \<equiv> (
  shows_prog p ''''
)"

definition "integer_indexl_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code integer_indexl_ex} @{code integer_indexl_exec} "../TestC" "integer_indexl"\<close>


end
