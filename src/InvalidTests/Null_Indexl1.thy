theory Null_Indexl1
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        (Indexl (Null) (Const 21)) ::== Const 42 (* The first operator of indexl can't be null *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''null_indexl1'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "null_indexl1_exec \<equiv> execute_show [] p"

definition "null_indexl1_ex \<equiv> (
  shows_prog p ''''
)"

definition "null_indexl1_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code null_indexl1_ex} @{code null_indexl1_exec} "../TestC" "null_indexl1"\<close>


end
