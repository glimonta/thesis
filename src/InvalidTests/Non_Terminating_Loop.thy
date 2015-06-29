theory Non_Terminating_Loop
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        WHILE (Const 1) DO
          SKIP
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''non_terminating_loop'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "non_terminating_loop_exec \<equiv> execute_show [] p"

definition "non_terminating_loop_ex \<equiv> (
  shows_prog p ''''
)"

definition "non_terminating_loop_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code non_terminating_loop_ex} @{code non_terminating_loop_exec} "../TestC" "non_terminating_loop"\<close>


end
