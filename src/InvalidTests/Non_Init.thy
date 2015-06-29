theory Non_Init
imports "../SmallStep" "../Test" "../Test_Harness"
begin


definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Plus (V xx) (Const 42)) (* Variable a is not initialized *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''non_init'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "non_init_exec \<equiv> execute_show [] p"

definition "non_init_ex \<equiv> (
  shows_prog p ''''
)"

definition "non_init_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code non_init_ex} @{code non_init_exec} "../TestC" "non_init"\<close>

end