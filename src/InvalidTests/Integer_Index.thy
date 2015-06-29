theory Integer_Index
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Index (Const 42) (Const 21)) (* Cannot apply index to two integers *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''integer_index'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "integer_index_exec \<equiv> execute_show [] p"

definition "integer_index_ex \<equiv> (
  shows_prog p ''''
)"

definition "integer_index_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code integer_index_ex} @{code integer_index_exec} "../TestC" "integer_index"\<close>


end
