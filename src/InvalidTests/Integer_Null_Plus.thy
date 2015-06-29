theory Integer_Null_Plus
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Plus (Const 21) (Null)) (* Cannot add an integer to Null *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''integer_null_plus'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "integer_null_plus_exec \<equiv> execute_show [] p"

definition "integer_null_plus_ex \<equiv> (
  shows_prog p ''''
)"

definition "integer_null_plus_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code integer_null_plus_ex} @{code integer_null_plus_exec} "../TestC" "integer_null_plus"\<close>


end