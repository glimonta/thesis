theory Reserved_Keywords_Continue
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        ''continue'' ::= (Const 42) (* ''continue'' is a reserved keyword *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''reserved_keywords_continue'',
      program.globals = [''continue''],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "reserved_keywords_continue_exec \<equiv> execute_show [] p"

definition "reserved_keywords_continue_ex \<equiv> (
  shows_prog p ''''
)"

definition "reserved_keywords_continue_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code reserved_keywords_continue_ex} @{code reserved_keywords_continue_exec} "../TestC" "reserved_keywords_continue"\<close>

end
