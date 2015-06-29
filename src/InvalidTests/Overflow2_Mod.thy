theory Overflow2_Mod
imports "../SmallStep" "../Test" "../Test_Harness"
begin


(* Here we have a problem, overflow is being detected in Plus not in Mod *)
definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Mod (Plus (Const (word_of_int INT_MIN)) (Const 1)) (Const 2)) (* Overflow *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''overflow2_mod'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "overflow2_mod_exec \<equiv> execute_show [] p"

definition "overflow2_mod_ex \<equiv> (
  shows_prog p ''''
)"

definition "overflow2_mod_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code overflow2_mod_ex} @{code overflow2_mod_exec} "../TestC" "overflow2_mod"\<close>


end
