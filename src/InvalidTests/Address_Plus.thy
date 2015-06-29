theory Address_Plus
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Plus (New (Const 21)) (New (Const 21))) (* Cannot add 2 addresses *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''address_plus'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "address_plus_exec \<equiv> execute_show [] p"

definition "address_plus_ex \<equiv> (
  shows_prog p ''''
)"

definition "address_plus_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code address_plus_ex} @{code address_plus_exec} "../TestC" "address_plus"\<close>


end