theory Integer_Address_Less
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Less (Const 21) (New (Const 21)))
        (* Cannot perform less than operation between an integer and an address *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''integer_address_less'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "integer_address_less_exec \<equiv> execute_show [] p"

definition "integer_address_less_ex \<equiv> (
  shows_prog p ''''
)"

definition "integer_address_less_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code integer_address_less_ex} @{code integer_address_less_exec} "../TestC" "integer_address_less"\<close>


end
