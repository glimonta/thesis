theory Address_Null_Mult
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Mult (New (Const 42)) (Null))
        (* Cannot perform multiplication between an integer and Null *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''address_null_mult'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "address_null_mult_exec \<equiv> execute_show [] p"

definition "address_null_mult_ex \<equiv> (
  shows_prog p ''''
)"

definition "address_null_mult_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code address_null_mult_ex} @{code address_null_mult_exec} "../TestC" "address_null_mult"\<close>


end
