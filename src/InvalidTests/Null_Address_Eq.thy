theory Null_Address_Eq
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Eq (Null) (New (Const 21)))
        (* Cannot perform equality between an integer and Null *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''null_address_eq'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "null_address_eq_exec \<equiv> execute_show [] p"

definition "null_address_eq_ex \<equiv> (
  shows_prog p ''''
)"

definition "null_address_eq_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>expeqt_c_code @{code null_address_eq_ex} @{code null_address_eq_exec} "../TestC" "null_address_eq"\<close>


end
