theory Invalid_Address_Deref
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= New (Const 5);;
        yy ::= (Deref (Plus (V xx) (Const 5)))
        (* Cannot apply deref to an invalid address, the address would be the next to last element *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''invalid_address_deref'',
      program.globals = [xx, yy],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "invalid_address_deref_exec \<equiv> execute_show [] p"

definition "invalid_address_deref_ex \<equiv> (
  shows_prog p ''''
)"

definition "invalid_address_deref_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code invalid_address_deref_ex} @{code invalid_address_deref_exec} "../TestC" "invalid_address_deref"\<close>


end
