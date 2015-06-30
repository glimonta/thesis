theory New
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* New operation doesn't fail unless asking for space of zero or negative size *)
        aa ::= (New (Const 2));; (* New operation of length 2 *)
        bb ::= (New (Const 42)) (* New operation of length 42 *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''new'',
      program.globals = [aa,bb],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "new_exec \<equiv> execute_show [] p"

definition "new_ex \<equiv> (
  shows_prog p ''''
)"

definition "new_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code new_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code new_ex} @{code new_exec} "../TestC" "new"\<close>


end