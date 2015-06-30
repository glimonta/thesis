theory Minus
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= (Minus (Const 2));; (* Minus operation on positive values *)
        bb ::= (Minus (Const (-1))) (* Minus operation on negative values *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''minus'',
      program.globals = [aa,bb],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "minus_exec \<equiv> execute_show [] p"

definition "minus_ex \<equiv> (
  shows_prog p ''''
)"

definition "minus_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code minus_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code minus_ex} @{code minus_exec} "../TestC" "minus"\<close>


end