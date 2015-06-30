theory Div
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* Division on positive integers that can be exactly divided *)
        aa ::= (Div (Const 4) (Const 2));;
        (* Division on positive integers that can't be exactly divided *)
        bb ::= (Div (Const (7)) (Const (4)));;
        (* Division on negative integers with truncation towards zero *)
        cc ::= (Div (Const (-8)) (Const (-3)));;
        (* Division on a postive and a negative integer with truncation towards zero *)
        dd ::= (Div (Const (14)) (Const (-5)))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''div'',
      program.globals = [aa,bb,cc,dd],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "div_exec \<equiv> execute_show [] p"

definition "div_ex \<equiv> (
  shows_prog p ''''
)"

definition "div_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code div_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code div_ex} @{code div_exec} "../TestC" "div"\<close>


end