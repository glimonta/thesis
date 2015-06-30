theory Mod
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* Modulo on positive integers resulting in zero *)
        aa ::= (Mod (Const 4) (Const 2));;
        (* Modulo on positive integers different from zero *)
        bb ::= (Mod (Const (7)) (Const (3)));;
        (* Modulo on negative integers with truncation towards zero *)
        cc ::= (Mod (Const (-8)) (Const (-3)));;
        (* Modulo on a postive and a negative integer with truncation towards zero *)
        dd ::= (Mod (Const (14)) (Const (-5)))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''mod'',
      program.globals = [aa,bb,cc,dd],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "mod_exec \<equiv> execute_show [] p"

definition "mod_ex \<equiv> (
  shows_prog p ''''
)"

definition "mod_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code mod_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code mod_ex} @{code mod_exec} "../TestC" "mod"\<close>


end