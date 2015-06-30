theory Not
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        ''true'' ::= Const 1;;
        ''false'' ::= Const 0;;
      (* True \<rightarrow> False*)
        aa ::= (Not (V ''true''));;
      (* False \<rightarrow> True*)
        bb ::= (Not (V ''false''))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''not'',
      program.globals = [aa,bb,''true'',''false''],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "not_exec \<equiv> execute_show [] p"

definition "not_ex \<equiv> (
  shows_prog p ''''
)"

definition "not_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code not_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code not_ex} @{code not_exec} "../TestC" "not"\<close>


end