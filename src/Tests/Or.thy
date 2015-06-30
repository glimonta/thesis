theory Or
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
      (* True *)
        aa ::= (Or (V ''true'') (V ''true''));;
      (* True (short-circuit evaluation) *)
        bb ::= (Or (V ''true'') (V ''false''));;
      (* True *)
        cc ::= (Or (V ''false'') (V ''true''));;
      (* False *)
        dd ::= (Or (V ''false'') (V ''false''))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''or'',
      program.globals = [aa,bb,cc,dd,''true'',''false''],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "or_exec \<equiv> execute_show [] p"

definition "or_ex \<equiv> (
  shows_prog p ''''
)"

definition "or_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code or_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code or_ex} @{code or_exec} "../TestC" "or"\<close>


end