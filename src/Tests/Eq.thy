theory Eq
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= New (Const 10);;
        bb ::= (V aa);;
        cc ::= (Plus (V aa) (Const 2));;
      (* True, two integers*)
        dd ::= (Eq (Const 42) (Const 42));;
      (* False, two integers *)
        ee ::= (Eq (Const 0) (Const 23));;
      (* True, two addresses *)
        ff ::= (Eq (V aa) (V bb));;
      (* False, two addresses *)
        gg ::= (Eq (V aa) (V cc))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''eq'',
      program.globals = [aa,bb,cc,dd,ee,ff,gg],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "eq_exec \<equiv> execute_show [] p"

definition "eq_ex \<equiv> (
  shows_prog p ''''
)"

definition "eq_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code eq_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code eq_ex} @{code eq_exec} "../TestC" "eq"\<close>


end