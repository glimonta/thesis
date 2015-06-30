theory Less
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* True *)
        aa ::= (Less (Const 2) (Const 89));;
      (* True *)
        bb ::= (Less (Const (-7)) (Const (-4)));;
      (* True *)
        cc ::= (Less (Const (-8)) (Const (3)));;
      (* False *)
        dd ::= (Less (Const (14)) (Const (-5)));;
      (* False *)
        ee ::= (Less (Const 42) (Const 4));;
      (* False *)
        ff ::= (Less (Const (-4)) (Const (-56)));;
      (* False *)
        gg ::= (Less (Const 42) (Const 42))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''less'',
      program.globals = [aa,bb,cc,dd,ee,ff,gg],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "less_exec \<equiv> execute_show [] p"

definition "less_ex \<equiv> (
  shows_prog p ''''
)"

definition "less_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code less_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code less_ex} @{code less_exec} "../TestC" "less"\<close>


end