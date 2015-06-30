theory Plus
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= (Plus (Const 2) (Const 2));; (* Addition positive values *)
        bb ::= (Plus (Const (-1)) (Const (-3)));; (* Addition negative values *)
        cc ::= (Plus (Const (-3)) (Const (2)));; (* Addition negative + postive = negative *)
        dd ::= (Plus (Const (3)) (Const (-2)));; (* Addition postive + negative = positive *)
        ee ::= (Plus (Const (-3)) (Const (5)));; (* Addition negative + postive = positive *)
        ff ::= (Plus (Const (3)) (Const (-6)));; (* Addition postive + negative = negative *)
        gg ::= (New (Const 4));;
        hh ::= (Plus (V gg) (Const 4));; (* Addition address + positive value *)
        ii ::= (Plus (V hh) (Const (-2))) (* Addition address + negative value *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''plus'',
      program.globals = [aa,bb,cc,dd,ee,ff,gg,hh,ii],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "plus_exec \<equiv> execute_show [] p"

definition "plus_ex \<equiv> (
  shows_prog p ''''
)"

definition "plus_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code plus_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code plus_ex} @{code plus_exec} "../TestC" "plus"\<close>


end