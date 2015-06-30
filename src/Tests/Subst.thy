theory Subst
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= (Subst (Const 2) (Const 2));; (* Substraction positive values *)
        bb ::= (Subst (Const (-1)) (Const (-3)));; (* Substraction negative values *)
        cc ::= (Subst (Const (-3)) (Const (2)));; (* Substraction negative + postive = negative *)
        dd ::= (Subst (Const (3)) (Const (-2)));; (* Substraction postive + negative = positive *)
        ee ::= (New (Const 4));;
        ff ::= (Subst (Plus (V ee) (Const 2)) (Const 2)) (* Addition address + positive value - positive value *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''subst'',
      program.globals = [aa,bb,cc,dd,ee,ff],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "subst_exec \<equiv> execute_show [] p"

definition "subst_ex \<equiv> (
  shows_prog p ''''
)"

definition "subst_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code subst_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code subst_ex} @{code subst_exec} "../TestC" "subst"\<close>


end