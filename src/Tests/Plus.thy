theory Plus
imports "../SmallStep" "Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= (Plus (Const 2) (Const 2));; (* Addition positive values *)
        bb ::= (Plus (Const (-1)) (Const (-3)));; (* Addition negative values *)
        cc ::= (New (Const 4));;
        dd ::= (Plus (V cc) (Const 2)) (* Addition address + positive value *)
        (*ee ::= (Plus (Const 2147483647) (Const 1)) (* Overflow *)*)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''plus'',
      program.globals = [aa,bb,cc,dd,ee],
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

setup \<open>export_c_code @{code plus_ex} "../TestC" "plus"\<close>


end