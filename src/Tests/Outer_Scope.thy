theory Outer_Scope
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition mult_foo_decl :: fun_decl
  where "mult_foo_decl \<equiv>
    \<lparr> fun_decl.name = ''mult_foo'',
      fun_decl.params = [ii],
      fun_decl.locals = [],
      fun_decl.body = 
        foo ::= Mult (V foo) (V ii)
    \<rparr>"                                

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        (* The mult function access a variable that's not in it's local scope *)
        foo ::= Const 21;;
        Callfunv ''mult_foo'' [(Const 2)];;
        IF (Not (Eq (V foo) (Const 0))) THEN
          bar ::= Const 1 (* If it's correct then we set bar to true *)
        ELSE
          bar ::= (Plus (Const (word_of_int INT_MAX)) (Const 1)) (* Otherwise we generate an error in the program *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''outer_scope'',
      program.globals = [foo, bar],
      program.procs = [mult_foo_decl, main_decl]
    \<rparr>"

export_code p in SML

(* the mult function should access the correct variable and save the result there *)
value "execute_show [] p"

definition "outer_scope_exec \<equiv> execute_show [] p"

definition "outer_scope \<equiv> (
  shows_prog p ''''
)"

definition "outer_scope_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code outer_scope_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code outer_scope} @{code outer_scope_exec}"../TestC" "outer_scope"\<close>

end