theory Global_Scope2
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition mult_decl :: fun_decl
  where "mult_decl \<equiv>
    \<lparr> fun_decl.name = ''mult'',
      fun_decl.params = [ii, jj],
      fun_decl.locals = [],
      fun_decl.body = 
        (* The foo accessed here is the global one, not the one in double *)
        foo ::= Const 42;;
        Return (Mult (V ii) (V jj))
    \<rparr>"

definition doub_decl :: fun_decl
  where "doub_decl \<equiv>
    \<lparr> fun_decl.name = ''doub'',
      fun_decl.params = [ii],
      fun_decl.locals = [foo],
      fun_decl.body = 
        (* The foo accessed here is the local one, not the global one *)  
        Callfun foo ''mult'' [(V ii), (V ii)];;
        Return (V foo)
    \<rparr>"


definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        foo ::= Const 21;;
        Callfun bar ''doub'' [(Const 4)];;
        IF (Eq (V foo) (Const (42))) THEN
        (* We should be using the global variable in the global context *)
          baz ::= Const 1
        ELSE
        (* Otherwise we generate an error in the program *)
          baz ::= (Plus (Const (word_of_int INT_MAX)) (Const 1))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''global_scope2'',
      program.globals = [foo, bar, baz],
      program.procs = [mult_decl, doub_decl, main_decl]
    \<rparr>"

export_code p in SML

(* the mult function should access the correct variable and save the result there *)
value "execute_show [] p"

definition "global_scope2_exec \<equiv> execute_show [] p"

definition "global_scope2 \<equiv> (
  shows_prog p ''''
)"

definition "global_scope2_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code global_scope2_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code global_scope2} @{code global_scope2_exec}"../TestC" "global_scope2"\<close>

end