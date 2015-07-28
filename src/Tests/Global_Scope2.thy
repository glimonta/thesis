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
        RETURN (Mult (V ii) (V jj))
    \<rparr>"

definition doub_decl :: fun_decl
  where "doub_decl \<equiv>
    \<lparr> fun_decl.name = ''doub'',
      fun_decl.params = [ii],
      fun_decl.locals = [foo],
      fun_decl.body = 
        (* The foo accessed here is the local one, not the global one *)  
        foo ::= ''mult'' ([(V ii), (V ii)]);;
        RETURN (V foo)
    \<rparr>"


definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        foo ::= Const 21;;
        bar ::= ''doub'' ([(Const 4)]);;
        IF (Eq (V foo) (Const (42))) THEN
        (* We should be using the global variable in the global context *)
          baz ::= Const 1
        ELSE
        (* Otherwise we generate an error in the program *)
          baz ::= (Plus (Const INT_MAX) (Const 1))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''global_scope2'',
      program.globals = [foo, bar, baz],
      program.procs = [mult_decl, doub_decl, main_decl]
    \<rparr>"


definition "global_scope2_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code global_scope2_export}"../TestC" "global_scope2"\<close>

end
