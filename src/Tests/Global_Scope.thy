theory Global_Scope
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition mult_decl :: fun_decl
  where "mult_decl \<equiv>
    \<lparr> fun_decl.name = ''mult'',
      fun_decl.params = [ii, jj],
      fun_decl.locals = [foo],
      fun_decl.body = 
        (* The foo accessed here is the local one, not the global one *)
        foo ::= V ii;;
        Return (Mult (V foo) (V jj))
    \<rparr>"                                

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        foo ::= Const 21;;
        Callfun bar ''mult'' [(Const 2), (Const 4)];;
        foo ::= (Subst (V bar) (V foo));;
        IF (Eq (V foo) (Const (- 13))) THEN
        (* We should be using the global variable in the global context *)
          baz ::= Const 1
        ELSE
        (* Otherwise we generate an error in the program *)
          baz ::= (Plus (Const INT_MAX) (Const 1))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''global_scope'',
      program.globals = [foo, bar, baz],
      program.procs = [mult_decl, main_decl]
    \<rparr>"


definition "global_scope_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code global_scope_export}"../TestC" "global_scope"\<close>

end
