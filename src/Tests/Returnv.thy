theory Returnv
imports "../SmallStep" "../Test" "../Test_Harness"
begin


(* Even though there's no explicit return in the plus function it will return because
   a function returns when reaching the end of control *)
definition plus_foo_decl :: fun_decl
  where "plus_foo_decl \<equiv>
    \<lparr> fun_decl.name = ''plus_foo'',
      fun_decl.params = [ii],
      fun_decl.locals = [],
      fun_decl.body = 
        foo ::= Plus (V foo) (V ii)
    \<rparr>"                                

(* We can also use a explicit return and it works the same way *)
definition plus_one_foo_decl :: fun_decl
  where "plus_one_foo_decl \<equiv>
    \<lparr> fun_decl.name = ''plus_one_foo'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        foo ::= Plus (V foo) (Const 1)
    \<rparr>"  

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        foo ::= Const 21;;
        Callfunv ''plus_foo'' [(Const 20)];;
        Callfunv ''plus_one_foo'' [];;
        IF (Eq (V foo) (Const 42)) THEN
          bar ::= Const 1 (* If it's correct then we set bar to true *)
        ELSE
          bar ::= (Plus (Const INT_MAX) (Const 1)) (* Otherwise we generate an error in the program *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''returnv'',
      program.globals = [foo, bar],
      program.procs = [plus_foo_decl, plus_one_foo_decl, main_decl]
    \<rparr>"

definition "returnv_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code returnv_export}"../TestC" "returnv"\<close>

end
