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
        CALL ''mult_foo'' ([(Const 2)]);;
        IF (Not (Eq (V foo) (Const 0))) THEN
          bar ::= Const 1 (* If it's correct then we set bar to true *)
        ELSE
          bar ::= (Plus (Const INT_MAX) (Const 1)) (* Otherwise we generate an error in the program *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''outer_scope'',
      program.globals = [foo, bar],
      program.procs = [mult_foo_decl, main_decl]
    \<rparr>"

definition "outer_scope_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code outer_scope_export}"../TestC" "outer_scope"\<close>

end
