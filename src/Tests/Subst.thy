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

definition "subst_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code subst_export}"../TestC" "subst"\<close>

end
