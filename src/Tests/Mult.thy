theory Mult
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* Multiplication on positive integers *)
        aa ::= (Mult (Const 4) (Const 2));;
      (* Multiplication on negative integers *)
        bb ::= (Mult (Const (-7)) (Const (-4)));;
      (* Multiplication on a positive and a negative integer *)
        cc ::= (Mult (Const (-8)) (Const (3)));;
      (* Multiplication on a negative and a positive integer *)
        dd ::= (Mult (Const (14)) (Const (-5)));;
      (* Multiplication by zero *)
        ee ::= (Mult (Const 42) (Const 0));;
        ff ::= (Mult (Const 0) (Const 42))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''mult'',
      program.globals = [aa,bb,cc,dd,ee,ff],
      program.procs = [main_decl]
    \<rparr>"

definition "mult_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code mult_export}"../TestC" "mult"\<close>

end
