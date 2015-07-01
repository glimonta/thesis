theory Div
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* Division on positive integers that can be exactly divided *)
        aa ::= (Div (Const 4) (Const 2));;
        (* Division on positive integers that can't be exactly divided *)
        bb ::= (Div (Const (7)) (Const (4)));;
        (* Division on negative integers with truncation towards zero *)
        cc ::= (Div (Const (-8)) (Const (-3)));;
        (* Division on a postive and a negative integer with truncation towards zero *)
        dd ::= (Div (Const (14)) (Const (-5)))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''div'',
      program.globals = [aa,bb,cc,dd],
      program.procs = [main_decl]
    \<rparr>"


definition "div_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code div_export}"../TestC" "div"\<close>

end
