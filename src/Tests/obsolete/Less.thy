theory Less
imports Test_Setup
begin


definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* True *)
        aa ::= (Less (Const 2) (Const 89));;
      (* True *)
        bb ::= (Less (Const (-7)) (Const (-4)));;
      (* True *)
        cc ::= (Less (Const (-8)) (Const (3)));;
      (* False *)
        dd ::= (Less (Const (14)) (Const (-5)));;
      (* False *)
        ee ::= (Less (Const 42) (Const 4));;
      (* False *)
        ff ::= (Less (Const (-4)) (Const (-56)));;
      (* False *)
        gg ::= (Less (Const 42) (Const 42))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''less'',
      program.globals = [aa,bb,cc,dd,ee,ff,gg],
      program.procs = [main_decl]
    \<rparr>"

definition "less_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code less_export}"../TestC" "less"\<close>

end
