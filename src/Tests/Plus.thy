theory Plus
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= (Plus (Const 2) (Const 2));; (* Addition positive values *)
        bb ::= (Plus (Const (-1)) (Const (-3)));; (* Addition negative values *)
        cc ::= (Plus (Const (-3)) (Const (2)));; (* Addition negative + postive = negative *)
        dd ::= (Plus (Const (3)) (Const (-2)));; (* Addition postive + negative = positive *)
        ee ::= (Plus (Const (-3)) (Const (5)));; (* Addition negative + postive = positive *)
        ff ::= (Plus (Const (3)) (Const (-6)));; (* Addition postive + negative = negative *)
        gg ::= (New (Const 4));;
        hh ::= (Plus (V gg) (Const 4));; (* Addition address + positive value *)
        ii ::= (Plus (V hh) (Const (-2))) (* Addition address + negative value *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''plus'',
      program.globals = [aa,bb,cc,dd,ee,ff,gg,hh,ii],
      program.procs = [main_decl]
    \<rparr>"

definition "plus_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code plus_export}"../TestC" "plus"\<close>

end
