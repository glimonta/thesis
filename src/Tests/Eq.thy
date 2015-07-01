theory Eq
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= New (Const 10);;
        bb ::= (V aa);;
        cc ::= (Plus (V aa) (Const 2));;
      (* True, two integers*)
        dd ::= (Eq (Const 42) (Const 42));;
      (* False, two integers *)
        ee ::= (Eq (Const 0) (Const 23));;
      (* True, two addresses *)
        ff ::= (Eq (V aa) (V bb));;
      (* False, two addresses *)
        gg ::= (Eq (V aa) (V cc))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''eq'',
      program.globals = [aa,bb,cc,dd,ee,ff,gg],
      program.procs = [main_decl]
    \<rparr>"

definition "eq_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code eq_export}"../TestC" "eq"\<close>

end
