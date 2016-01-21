theory Or
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        ''true'' ::= Const 1;;
        ''false'' ::= Const 0;;
      (* True *)
        aa ::= (Or (V ''true'') (V ''true''));;
      (* True (short-circuit evaluation) *)
        bb ::= (Or (V ''true'') (V ''false''));;
      (* True *)
        cc ::= (Or (V ''false'') (V ''true''));;
      (* False *)
        dd ::= (Or (V ''false'') (V ''false''))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''or'',
      program.globals = [aa,bb,cc,dd,''true'',''false''],
      program.procs = [main_decl]
    \<rparr>"

definition "or_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code or_export}"../TestC" "or"\<close>

end
