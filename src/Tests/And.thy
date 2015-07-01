theory And
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
        aa ::= (And (V ''true'') (V ''true''));;
      (* False *)
        bb ::= (And (V ''true'') (V ''false''));;
      (* False (short-circuit evaluation) *)
        cc ::= (And (V ''false'') (V ''true''));;
      (* False *)
        dd ::= (And (V ''false'') (V ''false''))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''and'',
      program.globals = [aa,bb,cc,dd,''true'',''false''],
      program.procs = [main_decl]
    \<rparr>"

definition "and_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code and_export}"../TestC" "and"\<close>

end