theory Deref
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition init_decl :: fun_decl
  where "init_decl \<equiv>
    \<lparr> fun_decl.name = ''init'',
      fun_decl.params = [aa, nn],
      fun_decl.locals = [ii],
      fun_decl.body = 
        ii ::= Const 0;;
        WHILE (Less (V ii) (V nn)) DO (
          (Indexl (V aa) (V ii)) ::== (V ii);;
          ii ::= (Plus (V ii) (Const 1))
        )
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        nn ::= Const 10;;
        aa ::= New (V nn);;

        Callfunv ''init'' [V aa, V nn];;

        (* j contains the number of matches with the content in memory *)
        ii ::= Const 0;;
        jj ::= Const 0;;
        WHILE (Less (V ii) (V nn)) DO (
          (IF (Eq (Deref (Plus (V aa) (V ii))) (V ii)) THEN
            jj ::= (Plus (V jj) (Const 1))
          ELSE
            SKIP);;
          ii ::= (Plus (V ii) (Const 1))
        )
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''deref'',
      program.globals = [nn,aa,ii,jj],
      program.procs = [init_decl, main_decl]
    \<rparr>"

definition "deref_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code deref_export}"../TestC" "deref"\<close>

end
