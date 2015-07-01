theory Mergesort
imports "../SmallStep" "../Test" "../Test_Harness"
begin

(* Merge: Takes an array a and its length n and merges the two ordered parts of the array *)
definition merge_decl :: fun_decl
  where "merge_decl \<equiv>
    \<lparr> fun_decl.name = ''merge'',
      fun_decl.params = [aa, nn, mm],
      fun_decl.locals = [ii, jj, kk, xx],
      fun_decl.body = 
        xx ::= New (V nn);;
        ii ::= Const 0;;
        jj ::= V mm;;
        kk ::= Const 0;;
        WHILE (Less (V kk) (V nn)) DO (
          (IF (Eq (V jj) (V nn)) THEN
            ((Indexl (V xx) (V kk)) ::== (Index (V aa) (V ii));;
            ii ::= (Plus (V ii) (Const 1)))
          ELSE 
            (IF (Eq (V ii) (V mm)) THEN
              ((Indexl (V xx) (V kk)) ::== (Index (V aa) (V jj));;
              jj ::= (Plus (V jj) (Const 1)))
            ELSE
              (IF (Less (Index (V aa) (V jj)) (Index (V aa) (V ii))) THEN
                ((Indexl (V xx) (V kk)) ::== (Index (V aa) (V jj));;
                jj ::= (Plus (V jj) (Const 1)))
              ELSE
                ((Indexl (V xx) (V kk)) ::== (Index (V aa) (V ii));;
                ii ::= (Plus (V ii) (Const 1)))
              )
            )
          );;
          kk ::= (Plus (V kk) (Const 1))
        );;
        ii ::= Const 0;;
        WHILE (Less (V ii) (V nn)) DO (
          (Indexl (V aa) (V ii)) ::== (Index (V xx) (V ii));;
          ii ::= (Plus (V ii) (Const 1))
        );;
        FREE (Derefl (V xx))
    \<rparr>"

(* Mergesort: Takes an array a and its length n and returns the sorted array *)
definition mergesort_decl :: fun_decl
  where "mergesort_decl \<equiv>
    \<lparr> fun_decl.name = ''mergesort'',
      fun_decl.params = [aa, nn],
      fun_decl.locals = [mm, xx],
      fun_decl.body = 
        IF (Less (V nn) (Const 2)) THEN
          Returnv
        ELSE
          (mm ::= (Div (V nn) (Const 2));;
          Callfunv ''mergesort'' [V aa, V mm];;
          Callfunv ''mergesort'' [(Ref (Indexl (V aa) (V mm))), (Plus (V nn) (Minus (V mm)))]);;
          Callfunv ''merge'' [V aa, V nn, V mm]
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= New (Const ( 10));;
        (Indexl (V aa) (Const ( 0))) ::== (Const ( 44));;
        (Indexl (V aa) (Const ( 1))) ::== (Const ( 98));;
        (Indexl (V aa) (Const ( 2))) ::== (Const ( 60));;
        (Indexl (V aa) (Const ( 3))) ::== (Const ( 26));;
        (Indexl (V aa) (Const ( 4))) ::== (Const ( 54));;
        (Indexl (V aa) (Const ( 5))) ::== (Const (  1));;
        (Indexl (V aa) (Const ( 6))) ::== (Const ( 92));;
        (Indexl (V aa) (Const ( 7))) ::== (Const ( 84));;
        (Indexl (V aa) (Const ( 8))) ::== (Const ( 38));;
        (Indexl (V aa) (Const ( 9))) ::== (Const ( 80));;
        nn ::= (Const ( 10));;
        Callfunv ''mergesort'' [(V aa), (V nn)]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''mergesort'',
      program.globals = [aa, nn],
      program.procs = [merge_decl, mergesort_decl, main_decl]
    \<rparr>"

definition "mergesort_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code mergesort_export}"../TestC" "mergesort"\<close>

end
