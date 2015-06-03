theory Bubblesort
imports "../SmallStep" "Test"
begin

(* Bubblesort: Takes an array a and its length n and returns the sorted array *)
definition bubblesort_decl :: fun_decl
  where "bubblesort_decl \<equiv>
    \<lparr> fun_decl.name = ''bubblesort'',
      fun_decl.params = [aa, nn],
      fun_decl.locals = [ii,jj, tt],
      fun_decl.body = 
        tt ::= Const 0;;
        FOR ii FROM (Const 1) TO (V nn) DO
          (FOR jj FROM (Const ( 0)) TO (Plus (V nn) (Const ( -1))) DO
            (IF (Less (Index (V aa) (Plus (V jj) (Const ( 1)))) (Index (V aa) (V jj)))
            THEN (tt ::= (Index (V aa) (V jj));;
              (Indexl (V aa) (V jj)) ::== (Index (V aa) (Plus (V jj) (Const ( 1))));;
              (Indexl (V aa) (Plus (V jj) (Const ( 1)))) ::== (V tt))
            ELSE SKIP))
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= New (Const ( 10));;
        (Indexl (V aa) (Const ( 0))) ::== (Const ( 44));;
        (Indexl (V aa) (Const ( 1))) ::== (Const (  1));;
        (Indexl (V aa) (Const ( 2))) ::== (Const ( 60));;
        (Indexl (V aa) (Const ( 3))) ::== (Const ( -26));;
        (Indexl (V aa) (Const ( 4))) ::== (Const ( 54));;
        (Indexl (V aa) (Const ( 5))) ::== (Const ( 1));;
        (Indexl (V aa) (Const ( 6))) ::== (Const ( 92));;
        (Indexl (V aa) (Const ( 7))) ::== (Const ( 84));;
        (Indexl (V aa) (Const ( 8))) ::== (Const ( 38));;
        (Indexl (V aa) (Const ( 9))) ::== (Const ( 80));;
        nn ::= (Const ( 10));;
        Callfunv ''bubblesort'' [(V aa), (V nn)]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.globals = [aa, nn],
      program.procs = [main_decl, bubblesort_decl]
    \<rparr>"

export_code p in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "case execute p of Some (_,\<gamma>,\<mu>) \<Rightarrow> (\<gamma> aa,\<mu>)"

end
