theory Occurs
imports "../SmallStep" Test
begin

(* Occurs: Takes an array a, its length n and an element x, returns 0 if the element x doesn't exist
   in the array and 1 if it does exist. *)
definition occurs_decl :: fun_decl
  where "occurs_decl \<equiv> 
    \<lparr> fun_decl.name = ''occurs'',
      fun_decl.params = [aa, nn, xx],
      fun_decl.locals = [cc, ii],
      fun_decl.body = 
        cc ::= (Const ( 0));; (* Counter of occurences *)
        FOR ii FROM (Const ( 0)) TO (V nn) DO
          (IF (Eq (Index (V aa) (V ii)) (V xx))
            THEN cc ::= (Plus (V cc) (Const ( 1)))
          ELSE SKIP);;
        Return (V cc)
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
        (Indexl (V aa) (Const ( 5))) ::== (Const ( 1));;
        (Indexl (V aa) (Const ( 6))) ::== (Const ( 92));;
        (Indexl (V aa) (Const ( 7))) ::== (Const ( 84));;
        (Indexl (V aa) (Const ( 8))) ::== (Const ( 38));;
        (Indexl (V aa) (Const ( 9))) ::== (Const ( 80));;
        nn ::= (Const ( 10));;

        Callfun foo ''occurs'' [(V aa), (V nn), Const 5];;
        Callfun bar ''occurs'' [(V aa), (V nn), Const 84]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.globals = [aa, nn, foo, bar],
      program.procs = [main_decl, occurs_decl]
    \<rparr>"

export_code p in SML

(* Check if 5 and 84 occur in the array bb1 = 0 (False) bb2 = 1 (True) *)
value "case execute p of Some (_,\<gamma>,\<mu>) \<Rightarrow> (\<gamma> foo, \<gamma> bar,\<mu>)"

end
