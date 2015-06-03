theory Quicksort
imports "../SmallStep" Test
begin

(* Swap: swaps two elements in an array, takes the address of the first element xx and the second 
   element yy and swaps their contents *)
definition swap_decl :: fun_decl
  where "swap_decl \<equiv> 
    \<lparr> fun_decl.name = ''swap'',
      fun_decl.params = [xx, yy],
      fun_decl.locals = [tt],
      fun_decl.body = 
        tt ::= Deref (V xx);;
        (Derefl (V xx)) ::== (Deref (V yy));;
        (Derefl (V yy)) ::== (V tt);;
        Return (V tt)
    \<rparr>"

(* Quicksort: Takes an array a and its length n and returns the sorted array *)
definition quicksort_decl :: fun_decl
  where "quicksort_decl \<equiv> 
    \<lparr> fun_decl.name = ''quicksort'',
      fun_decl.params = [aa, ss, ee],
      fun_decl.locals = [ll, rr, pp, bb],
      fun_decl.body = 
        IF (Less (V ss) (V ee)) THEN
          (ll ::= (Plus (V ss) (Const 1));;
          rr ::= V ee;;
          pp ::= (Index (V aa) (V ss));;
          (WHILE (Less (V ll) (V rr)) DO (
            (IF (Less (Index (V aa) (V ll)) (Plus (V pp) (Const 1))) THEN
              ll ::= (Plus (V ll) (Const 1))
            ELSE
              (IF (Less (V pp) (Index (V aa) (V rr))) THEN
                rr ::= (Plus (V rr) (Const (- 1)))
              ELSE 
                Callfun bb ''swap'' [(Ref (Indexl (V aa) (V ll))), (Ref (Indexl (V aa) (V rr)))]
              )
            )
          ));;
          (IF (Less (Index (V aa) (V ll)) (V pp)) THEN
            (Callfun bb ''swap'' [(Ref (Indexl (V aa) (V ll))), (Ref (Indexl (V aa) (V ss)))];;
            ll ::= (Plus (V ll) (Const (- 1))))
          ELSE
            (ll ::= (Plus (V ll) (Const (- 1)));;
            (Callfun bb ''swap'' [(Ref (Indexl (V aa) (V ll))), (Ref (Indexl (V aa) (V ss)))]))
          );;
          Callfun bb ''quicksort'' [V aa, V ss, V ll];;
          Callfun bb ''quicksort'' [V aa, V rr, V ee]
          );;
          Return (V aa)
        ELSE
          Return (V aa)
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv> 
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= New (Const ( 10));;
        (Indexl (V aa) (Const ( 0))) ::== (Const (  4));;
        (Indexl (V aa) (Const ( 1))) ::== (Const ( 65));;
        (Indexl (V aa) (Const ( 2))) ::== (Const (  2));;
        (Indexl (V aa) (Const ( 3))) ::== (Const ( 31));;
        (Indexl (V aa) (Const ( 4))) ::== (Const (  0));;
        (Indexl (V aa) (Const ( 5))) ::== (Const ( 99));;
        (Indexl (V aa) (Const ( 6))) ::== (Const ( 92));;
        (Indexl (V aa) (Const ( 7))) ::== (Const ( 83));;
        (Indexl (V aa) (Const ( 8))) ::== (Const (782));;
        (Indexl (V aa) (Const ( 9))) ::== (Const (  1));;
        nn ::= (Const ( 10));;
        Callfun bb ''quicksort'' [(V aa), (Const 0), Plus (V nn) (Const (- 1))]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.globals = [aa, nn, bb],
      program.procs = [main_decl, quicksort_decl, swap_decl]
    \<rparr>"

export_code p in SML

(* The sorted array should be stored in the address indicated by both aa and bb *)
value "case execute p of Some (_,\<gamma>,\<mu>) \<Rightarrow> (\<gamma> bb,\<mu>)"

end
