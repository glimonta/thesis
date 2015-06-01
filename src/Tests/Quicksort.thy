theory Quicksort
imports "../SmallStep"
begin

abbreviation "aa \<equiv> ''a''"  abbreviation "bb \<equiv> ''b''" abbreviation "cc \<equiv> ''c''"
abbreviation "dd \<equiv> ''d''"  abbreviation "ee \<equiv> ''d''" abbreviation "ff \<equiv> ''f''"
abbreviation "gg \<equiv> ''g''"  abbreviation "hh \<equiv> ''h''" abbreviation "ii \<equiv> ''i''"
abbreviation "jj \<equiv> ''j''"  abbreviation "kk \<equiv> ''k''" abbreviation "ll \<equiv> ''l''"
abbreviation "mm \<equiv> ''m''"  abbreviation "nn \<equiv> ''n''" abbreviation "oo \<equiv> ''o''"
abbreviation "pp \<equiv> ''p''"  abbreviation "qq \<equiv> ''q''" abbreviation "rr \<equiv> ''r''"
abbreviation "ss \<equiv> ''s''"  abbreviation "tt \<equiv> ''t''" abbreviation "uu \<equiv> ''u''"
abbreviation "vv \<equiv> ''v''"  abbreviation "ww \<equiv> ''w''" abbreviation "xx \<equiv> ''x''"
abbreviation "yy \<equiv> ''y''"  abbreviation "zz \<equiv> ''z''"

(* Swap: swaps two elements in an array, takes the address of the first element xx and the second 
   element yy and swaps their contents *)
definition swap_decl :: fun_decl
  where "swap_decl \<equiv> ([xx, yy],  [tt],
    tt ::= Deref (V xx);;
    (Derefl (V xx)) ::== (Deref (V yy));;
    (Derefl (V yy)) ::== (V tt);;
    Return (V tt)
)"

(* Quicksort: Takes an array a and its length n and returns the sorted array *)
definition quicksort_decl :: fun_decl
  where "quicksort_decl \<equiv> ([aa, ss, ee], [ll, rr, pp, bb], 
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
    )"

definition main_decl :: fun_decl
  where "main_decl \<equiv> ([], [],
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
    Callfun bb ''quicksort'' [(V aa), (Const 0), Plus (V nn) (Const (- 1))])"

definition "main_loc \<equiv> (\<lambda>(_,l,_). l) main_decl"
definition "main_body \<equiv> (\<lambda>(_,_,c). c) main_decl"

definition initial_proc :: program where "initial_proc \<equiv> \<lambda>name. None"

definition proc_table :: program where "proc_table \<equiv> 
  ((initial_proc(''main'' := (Some main_decl)))(''quicksort'' := (Some quicksort_decl)))(''swap'' := (Some swap_decl))"

definition initial_glob :: valuation where "initial_glob \<equiv> \<lambda>name. None"
definition initial_mem :: mem where "initial_mem \<equiv> []"
definition initial_stack :: "stack_frame list" where
  "initial_stack \<equiv> [(main_body,map_of (map (\<lambda>x. (x,None)) main_loc),Invalid)]"
definition init_state :: state 
  where "init_state \<equiv> (initial_stack, initial_glob, initial_mem)"

export_code init_state in SML

value "interp proc_table init_state"

(* The sorted array should be stored in the address indicated by both aa and bb *)
value "case interp proc_table init_state of Some (_,\<gamma>,\<mu>) \<Rightarrow> (\<gamma> bb,\<mu>)"

end
