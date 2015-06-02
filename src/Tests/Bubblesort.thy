theory Bubblesort
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

text {* A convenient loop construct: *}

abbreviation For :: "vname \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> com \<Rightarrow> com"
  ("(FOR _/ FROM _/ TO _/ DO _)"  [0, 0, 0, 61] 61) where
  "FOR v FROM a1 TO a2 DO c \<equiv>
     v ::= a1 ;;  WHILE (Less (V v) a2) DO (c ;; v ::= Plus (V v) (Const (1)))"

(* Bubblesort: Takes an array a and its length n and returns the sorted array *)
definition bubblesort_decl :: fun_decl
  where "bubblesort_decl \<equiv> ([aa, nn], [ii,jj, tt],
      tt ::= Const 0;;
      FOR ii FROM (Const 1) TO (V nn) DO
        (FOR jj FROM (Const ( 0)) TO (Plus (V nn) (Const ( -1))) DO
          (IF (Less (Index (V aa) (Plus (V jj) (Const ( 1)))) (Index (V aa) (V jj)))
          THEN (tt ::= (Index (V aa) (V jj));;
            (Indexl (V aa) (V jj)) ::== (Index (V aa) (Plus (V jj) (Const ( 1))));;
            (Indexl (V aa) (Plus (V jj) (Const ( 1)))) ::== (V tt))
          ELSE SKIP));;
      Return (V aa))"

definition main_decl :: fun_decl
  where "main_decl \<equiv> ([], [],
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
    Callfun bb ''bubblesort'' [(V aa), (V nn)])"

definition "main_loc \<equiv> (\<lambda>(_,l,_). l) main_decl"
definition "main_body \<equiv> (\<lambda>(_,_,c). c) main_decl"

definition initial_proc :: program where "initial_proc \<equiv> \<lambda>name. None"

definition proc_table :: program where "proc_table \<equiv> 
  (initial_proc(''main'' := (Some main_decl)))(''bubblesort'' := (Some bubblesort_decl))"

definition initial_glob :: valuation where "initial_glob \<equiv> \<lambda>name. None"
definition initial_mem :: mem where "initial_mem \<equiv> []"
definition initial_stack :: "stack_frame list" where
  "initial_stack \<equiv> [(main_body,map_of (map (\<lambda>x. (x,None)) main_loc),Invalid)]"
definition init_state :: state 
  where "init_state \<equiv> (initial_stack, initial_glob, initial_mem)"

export_code init_state in SML

value "case
  (fstep proc_table 
  (the (fstep proc_table 
  (the (fstep proc_table 
  (the (fstep proc_table 
  (the (fstep proc_table 
  init_state)))))))))
  of Some (\<sigma>,\<gamma>,\<mu>) \<Rightarrow> (fst (snd (hd \<sigma>)) tt, fst (snd (hd \<sigma>)) ii, fst (snd (hd \<sigma>)) jj, \<mu>)"



(* The length of the string should be 5 and be saved in global variable ll *)
value "case interp proc_table init_state of Some (_,\<gamma>,\<mu>) \<Rightarrow> (\<gamma> bb,\<mu>)"

end
