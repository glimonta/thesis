theory StrLength
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


(* Definition for main procedure *)

(* Takes a number n and returns an array of length n + 1 initialized with numbers from 1 to n in
  its [0,n] positions *)
definition create_array_decl :: fun_decl
  where "create_array_decl \<equiv> ([nn], [],
    pp ::= New (Plus (V nn) (Const (1)));; ii ::= Const (0);;
    WHILE (Less (V ii) (V nn)) DO (
      (Indexl (V pp) (V ii)) ::== (Plus (V ii) (Const (1)));;
      ii ::= Plus (V ii) (Const (1))
      );;
    (Indexl (V pp) (V ii)) ::== (Const ( 0)) ;;
    Return (V pp))"

(* Strlength: Takes an array (ending in 0) and returns the length of the array *)
definition str_len_decl :: fun_decl
  where "str_len_decl \<equiv> ([aa], [pp, ll],
  pp ::= (V aa);;
  ll ::= Const ( 0);;
  WHILE (Deref (V pp)) DO (
    ll ::= Plus (V ll) (Const ( 1));;
    pp ::= Plus (V pp) (Const ( 1))
    );;
  Return (V ll))"


definition main_decl :: fun_decl
  where "main_decl \<equiv> ([], [], Callfun aa ''create_array'' [(Const 5)];;
    Callfun ll ''str_len'' [V aa])"

definition "main_loc \<equiv> (\<lambda>(_,l,_). l) main_decl"
definition "main_body \<equiv> (\<lambda>(_,_,c). c) main_decl"

definition initial_proc :: program where "initial_proc \<equiv> \<lambda>name. None"

definition proc_table :: program where "proc_table \<equiv> 
  ((initial_proc(''main'' := (Some main_decl)))(''create_array'' := (Some create_array_decl)))(''str_len'' := (Some str_len_decl))"

definition initial_glob :: valuation where "initial_glob \<equiv> \<lambda>name. None"
definition initial_mem :: mem where "initial_mem \<equiv> []"
definition initial_stack :: "stack_frame list" where
  "initial_stack \<equiv> [(main_body,map_of (map (\<lambda>x. (x,None)) main_loc),Invalid)]"
definition init_state :: state 
  where "init_state \<equiv> (initial_stack, initial_glob, initial_mem)"

export_code init_state in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "case interp proc_table init_state of Some (_,\<gamma>,\<mu>) \<Rightarrow> \<gamma> ll"

end
