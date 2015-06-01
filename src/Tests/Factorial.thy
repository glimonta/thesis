theory Factorial
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

(* Factorial: Takes a number and returns the factorial *)
definition fact_decl :: fun_decl
  where "fact_decl \<equiv> ([nn], [rr, ii],
    rr ::= (Const 1);;
    ii ::= (Const 1);;
    (WHILE (Less (V ii) (Plus (V nn) (Const 1))) DO
      (rr ::= (Mult (V rr) (V ii));;
      ii ::= (Plus (V ii) (Const 1)))
    );;
    Return (V rr))"

definition main_decl :: fun_decl
  where "main_decl \<equiv> ([], [],
    Callfun rr ''fact'' [Const 5])"

definition "main_loc \<equiv> (\<lambda>(_,l,_). l) main_decl"
definition "main_body \<equiv> (\<lambda>(_,_,c). c) main_decl"

definition initial_proc :: program where "initial_proc \<equiv> \<lambda>name. None"

definition proc_table :: program where "proc_table \<equiv> 
  (initial_proc(''main'' := (Some main_decl)))(''fact'' := (Some fact_decl))"

definition initial_glob :: valuation where "initial_glob \<equiv> \<lambda>name. None"
definition initial_mem :: mem where "initial_mem \<equiv> []"
definition initial_stack :: "stack_frame list" where
  "initial_stack \<equiv> [(main_body,map_of (map (\<lambda>x. (x,None)) main_loc),Invalid)]"
definition init_state :: state 
  where "init_state \<equiv> (initial_stack, initial_glob, initial_mem)"

export_code init_state in SML

(* The factorial of the number is on the variable rr *)
value "case interp proc_table init_state of Some (_,\<gamma>,\<mu>) \<Rightarrow> (\<gamma> rr,\<mu>)"

end
