theory Test
imports SmallStep
begin


definition "uninit name \<equiv> Code.abort (STR ''Uninitialized variable'') (\<lambda>_. undefined name)"

definition initial_loc :: loc where "initial_loc \<equiv> \<lambda>name. uninit name"
definition initial_mem :: mem where "initial_mem \<equiv> []"
definition initial_state :: state where "initial_state \<equiv> (initial_loc, initial_mem)"

export_code initial_state in SML

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
     v ::= a1 ;;  WHILE (Less (V v) a2) DO (c ;; v ::= Plus (V v) (Const (I 1)))"

definition "test1 c \<equiv>
  pp ::= New (Plus (Const (I c)) (Const (I 1)));;
  ii ::= Const (I 0);;
  WHILE (Less (V ii) (Const (I c))) DO (
    (Indexl (V pp) (V ii)) ::== (Plus (V ii) (Const (I 1)));;
    ii ::= Plus (V ii) (Const (I 1))
  );;
  ll ::= Const (I 0)
  ;;
  WHILE (Deref (V pp)) DO (
    ll ::= Plus (V ll) (Const (I 1));;
    pp ::= Plus (V pp) (Const (I 1))
  )"

definition "test1' \<equiv> test1 5"

ML_val {*

  val interp = @{code interp}

  val s = (@{code test1'}, @{code initial_state});
  val step = @{code fstep};

  val SOME (_,(l,m)) = interp s
  val r = l [#"l"]
*}


value 
  "case interp (test1 5, initial_state) of Some (_,(l,_)) \<Rightarrow> l ''l''"

definition "add_test a b \<equiv>
  cc ::= (Plus (Const (I a)) (Const (I b)))"

definition "add_test' \<equiv> add_test 1 2"

value 
  "case interp (add_test 1 2, initial_state) of Some (_,(l,_)) \<Rightarrow> l cc"

(* I need multiplication for this *)

definition "factorial_test n \<equiv>
  nn ::= (Const (I n));;
  ff ::= (Const (I 1));;
  cc ::= (Const (I 1));;
  FOR cc FROM (Const (I 1)) TO (V nn) DO
  SKIP
"

end
