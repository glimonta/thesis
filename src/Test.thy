theory Test
imports SmallStep
begin

definition initial_loc :: valuation where "initial_loc \<equiv> \<lambda>name. None"
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
     v ::= a1 ;;  WHILE (Less (V v) a2) DO (c ;; v ::= Plus (V v) (Const (1)))"

definition "test1 c \<equiv>
  pp ::= New (Plus (Const (c)) (Const (1)));;
  ii ::= Const ( 0);;
  WHILE (Less (V ii) (Const (c))) DO (
    (Indexl (V pp) (V ii)) ::== (Plus (V ii) (Const (1)));;
    ii ::= Plus (V ii) (Const (1))
  );;
  (Indexl (V pp) (V ii)) ::== (Const ( 0)) ;;
  ll ::= Const ( 0)
  ;;
  WHILE (Deref (V pp)) DO (
    ll ::= Plus (V ll) (Const ( 1));;
    pp ::= Plus (V pp) (Const ( 1))
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
  cc ::= (Plus (Const ( a)) (Const ( b)))"

definition "add_test' \<equiv> add_test 1 2"

value
  "case interp (add_test 1 2, initial_state) of Some (_,(l,_)) \<Rightarrow> l cc"

(* I need multiplication for this *)

definition "factorial_test n \<equiv>
  nn ::= (Const ( n));;
  ff ::= (Const ( 1));;
  cc ::= (Const ( 1));;
  FOR cc FROM (Const ( 1)) TO (V nn) DO
  SKIP
"

definition "bubblesort_test \<equiv>
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
  tt ::= (Const ( 0));;


  FOR ii FROM (Const ( 1)) TO (V nn) DO
    (FOR jj FROM (Const ( 0)) TO (Plus (V nn) (Const ( -1))) DO
      (IF (Less (Index (V aa) (Plus (V jj) (Const ( 1)))) (Index (V aa) (V jj)))
      THEN (tt ::= (Index (V aa) (V jj));;
        (Indexl (V aa) (V jj)) ::== (Index (V aa) (Plus (V jj) (Const ( 1))));;
        (Indexl (V aa) (Plus (V jj) (Const ( 1)))) ::== (V tt))
      ELSE SKIP))
"

value
  "case interp (bubblesort_test, initial_state) of Some (_,(l,m)) \<Rightarrow> (l aa, m)"

ML {*

val interp = @{code interp}

  val s = (@{code bubblesort_test}, @{code initial_state});
  val step = @{code fstep};

  val SOME (_,(l,m)) = interp s
val r = l [#"a"]
val r2 = hd m
*}

definition "min_test \<equiv>
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

  nn ::= (Const ( 10));; (* Length of array *)
  mm ::= (Index (V aa) (Const ( 0)));; (* Min *)


  FOR ii FROM (Const ( 0)) TO (Plus (V nn) (Const ( -1))) DO
    (IF (Less (Index (V aa) (V ii)) (V mm))
     THEN mm ::= (Index (V aa) (V ii))
     ELSE SKIP)
"

value
  "case interp (min_test, initial_state) of Some (_,(l,_)) \<Rightarrow> (l mm)"

definition "occurs_test x \<equiv>
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

  nn ::= (Const ( 10));; (* Length of array *)
  xx ::= (Const ( x));;
  bb ::= (Const ( 0));; (* Default: False (value does not occur) *)


  FOR ii FROM (Const ( 0)) TO (Plus (V nn) (Const ( -1))) DO
    (IF (Eq (Index (V aa) (V ii)) (V xx))
     THEN bb ::= (Const ( 1))
     ELSE SKIP)
"

(* The element doesn't exist *)
value
  "case interp (occurs_test 5, initial_state) of Some (_,(l,_)) \<Rightarrow> (l bb)"

(* The element exists *)
value
  "case interp (occurs_test 84, initial_state) of Some (_,(l,_)) \<Rightarrow> (l bb)"

definition "count_test x \<equiv>
  bb ::= (Const ( 0));;
  aa ::= New (Const ( 10));;
  (Indexl (V aa) (Const ( 0))) ::== (Const ( 44));;
  (Indexl (V aa) (Const ( 1))) ::== (Const ( 98));;
  (Indexl (V aa) (Const ( 2))) ::== (Const ( 44));;
  (Indexl (V aa) (Const ( 3))) ::== (Const ( 44));;
  (Indexl (V aa) (Const ( 4))) ::== (Const ( 54));;
  (Indexl (V aa) (Const ( 5))) ::== (Const ( 1));;
  (Indexl (V aa) (Const ( 6))) ::== (Const ( 92));;
  (Indexl (V aa) (Const ( 7))) ::== (Const ( 84));;
  (Indexl (V aa) (Const ( 8))) ::== (Const ( 44));;
  (Indexl (V aa) (Const ( 9))) ::== (Const ( 44));;

  nn ::= (Const ( 10));; (* Length of array *)
  xx ::= (Const ( x));;
  cc ::= (Const ( 0));; (* Counter of occurences *)
  dd ::= (Index (V aa) (Const ( 9)));;

  FOR ii FROM (Const ( 0)) TO (V nn) DO
    (IF (Eq (Index (V aa) (V ii)) (V xx))
     THEN cc ::= (Plus (V cc) (Const ( 1)))
     ELSE SKIP)
"

(* The element doesn't exist *)
value
  "case interp (count_test 5, initial_state) of Some (_,(l,_)) \<Rightarrow> (l cc)"

(* The element exists once *)
value
  "case interp (count_test 84, initial_state) of Some (_,(l,_)) \<Rightarrow> (l cc)"

(* The element exists more than once *)
value
  "case interp (count_test 44, initial_state) of Some (_,(l,_)) \<Rightarrow> (l cc)"

definition "selectionsort_test \<equiv>
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


  FOR ii FROM (Const ( 0)) TO (Plus (V nn) (Const ( -1))) DO
    (mm ::= (Index (V aa) (V ii));; (* Min *)
    tt ::= (V ii);; (* Min index *)
    (FOR jj FROM (Plus (V ii) (Const ( 1))) TO (V nn) DO
      (IF (Less (Index (V aa) (V jj)) (V mm))
      THEN 
        mm ::= (Index (V aa) (V jj));;
        tt ::= (V jj)
      ELSE SKIP));;
    (Indexl (V aa) (V tt)) ::== (Index (V aa) (V ii));;
    (Indexl (V aa) (V ii)) ::== (V mm))
"

value
  "case interp (selectionsort_test, initial_state) of Some (_,(l,m)) \<Rightarrow> (l aa, m)"

(* Creates a new list of size n initialized in zeros *)
definition "newlist_test n \<equiv>
  ll ::= New (Const ( 1));;
  nn ::= (Const ( n));;

  FOR ii FROM (Const ( 0)) TO (V nn) DO
  (xx ::= New (Const ( 2));;
  (Indexl (V xx) (Const ( 0))) ::== (Const ( 0));;
  (Indexl (V xx) (Const ( 1))) ::== (Deref (V ll));;
  (Derefl (V ll)) ::== (V xx))
"

value
  "case interp (newlist_test 5, initial_state) of Some (_,(l,m)) \<Rightarrow> (l ll, m)"

end
