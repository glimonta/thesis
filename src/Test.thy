theory Test
imports SmallStep
begin

definition initial_loc :: loc where "initial_loc \<equiv> \<lambda>name. None"
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
  (Indexl (V pp) (V ii)) ::== (Const (I 0)) ;;
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

definition "bubblesort_test \<equiv>
  aa ::= New (Const (I 10));;
  (Indexl (V aa) (Const (I 0))) ::== (Const (I 44));;
  (Indexl (V aa) (Const (I 1))) ::== (Const (I 98));;
  (Indexl (V aa) (Const (I 2))) ::== (Const (I 60));;
  (Indexl (V aa) (Const (I 3))) ::== (Const (I 26));;
  (Indexl (V aa) (Const (I 4))) ::== (Const (I 54));;
  (Indexl (V aa) (Const (I 5))) ::== (Const (I 1));;
  (Indexl (V aa) (Const (I 6))) ::== (Const (I 92));;
  (Indexl (V aa) (Const (I 7))) ::== (Const (I 84));;
  (Indexl (V aa) (Const (I 8))) ::== (Const (I 38));;
  (Indexl (V aa) (Const (I 9))) ::== (Const (I 80));;

  nn ::= (Const (I 10));;
  tt ::= (Const (I 0));;


  FOR ii FROM (Const (I 1)) TO (V nn) DO
    (FOR jj FROM (Const (I 0)) TO (Plus (V nn) (Const (I -1))) DO
      (IF (Less (Index (V aa) (Plus (V jj) (Const (I 1)))) (Index (V aa) (V jj)))
      THEN (tt ::= (Index (V aa) (V jj));;
        (Indexl (V aa) (V jj)) ::== (Index (V aa) (Plus (V jj) (Const (I 1))));;
        (Indexl (V aa) (Plus (V jj) (Const (I 1)))) ::== (V tt))
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
  aa ::= New (Const (I 10));;
  (Indexl (V aa) (Const (I 0))) ::== (Const (I 44));;
  (Indexl (V aa) (Const (I 1))) ::== (Const (I 98));;
  (Indexl (V aa) (Const (I 2))) ::== (Const (I 60));;
  (Indexl (V aa) (Const (I 3))) ::== (Const (I 26));;
  (Indexl (V aa) (Const (I 4))) ::== (Const (I 54));;
  (Indexl (V aa) (Const (I 5))) ::== (Const (I 1));;
  (Indexl (V aa) (Const (I 6))) ::== (Const (I 92));;
  (Indexl (V aa) (Const (I 7))) ::== (Const (I 84));;
  (Indexl (V aa) (Const (I 8))) ::== (Const (I 38));;
  (Indexl (V aa) (Const (I 9))) ::== (Const (I 80));;

  nn ::= (Const (I 10));; (* Length of array *)
  mm ::= (Index (V aa) (Const (I 0)));; (* Min *)


  FOR ii FROM (Const (I 0)) TO (Plus (V nn) (Const (I -1))) DO
    (IF (Less (Index (V aa) (V ii)) (V mm))
     THEN mm ::= (Index (V aa) (V ii))
     ELSE SKIP)
"

value
  "case interp (min_test, initial_state) of Some (_,(l,_)) \<Rightarrow> (l mm)"

definition "occurs_test x \<equiv>
  aa ::= New (Const (I 10));;
  (Indexl (V aa) (Const (I 0))) ::== (Const (I 44));;
  (Indexl (V aa) (Const (I 1))) ::== (Const (I 98));;
  (Indexl (V aa) (Const (I 2))) ::== (Const (I 60));;
  (Indexl (V aa) (Const (I 3))) ::== (Const (I 26));;
  (Indexl (V aa) (Const (I 4))) ::== (Const (I 54));;
  (Indexl (V aa) (Const (I 5))) ::== (Const (I 1));;
  (Indexl (V aa) (Const (I 6))) ::== (Const (I 92));;
  (Indexl (V aa) (Const (I 7))) ::== (Const (I 84));;
  (Indexl (V aa) (Const (I 8))) ::== (Const (I 38));;
  (Indexl (V aa) (Const (I 9))) ::== (Const (I 80));;

  nn ::= (Const (I 10));; (* Length of array *)
  xx ::= (Const (I x));;
  bb ::= (Const (I 0));; (* Default: False (value does not occur) *)


  FOR ii FROM (Const (I 0)) TO (Plus (V nn) (Const (I -1))) DO
    (IF (Eq (Index (V aa) (V ii)) (V xx))
     THEN bb ::= (Const (I 1))
     ELSE SKIP)
"

(* The element doesn't exist *)
value
  "case interp (occurs_test 5, initial_state) of Some (_,(l,_)) \<Rightarrow> (l bb)"

(* The element exists *)
value
  "case interp (occurs_test 84, initial_state) of Some (_,(l,_)) \<Rightarrow> (l bb)"

definition "count_test x \<equiv>
  bb ::= (Const (I 0));;
  aa ::= New (Const (I 10));;
  (Indexl (V aa) (Const (I 0))) ::== (Const (I 44));;
  (Indexl (V aa) (Const (I 1))) ::== (Const (I 98));;
  (Indexl (V aa) (Const (I 2))) ::== (Const (I 44));;
  (Indexl (V aa) (Const (I 3))) ::== (Const (I 44));;
  (Indexl (V aa) (Const (I 4))) ::== (Const (I 54));;
  (Indexl (V aa) (Const (I 5))) ::== (Const (I 1));;
  (Indexl (V aa) (Const (I 6))) ::== (Const (I 92));;
  (Indexl (V aa) (Const (I 7))) ::== (Const (I 84));;
  (Indexl (V aa) (Const (I 8))) ::== (Const (I 44));;
  (Indexl (V aa) (Const (I 9))) ::== (Const (I 44));;

  nn ::= (Const (I 10));; (* Length of array *)
  xx ::= (Const (I x));;
  cc ::= (Const (I 0));; (* Counter of occurences *)
  dd ::= (Index (V aa) (Const (I 9)));;

  FOR ii FROM (Const (I 0)) TO (V nn) DO
    (IF (Eq (Index (V aa) (V ii)) (V xx))
     THEN cc ::= (Plus (V cc) (Const (I 1)))
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
  aa ::= New (Const (I 10));;
  (Indexl (V aa) (Const (I 0))) ::== (Const (I 44));;
  (Indexl (V aa) (Const (I 1))) ::== (Const (I 98));;
  (Indexl (V aa) (Const (I 2))) ::== (Const (I 60));;
  (Indexl (V aa) (Const (I 3))) ::== (Const (I 26));;
  (Indexl (V aa) (Const (I 4))) ::== (Const (I 54));;
  (Indexl (V aa) (Const (I 5))) ::== (Const (I 1));;
  (Indexl (V aa) (Const (I 6))) ::== (Const (I 92));;
  (Indexl (V aa) (Const (I 7))) ::== (Const (I 84));;
  (Indexl (V aa) (Const (I 8))) ::== (Const (I 38));;
  (Indexl (V aa) (Const (I 9))) ::== (Const (I 80));;

  nn ::= (Const (I 10));;


  FOR ii FROM (Const (I 0)) TO (Plus (V nn) (Const (I -1))) DO
    (mm ::= (Index (V aa) (V ii));; (* Min *)
    tt ::= (V ii);; (* Min index *)
    (FOR jj FROM (Plus (V ii) (Const (I 1))) TO (V nn) DO
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
  ll ::= New (Const (I 1));;
  nn ::= (Const (I n));;

  FOR ii FROM (Const (I 0)) TO (V nn) DO
  (xx ::= New (Const (I 2));;
  (Indexl (V xx) (Const (I 0))) ::== (Const (I 0));;
  (Indexl (V xx) (Const (I 1))) ::== (Deref (V ll));;
  (Derefl (V ll)) ::== (V xx))
"

value
  "case interp (newlist_test 5, initial_state) of Some (_,(l,m)) \<Rightarrow> (l ll, m)"

end
