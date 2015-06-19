theory Test
imports Main "../SmallStep" "../Pretty" "../GraphTest"
begin

abbreviation "aa \<equiv> ''a''"  abbreviation "bb \<equiv> ''b''" abbreviation "cc \<equiv> ''c''"
abbreviation "dd \<equiv> ''d''"  abbreviation "ee \<equiv> ''e''" abbreviation "ff \<equiv> ''f''"
abbreviation "gg \<equiv> ''g''"  abbreviation "hh \<equiv> ''h''" abbreviation "ii \<equiv> ''i''"
abbreviation "jj \<equiv> ''j''"  abbreviation "kk \<equiv> ''k''" abbreviation "ll \<equiv> ''l''"
abbreviation "mm \<equiv> ''m''"  abbreviation "nn \<equiv> ''n''" abbreviation "oo \<equiv> ''o''"
abbreviation "pp \<equiv> ''p''"  abbreviation "qq \<equiv> ''q''" abbreviation "rr \<equiv> ''r''"
abbreviation "ss \<equiv> ''s''"  abbreviation "tt \<equiv> ''t''" abbreviation "uu \<equiv> ''u''"
abbreviation "vv \<equiv> ''v''"  abbreviation "ww \<equiv> ''w''" abbreviation "xx \<equiv> ''x''"
abbreviation "yy \<equiv> ''y''"  abbreviation "zz \<equiv> ''z''"

abbreviation "foo \<equiv> ''foo''" abbreviation "bar \<equiv> ''bar''" abbreviation "baz \<equiv> ''baz''"

text {* A convenient loop construct: *}

abbreviation For :: "vname \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> com \<Rightarrow> com"
  ("(FOR _/ FROM _/ TO _/ DO _)"  [0, 0, 0, 61] 61) where
  "FOR v FROM a1 TO a2 DO c \<equiv>
     v ::= a1 ;;  WHILE (Less (V v) a2) DO (c ;; v ::= Plus (V v) (Const (1)))"

term remdups

definition "execute_show vnames p \<equiv> case execute p of
  Some s \<Rightarrow> show_state (program.globals p @ (remdups (collect_locals (program.procs p))) @ vnames) s
  | None \<Rightarrow> show ''<Error>''"

fun get_value_node :: "node list_graph \<Rightarrow> addr \<Rightarrow> val" where
  "get_value_node graph addr = (case (lookup_node addr (nodesL graph)) of
(* Node in memory doesn't exist, probably already deallocated, in this case, this
  would be an error, there would be no program to test because it wouldn't have
  been generated in the first place *)
            None \<Rightarrow> NullVal |
            Some node \<Rightarrow> (case (node.content node) of
              Val i \<Rightarrow> I i |
(* This would be an error, there would be no program to test because it wouldn't have
  been generated in the first place *)
              U \<Rightarrow> NullVal | 
              P addr \<Rightarrow> A addr |
(* This would be an error, there would be no program to test because it wouldn't have
  been generated in the first place *)
              InvalidP \<Rightarrow> NullVal))"

fun is_addr :: "(nat \<times> val) \<Rightarrow> bool" where
  "is_addr (_, (A _)) = True"
| "is_addr (_, _) = False"

lemma is_addr_addr[simp]:
  assumes "is_addr (n, v)"
  shows "\<exists>addr. v = A addr"
  proof (cases v)
    case NullVal
      hence "is_addr (n, v) \<equiv> False" using is_addr_def by auto
      hence "False" using `is_addr (n,v)` by blast
      thus ?thesis by simp
  next
    case (I i)
      hence "is_addr (n, v) \<equiv> False" using is_addr_def by auto
      hence "False" using `is_addr (n,v)` by blast
      thus ?thesis by simp
  next
    case (A addr)
      thus ?thesis by simp
qed

(* n is how nested the actual value is, how many pointers must be followed in order to get to the value *)
fun follow_object_graph :: "nat \<Rightarrow> addr \<Rightarrow> node list_graph \<Rightarrow> (nat \<times> val)" where
  "follow_object_graph n addr graph = (while
    (is_addr)
    (\<lambda>(n, A addr) \<Rightarrow> (n+1, get_value_node graph addr))
    (n, get_value_node graph addr))"

value "shows_graph memory_graph ''''"
definition "test \<equiv> (construct_graph [None, Some [(Some (A (2,0))), Some (A (2,1))], Some [(Some (A (1,1))), Some (I 4), None]])"
value "follow_object_graph 0 (1,0) test"

fun follow_pointer :: "nat \<Rightarrow> exp \<Rightarrow> exp" where
  "follow_pointer 0 e = e"
| "follow_pointer n e = follow_pointer (n-1) (Deref e)"

fun generate_test :: "exp \<Rightarrow> val \<Rightarrow> node list_graph \<Rightarrow> com" where
  "generate_test x value graph =
      (case value of 
        NullVal \<Rightarrow>
          IF (Eq x (Null))
          THEN
            (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
            ''passed'' ::= (Plus (V ''passed'') (Const 1)))
          ELSE
            (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
            ''failed'' ::= (Plus (V ''failed'') (Const 1))) |
        I i \<Rightarrow>
          IF (Eq x (Const i))
          THEN
            (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
            ''passed'' ::= (Plus (V ''passed'') (Const 1)))
          ELSE
            (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
            ''failed'' ::= (Plus (V ''failed'') (Const 1))) |
        A addr \<Rightarrow>
          let
            (n, v) = follow_object_graph 0 addr graph;
            lval = follow_pointer n (Deref x)
          in
            (case v of
              (I i) \<Rightarrow>
                IF (Eq lval (Const i))
                THEN
                  (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
                  ''passed'' ::= (Plus (V ''passed'') (Const 1)))
                ELSE
                  (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
                  ''failed'' ::= (Plus (V ''failed'') (Const 1))) |
              _ \<Rightarrow> SKIP (* Should never happen *)
            )
      )"

(* vname list and val list must have the same length *)
fun generate_tests :: "exp list \<Rightarrow> val list \<Rightarrow> node list_graph \<Rightarrow> com" where
  "generate_tests [] [] graph = SKIP"
| "generate_tests (x#xs) (y#ys) graph = generate_test x y graph;; generate_tests xs ys graph"

(* vname list and val list must have the same length *)
fun generate_test_function :: "exp list \<Rightarrow> val list \<Rightarrow> node list_graph \<Rightarrow> fun_decl" where
  "generate_test_function x y graph= 
    \<lparr> fun_decl.name = ''test'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = generate_tests x y graph
    \<rparr>"

end