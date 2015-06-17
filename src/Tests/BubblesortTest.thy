theory BubblesortTest
imports "../SmallStep" "Bubblesort" "../GraphTest"
begin

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

lemma follow_object_graph_unfold: "follow_object_graph n addr graph = (
  if is_addr(n, A addr) then
      let (n, v) = (n+1, get_value_node graph addr)
      in (case v of (A addr) \<Rightarrow> follow_object_graph n addr graph)
  else
    (n, get_value_node graph addr)
)"
  proof (cases "lookup_node addr (nodesL graph)")
  apply (subst while_unfold)
  apply (auto split: Option.bind_split)
  apply (subst while_unfold)
  apply auto
  done
oops

lemma interp_term: "is_term (Some cs) \<Longrightarrow> interp proc_table cs = Some cs"
  apply (subst interp_unfold)
  by simp

value "shows_graph memory_graph ''''"
definition "test \<equiv> (construct_graph [None, Some [(Some (A (2,0))), Some (A (2,1))], Some [(Some (A (1,1))), Some (I 4), None]])"
value "follow_object_graph 0 (1,0) test"

fun follow_pointer :: "nat \<Rightarrow> exp \<Rightarrow> exp" where
  "follow_pointer 0 e = e"
| "follow_pointer n e = follow_pointer (n-1) (Deref e)"

fun generate_test :: "vname \<Rightarrow> val \<Rightarrow> node list_graph \<Rightarrow> com" where
  "generate_test x value graph =
      (case value of 
        NullVal \<Rightarrow>
          IF (Eq (V x) (Null))
          THEN
            (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
            ''passed'' ::= (Plus (V ''passed'') (Const 1)))
          ELSE
            (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
            ''failed'' ::= (Plus (V ''failed'') (Const 1))) |
        I i \<Rightarrow>
          IF (Eq (V x) (Const i))
          THEN
            (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
            ''passed'' ::= (Plus (V ''passed'') (Const 1)))
          ELSE
            (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
            ''failed'' ::= (Plus (V ''failed'') (Const 1))) |
        A addr \<Rightarrow>
          let
            (n, v) = follow_object_graph 0 addr graph;
            lval = follow_pointer n (Deref (V x))
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
fun generate_tests :: "vname list \<Rightarrow> val list \<Rightarrow> node list_graph \<Rightarrow> com" where
  "generate_tests [] [] graph = SKIP"
| "generate_tests (x#xs) (y#ys) graph = generate_test x y graph;; generate_tests xs ys graph"

(* vname list and val list must have the same length *)
fun generate_test_function :: "vname list \<Rightarrow> val list \<Rightarrow> node list_graph \<Rightarrow> fun_decl" where
  "generate_test_function x y graph= 
    \<lparr> fun_decl.name = ''test'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = generate_tests x y graph
    \<rparr>"

definition "bubblesort_graph \<equiv> case execute p of Some (_,_,\<mu>) \<Rightarrow> construct_graph \<mu>"

definition test_decl :: fun_decl
  where "test_decl \<equiv> generate_test_function [aa] [I (-26)] bubblesort_graph"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
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
        Callfunv ''bubblesort'' [(V aa), (V nn)];;
        ''num_tests'' ::= Const 0;;
        ''passed'' ::= Const 0;;
        ''failed'' ::= Const 0;;
        Callfunv ''test'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''bubblesort'',
      program.globals = [aa, nn, ''num_tests'', ''passed'', ''failed''],
      program.procs = [bubblesort_decl, test_decl, main_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p"

definition "bleh \<equiv> case execute p of Some (_,_,\<mu>) \<Rightarrow> shows_graph (construct_graph \<mu>) ''''"

definition "bubblesort_test_exec \<equiv> execute_show [] p"

definition "bubblesort_test \<equiv> (
  shows_prog p ''''
)"

ML_val {*
  val str = @{code bubblesort_test} |> String.implode;
  writeln str;

  val mem = @{code bleh} |> String.implode |> writeln;

  val os = TextIO.openOut "/home/gabriela/Documents/thesis/src/TestC/bubblesort.c";
  TextIO.output (os, str);
  TextIO.flushOut os;
  TextIO.closeOut os;

  val res = @{code bubblesort_test_exec} |> String.implode;
  writeln res;


*}


end