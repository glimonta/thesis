theory BubblesortTest
imports "../SmallStep" "Bubblesort"
begin

definition "bubblesort_graph \<equiv> case execute p of Some (_,_,\<mu>) \<Rightarrow> construct_graph \<mu>"

value "generate_tests [(Index (V aa) (Const 0))] [I (-26)] bubblesort_graph"

definition test_decl :: fun_decl
  where "test_decl \<equiv>
    generate_test_function
      [(Index (V aa) (Const 0)), (Index (V aa) (Const 1)), (Index (V aa) (Const 2)),
      (Index (V aa) (Const 3)), (Index (V aa) (Const 4)), (Index (V aa) (Const 5)),
      (Index (V aa) (Const 6)), (Index (V aa) (Const 7)), (Index (V aa) (Const 8)),
      (Index (V aa) (Const 9))]
      [I (-26), I 1, I 1, I 38, I 44, I 54, I 60, I 80, I 84, I 92]
      bubblesort_graph"

value "shows_fun_decl test_decl ''''"

definition test_decl' :: fun_decl
  where "test_decl' \<equiv> \<lparr> fun_decl.name = ''tests'',
    fun_decl.params = [],
    fun_decl.locals = [],  
    fun_decl.body =
      IF (Eq (Index (V aa) (Const 0)) (Const (-26)))
      THEN
        (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
        ''passed'' ::= (Plus (V ''passed'') (Const 1)))
      ELSE
        (''num_tests'' ::= (Plus (V ''num_tests'') (Const 1));;
          ''failed'' ::= (Plus (V ''failed'') (Const 1)))\<rparr>"

value "shows_fun_decl test_decl' ''''"

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
value "execute_show [] p'"

definition "bleh \<equiv> case execute p' of Some (_,_,\<mu>) \<Rightarrow> shows_graph (construct_graph \<mu>) ''''"

definition "bubblesort_test_exec \<equiv> execute_show [] p'"

definition "bubblesort_test \<equiv> (
  shows_prog p' ''''
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