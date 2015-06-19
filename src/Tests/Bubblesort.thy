theory Bubblesort
imports "../SmallStep" "Test" "../Test_Harness"
begin

(* Bubblesort: Takes an array a and its length n and returns the sorted array *)
definition bubblesort_decl :: fun_decl
  where "bubblesort_decl \<equiv>
    \<lparr> fun_decl.name = ''bubblesort'',
      fun_decl.params = [aa, nn],
      fun_decl.locals = [ii,jj, tt],
      fun_decl.body = 
        tt ::= Const 0;;
        FOR ii FROM (Const 1) TO (V nn) DO
          (FOR jj FROM (Const ( 0)) TO (Plus (V nn) (Const ( -1))) DO
            (IF (Less (Index (V aa) (Plus (V jj) (Const ( 1)))) (Index (V aa) (V jj)))
            THEN (tt ::= (Index (V aa) (V jj));;
              (Indexl (V aa) (V jj)) ::== (Index (V aa) (Plus (V jj) (Const ( 1))));;
              (Indexl (V aa) (Plus (V jj) (Const ( 1)))) ::== (V tt))
            ELSE SKIP))
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= New (Const ( 10));;
        xx ::= New (Const ( 3));;
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
        ''failed'' ::= Const 0
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''bubblesort'',
      program.globals = [aa, nn, xx, ''num_tests'', ''passed'', ''failed''],
      program.procs = [bubblesort_decl, main_decl]
    \<rparr>"

export_code p in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p"

definition "blah \<equiv> case execute p of Some (_,_,\<mu>) \<Rightarrow> shows_graph (construct_graph \<mu>) ''''"
value "case execute p of Some (_,_,\<mu>) \<Rightarrow> shows_graph (construct_graph \<mu>) ''''"

definition "bubblesort_exec \<equiv> execute_show [] p"

definition "bubblesort \<equiv> (
  shows_prog p ''''
)"

definition "bubblesort_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests '''';
  let instrs = tests_instructions tests '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code bubblesort_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code bubblesort} "../TestC" "bubblesort"\<close>


(*ML_val {*
  let 
    val thy = @{theory}
  
    val str = @{code bubblesort} |> String.implode;
    val _ = writeln str;
  
    val base_path = Resources.master_directory thy
    val rel_path = "../TestC/bubblesort.c"
    val rel_path = Path.explode rel_path
  
    val abs_path = Path.append base_path rel_path
    val abs_path = Path.implode abs_path
  
    val os = TextIO.openOut abs_path;
    val _ = TextIO.output (os, str);
    val _ = TextIO.flushOut os;
    val _ = TextIO.closeOut os;
  
    val res = @{code bubblesort_exec} |> String.implode;
    val _ = writeln res;
  in () end  
*}*)


end
