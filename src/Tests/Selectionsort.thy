theory Selectionsort
imports "../SmallStep" "../Test" "../Test_Harness"
begin

(* Selectionsort: Takes an array a and its length n and returns the sorted array *)
definition selection_decl :: fun_decl
  where "selection_decl \<equiv> 
    \<lparr> fun_decl.name = ''selection'',
      fun_decl.params = [aa, nn],
      fun_decl.locals = [ii, mm, tt, jj],
      fun_decl.body = 
        FOR ii FROM (Const ( 0)) TO (Plus (V nn) (Const ( -1))) DO
          (mm ::= (Index (V aa) (V ii));; (* Min *)
          tt ::= (V ii);; (* Min index *)
          (FOR jj FROM (Plus (V ii) (Const ( 1))) TO (V nn) DO
            (IF (Less (Index (V aa) (V jj)) (V mm)) THEN
              mm ::= (Index (V aa) (V jj));;
              tt ::= (V jj)
            ELSE SKIP));;
          (Indexl (V aa) (V tt)) ::== (Index (V aa) (V ii));;
          (Indexl (V aa) (V ii)) ::== (V mm))
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv> 
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
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
        Callfunv ''selection'' [(V aa), (V nn)]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''selection'',
      program.globals = [aa, nn],
      program.procs = [selection_decl, main_decl]
    \<rparr>"

export_code p in SML

(* The sorted array should be stored in the address indicated by both aa and bb *)
value "execute_show [] p"

definition "selection_exec \<equiv> execute_show [] p"

definition "selection \<equiv> (
  shows_prog p ''''
)"

definition "selection_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code selection_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code selection} @{code selection_exec} "../TestC" "selection"\<close>

end
