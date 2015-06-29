theory Count
imports "../SmallStep" "../Test" "../Test_Harness"
begin

(* Count: Takes an array a, its length n and an element x, returns the number of occurences of e
    in a. *)
definition count_decl :: fun_decl
  where "count_decl \<equiv>
    \<lparr> fun_decl.name = ''count'',
      fun_decl.params = [aa, nn, xx],
      fun_decl.locals = [cc, ii],
      fun_decl.body = 
        cc ::= (Const ( 0));; (* Counter of occurences *)
        FOR ii FROM (Const ( 0)) TO (V nn) DO
          (IF (Eq (Index (V aa) (V ii)) (V xx))
            THEN cc ::= (Plus (V cc) (Const ( 1)))
          ELSE SKIP);;
        Return (V cc)
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
        (Indexl (V aa) (Const ( 2))) ::== (Const ( 44));;
        (Indexl (V aa) (Const ( 3))) ::== (Const ( 44));;
        (Indexl (V aa) (Const ( 4))) ::== (Const ( 54));;
        (Indexl (V aa) (Const ( 5))) ::== (Const ( 1));;
        (Indexl (V aa) (Const ( 6))) ::== (Const ( 92));;
        (Indexl (V aa) (Const ( 7))) ::== (Const ( 84));;
        (Indexl (V aa) (Const ( 8))) ::== (Const ( 44));;
        (Indexl (V aa) (Const ( 9))) ::== (Const ( 44));;
        nn ::= (Const ( 10));;
    
        Callfun foo ''count'' [(V aa), (V nn), Const 5];;
        Callfun bar ''count'' [(V aa), (V nn), Const 84];;
        Callfun baz ''count'' [(V aa), (V nn), Const 44]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''count'',
      program.globals = [aa, nn, foo, bar, baz],
      program.procs = [count_decl, main_decl]
    \<rparr>"

export_code p in SML

(* Check how many times 5, 84 and 44 occur in the array foo = 0, bar = 1, baz = 5 *)
value "execute_show [] p"

definition "count_exec \<equiv> execute_show [] p"

definition "count \<equiv> (
  shows_prog p ''''
)"

definition "count_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code count_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code count} @{code count_exec} "../TestC" "count"\<close>

end
