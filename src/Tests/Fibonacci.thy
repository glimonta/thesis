theory Fibonacci
imports "../SmallStep" Test "../Test_Harness"
begin

(* Fibonacci: Takes a number and returns its fibonacci number *)
definition fib_decl :: fun_decl
  where "fib_decl \<equiv>
    \<lparr> fun_decl.name = ''fib'',
      fun_decl.params = [nn],
      fun_decl.locals = [rr, xx, tt],
      fun_decl.body = 
        (IF (Eq (V nn) (Const 0)) THEN Return (Const 0)
        ELSE (
          (IF (Eq (V nn) (Const 1)) THEN Return (Const 1)
          ELSE (
            xx ::= (Const 0);;
            rr ::= (Const 1);;
            nn ::= (Plus (V nn) (Const (- 1)));;
            (WHILE (Less (Const 0) (V nn)) DO
              (tt ::= (Plus (V xx) (V rr));;
              xx ::= (V rr);;
              rr ::= (V tt);;
              nn ::= (Plus (V nn) (Const (- 1))))
            );;
            Return (V rr)))))
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        nn ::= Const 14;;
        Callfun rr ''fib'' [V nn]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''fib'',
      program.globals = [nn, rr],
      program.procs = [fib_decl, main_decl]
    \<rparr>"

export_code p in SML

(* The factorial of the number is on the variable rr *)
value "execute_show [] p"

definition "fib_exec \<equiv> execute_show [] p"

definition "fib \<equiv> (
  shows_prog p ''''
)"

definition "fib_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code fib_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code fib} "../TestC" "fib"\<close>

end
