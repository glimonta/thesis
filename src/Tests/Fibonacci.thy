theory Fibonacci
imports "../SmallStep" Test
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
        Callfun rr ''fib'' [Const 14]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.globals = [rr],
      program.procs = [main_decl, fib_decl]
    \<rparr>"

export_code p in SML

(* The factorial of the number is on the variable rr *)
value "case execute p of Some (_,\<gamma>,\<mu>) \<Rightarrow> (\<gamma> rr,\<mu>)"

end
