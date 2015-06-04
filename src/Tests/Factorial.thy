theory Factorial
imports "../SmallStep" Test "../Pretty"
begin


(* Factorial: Takes a number and returns the factorial *)
definition factorial_decl :: fun_decl
  where "factorial_decl \<equiv>
    \<lparr> fun_decl.name = ''fact'',
      fun_decl.params = [nn],
      fun_decl.locals = [rr, ii],
      fun_decl.body = 
        rr ::= (Const 1);;
        ii ::= (Const 1);;
        (WHILE (Less (V ii) (Plus (V nn) (Const 1))) DO
          (rr ::= (Mult (V rr) (V ii));;
          ii ::= (Plus (V ii) (Const 1)))
        );;
        Return (V rr)
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        nn ::= Const 5;;
        Callfun rr ''fact'' [Const 5]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.globals = [nn, rr],
      program.procs = [factorial_decl, main_decl]
    \<rparr>"

export_code p in SML

(* The factorial of the number is on the variable rr *)
value "execute_show [] p"

definition "fact \<equiv> (
  shows_prog p ''''
)"

ML_val {*
  @{code fact} |> String.implode |> writeln;
*}



end
