theory Fibonacci
imports Test_Setup
begin

(* Fibonacci: Takes a number and returns its fibonacci number *)
definition fib_decl :: fun_decl
  where "fib_decl \<equiv>
    \<lparr> fun_decl.name = ''fib'',
      fun_decl.rtype = Some ty.I,
      fun_decl.params = ints [nn],
      fun_decl.locals = ints [rr, xx, tt],
      fun_decl.body = 
        (IF (Eq (V nn) (Const 0)) THEN return (Const 0)
        ELSE (
          (IF (Eq (V nn) (Const 1)) THEN return (Const 1)
          ELSE (
            $xx := (Const 0);;
            $rr := (Const 1);;
            $nn := (Plus (V nn) (- Const (1)));;
            (WHILE (Less (Const 0) (V nn)) DO
              ($tt := (Plus (V xx) (V rr));;
              $xx := (V rr);;
              $rr := (V tt);;
              $nn := (Plus (V nn) (- Const (1))))
            );;
            return (V rr)))))
    \<rparr>"

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $nn := Const 14;;
        $rr := ''fib''!([V nn])
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''fib'',
      program.structs = [],
      program.globals = ints [nn, rr],
      program.functs = [fib_decl, main_decl n]
    \<rparr>"

definition "fib_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code fib_export}"../TestC" "fib"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "fib_test"\<close>

end
