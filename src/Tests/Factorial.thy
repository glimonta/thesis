theory Factorial
imports Test_Setup
begin

(* Factorial: Takes a number and returns the factorial *)
definition factorial_decl :: fun_decl
  where "factorial_decl \<equiv>
    \<lparr> fun_decl.name = ''fact'',
      fun_decl.rtype = (Some ty.I),
      fun_decl.params = ints [nn],
      fun_decl.locals = ints [rr, ii],
      fun_decl.body = 
        $rr := (Const 1);;
        $ii := (Const 1);;
        (WHILE (Less (V ii) (Plus (V nn) (Const 1))) DO
          ($rr := (Mult (V rr) (V ii));;
          $ii := (Plus (V ii) (Const 1)))
        );;
        return (V rr)
    \<rparr>"

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $nn := Const 5;;
        $rr := ''fact''! ([V nn])
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''fact'',
      program.structs = [],
      program.globals = ints [nn, rr],
      program.functs = [factorial_decl, main_decl n]
    \<rparr>"

definition "fact_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code fact_export}"../TestC" "fact"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "fact_test"\<close>

end
