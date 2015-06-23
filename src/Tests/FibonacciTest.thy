theory FibonacciTest
imports "../SmallStep" "Fibonacci"
begin

definition fib_main_decl :: fun_decl
  where "fib_main_decl \<equiv>
    \<lparr> fun_decl.name = ''fib_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''fib_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''fib_test'',
      program.globals = (program.globals p),
      program.procs = [fib_decl, fib_main_decl, main_test_decl]
    \<rparr>"

export_code p' in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p'"

definition "fib_test_show \<equiv> (
  shows_prog p' ''''
)"

definition "fib_failed_check \<equiv> failed_check p'"

setup \<open>generate_c_test_code @{code fib_test_show} @{code fib_test}
  @{code init_disc} @{code fib_failed_check} "../TestC" "fib_test"\<close>

end