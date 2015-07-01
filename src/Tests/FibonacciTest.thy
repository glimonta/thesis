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

definition "fib_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code fib_test} "../TestC" "fib_test"\<close>

end
